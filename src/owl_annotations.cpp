// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#include "owl_annotations.hpp"
#include <spot/tl/parse.hh>
#include <spot/tl/relabel.hh>
#include <spot/twaalgos/contains.hh>
#include <cctype>
#include <functional>
#include <stdexcept>
#include <string>

namespace cola
{
  namespace
  {
    std::string trim(std::string s)
    {
      auto a = s.find_first_not_of(" \t\r\n");
      return a == std::string::npos ? "" : s.substr(a, s.find_last_not_of(" \t\r\n") - a + 1);
    }

    // Commas inside formulas, lists, records and quoted AP names are data.
    std::vector<std::string> split(const std::string& s)
    {
      std::vector<std::string> out;
      std::string stack;
      bool quoted = false, escape = false;
      unsigned begin = 0;
      for (unsigned i = 0; i < s.size(); ++i)
        {
          char c = s[i];
          if (quoted)
            {
              if (escape) escape = false;
              else if (c == '\\') escape = true;
              else if (c == '"') quoted = false;
              continue;
            }
          if (c == '"') { quoted = true; continue; }
          if (c == '(' || c == '[' || c == '{') stack += c;
          else if (c == ')' || c == ']' || c == '}')
            {
              char expected = c == ')' ? '(' : c == ']' ? '[' : '{';
              if (stack.empty() || stack.back() != expected) throw std::runtime_error("unbalanced OWL name");
              stack.pop_back();
            }
          else if (c == ',' && stack.empty())
            { out.push_back(trim(s.substr(begin, i - begin))); begin = i + 1; }
        }
      if (quoted || !stack.empty()) throw std::runtime_error("unterminated OWL name");
      if (begin < s.size()) out.push_back(trim(s.substr(begin)));
      return out;
    }

    unsigned end_group(const std::string& s, unsigned start)
    {
      char open = s.at(start), close = open == '(' ? ')' : open == '[' ? ']' : '}';
      unsigned depth = 0;
      bool quoted = false, escape = false;
      for (unsigned i = start; i < s.size(); ++i)
        {
          char c = s[i];
          if (quoted)
            { if (escape) escape = false; else if (c == '\\') escape = true; else if (c == '"') quoted = false; continue; }
          if (c == '"') { quoted = true; continue; }
          if (c == open) ++depth;
          if (c == close && --depth == 0) return i;
        }
      throw std::runtime_error("unterminated OWL group");
    }

    spot::formula parse(const std::string& text, const spot::const_twa_graph_ptr& aut, bool indexed)
    {
      std::string formula_text = text;
      if (indexed)
        {
          // OWL Formula.toString() omits token separators: p0Up1 and
          // !p2R(p3|p4). Spot otherwise reads p0Up1 as one AP name.
          formula_text.clear();
          for (unsigned i = 0; i < text.size();)
            {
              if (text[i] == 'p')
                {
                  unsigned start = i++;
                  while (i < text.size() && std::isdigit(static_cast<unsigned char>(text[i]))) ++i;
                  if (i == start + 1) throw std::runtime_error("invalid OWL indexed token");
                  formula_text += " " + text.substr(start, i - start) + " ";
                }
              else if (std::string("XFGURWM").find(text[i]) != std::string::npos)
                { formula_text += ' '; formula_text += text[i++]; formula_text += ' '; }
              else formula_text += text[i++];
            }
        }
      auto p = spot::parse_infix_psl(formula_text);
      if (!p.errors.empty() || !p.f || !p.f.is_ltl_formula()) throw std::runtime_error("invalid OWL formula");
      if (!indexed) return p.f;
      // Fixed-point Formula.toString() uses p0,p1,...; EquivalenceClass
      // descriptions instead use the original HOA atomic proposition names.
      std::function<spot::formula(spot::formula)> rename = [&](spot::formula f)
        {
          if (f.is(spot::op::ap))
            {
              auto name = f.ap_name();
              if (name.size() < 2 || name[0] != 'p') throw std::runtime_error("invalid indexed AP");
              for (unsigned j = 1; j < name.size(); ++j)
                if (!std::isdigit(static_cast<unsigned char>(name[j]))) throw std::runtime_error("invalid indexed AP");
              auto i = std::stoul(name.substr(1));
              if (i >= aut->ap().size()) throw std::runtime_error("indexed AP out of range");
              return aut->ap()[i];
            }
          return f.map(rename);
        };
      return rename(p.f);
    }

    std::vector<spot::formula> list(const std::string& text, const spot::const_twa_graph_ptr& aut, bool indexed)
    {
      if (text.size() < 2 || text.front() != '[' || end_group(text, 0) != text.size() - 1)
        throw std::runtime_error("invalid OWL list");
      std::vector<spot::formula> result;
      for (const auto& s : split(text.substr(1, text.size() - 2))) result.push_back(parse(s, aut, indexed));
      return result;
    }

    std::vector<spot::formula> decode(std::string name, const spot::const_twa_graph_ptr& aut,
                                      bool include_prefix)
    {
      if (name.size() < 4 || name.size() > 65536 || name.back() != ']') return {};
      if (include_prefix && name.substr(0, 2) == "A[")
        {
          auto body = trim(name.substr(2, name.size() - 3));
          if (body.empty()) return {};
          if (body.front() != '{') return {parse(body, aut, false)};
          if (end_group(body, 0) != body.size() - 1) return {};
          std::vector<spot::formula> terms;
          for (const auto& entry : split(body.substr(1, body.size() - 2)))
            {
              auto eq = entry.find('=');
              if (eq == std::string::npos) return {};
              terms.push_back(parse(entry.substr(eq + 1), aut, false));
            }
          return {spot::formula::Or(terms)};
        }
      if (name.substr(0, 2) != "B[") return {};
      name = trim(name.substr(2, name.size() - 3));
      if (name.empty()) return {};
      std::vector<spot::formula> terms;
      std::string::size_type end;
      bool symmetric = name.front() == '<';
      if (!symmetric)
        {
          if (name.front() != '(') return {};
          end = end_group(name, 0);
          auto tuple = split(name.substr(1, end - 1));
          if (tuple.size() != 4 || tuple[3].rfind("Fixpoints{", 0) != 0) return {};
          for (unsigned j = 0; j < 3; ++j)
            { auto fs = list(tuple[j], aut, true); terms.insert(terms.end(), fs.begin(), fs.end()); }
        }
      else
        {
          // SymmetricProductState.language() = safety & infinitelyOften.
          // Its almostAlways obligations are already represented by safety.
          if (name.size() < 3 || name[1] != '[') return {};
          auto first = end_group(name, 1);
          auto next = name.find_first_not_of(" ,\t", first + 1);
          if (next == std::string::npos || name[next] != '[') return {};
          auto last = end_group(name, next);
          end = name.find_first_not_of(" \t", last + 1);
          if (end == std::string::npos || name[end] != '>') return {};
          terms = list(name.substr(next, last - next + 1), aut, true);
        }
      auto fields = trim(name.substr(end + 1));
      if (fields.size() < 2 || fields.front() != '[' || end_group(fields, 0) != fields.size() - 1) return {};
      spot::formula liveness;
      for (const auto& field : split(fields.substr(1, fields.size() - 2)))
        {
          auto eq = field.find('=');
          if (eq == std::string::npos) return {};
          auto key = trim(field.substr(0, eq)), value = trim(field.substr(eq + 1));
          if (key == "GWR" || (!symmetric && key == "C")) terms.push_back(parse(value, aut, false));
          else if (!symmetric && key == "N")
            { auto fs = list(value, aut, false); terms.insert(terms.end(), fs.begin(), fs.end()); }
          else if (!symmetric && key == "i") { /* round-robin index is not a formula */ }
          else if (symmetric && key == "FUM")
            {
              if (value.rfind("RoundRobinState{", 0) != 0 || value.back() != '}') return {};
              auto record = split(value.substr(16, value.size() - 17));
              for (const auto& entry : record)
                if (entry.rfind("state=", 0) == 0) liveness = parse(entry.substr(6), aut, false);
            }
          else return {};
        }
      auto base = spot::formula::And(terms);
      // Some releases expose a weaker language() description for symmetric
      // states. Try the explicit pending monitor too; every candidate is checked.
      if (liveness) return {base, spot::formula::And({base, liveness})};
      return {base};
    }
  }

  owl_language_oracle::owl_language_oracle(const spot::const_twa_graph_ptr& aut, bool include_prefix)
    : formulas_(aut->num_states()), languages_(aut->num_states(), bddfalse),
      regions_(aut->num_states(), 0)
  {
    auto names = aut->get_named_prop<std::vector<std::string>>("state-names");
    if (!names) return;
    if (include_prefix && aut->is_existential() && aut->num_sets()
        && aut->acc().is_generalized_buchi() && names->size() == aut->num_states())
      {
        bool valid = true;
        for (unsigned q = 0; q < aut->num_states(); ++q)
          {
            const auto& s = (*names)[q];
            if (s.rfind("A[", 0) == 0) regions_[q] = 'A';
            else if (s.rfind("B[", 0) == 0) regions_[q] = 'B';
            else valid = false;
          }
        if (!is_prefix(aut->get_init_state_number())) valid = false;
        for (unsigned q = 0; q < aut->num_states() && valid; ++q)
          {
            bdd internal_guards = bddfalse;
            for (const auto& t : aut->out(q))
              {
                if (t.cond == bddfalse) continue;
                if (regions_[q] == 'B' && regions_[t.dst] != 'B') { valid = false; break; }
                if (regions_[q] == 'A' && regions_[t.dst] != 'A') continue;
                // Rejecting internally deterministic prefix, closed fully
                // deterministic accepting region. Duplicate edges are rejected
                // conservatively rather than trusting the state-name tags.
                if ((regions_[q] == 'A' && t.acc)
                    || (internal_guards & t.cond) != bddfalse) { valid = false; break; }
                internal_guards |= t.cond;
              }
          }
        stats.prefix_admitted = valid;
      }
    for (unsigned q = 0; q < aut->num_states() && q < names->size() && q < 256; ++q)
      {
      bool decoded = false;
      try
        {
          auto candidates = decode((*names)[q], aut, stats.prefix_admitted);
          if (candidates.empty()) continue;
          ++stats.decoded;
          decoded = true;
          auto rooted = spot::make_twa_graph(aut, spot::twa::prop_set::all());
          rooted->set_init_state(q);
          for (auto f : candidates)
            if (spot::are_equivalent(rooted, f))
              {
                auto language = boolean_abstraction(f);
                languages_[q] = language;
                formulas_[q] = f;
                ++stats.certified;
                if (is_prefix(q)) ++stats.prefix_certified;
                break;
              }
          if (!formulas_[q]) ++stats.rejected;
        }
      catch (const std::exception&)
        { if (decoded) ++stats.rejected; /* checker capacity: keep the run */ }
      }
  }

  owl_language_oracle::~owl_language_oracle() { dict_->unregister_all_my_variables(this); }

  bdd owl_language_oracle::boolean_abstraction(spot::formula f)
  {
    using spot::op;
    switch (f.kind())
      {
      case op::tt: return bddtrue;
      case op::ff: return bddfalse;
      case op::Not: return !boolean_abstraction(f[0]);
      case op::And: case op::Or:
        {
          bdd result = f.is(op::And) ? bdd(bddtrue) : bdd(bddfalse);
          for (auto c : f) result = f.is(op::And) ? result & boolean_abstraction(c) : result | boolean_abstraction(c);
          return result;
        }
      case op::Implies: return !boolean_abstraction(f[0]) | boolean_abstraction(f[1]);
      case op::Equiv: return !(boolean_abstraction(f[0]) ^ boolean_abstraction(f[1]));
      case op::Xor: return boolean_abstraction(f[0]) ^ boolean_abstraction(f[1]);
      default:
        auto found = atoms_.find(f);
        if (found != atoms_.end()) return found->second;
        auto variable = bdd_ithvar(dict_->register_anonymous_variables(1, this));
        atoms_.emplace(f, variable);
        return variable;
      }
  }

  bool owl_language_oracle::known(unsigned q) const { return q < formulas_.size() && bool(formulas_[q]); }
  bool owl_language_oracle::is_prefix(unsigned q) const { return q < regions_.size() && regions_[q] == 'A'; }

  bool owl_language_oracle::covers(unsigned target, const std::vector<unsigned>& older) const
  {
    if (!known(target)) return false;
    bdd cover = bddfalse;
    for (unsigned q : older) if (known(q)) cover |= languages_[q];
    return bdd_implies(languages_[target], cover);
  }
}
