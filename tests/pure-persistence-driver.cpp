// Graph certificate only: this does not lift alternating acceptance.
#include <spot/parseaut/public.hh>
#include <spot/twaalgos/sccinfo.hh>
#include <spot/tl/parse.hh>
#include <spot/tl/nenoform.hh>
#include <algorithm>
#include <functional>
#include <iostream>
#include <map>
#include <set>
#include <stdexcept>

struct certificate
{
  bool pure = true;
  const char* reason = "certified";
  unsigned state = 0;
  std::vector<unsigned> order;
};

static bool syntax(spot::formula f)
{
  using op = spot::op;
  if (f.is_boolean()) return true;
  if (f.is(op::And) || f.is(op::Or))
    { for (auto child : f) if (!syntax(child)) return false; return true; }
  if (f.is(op::X) || f.is(op::F)) return syntax(f[0]);
  if (f.is(op::G)) return f[0].is_boolean();
  if (f.is(op::U) || f.is(op::W)) return f[0].is_boolean() && syntax(f[1]);
  if (f.is(op::R) || f.is(op::M)) return syntax(f[0]) && f[1].is_boolean();
  return false;
}

static certificate certify(const spot::twa_graph_ptr& a)
{
  certificate out;
  std::vector<std::set<unsigned>> dependencies(a->num_states());
  for (unsigned q = 0; q < a->num_states(); ++q)
    for (const auto& e : a->out(q))
      if (e.cond != bddfalse)
        {
          std::set<unsigned> targets;
          for (unsigned d : a->univ_dests(e)) targets.insert(d);
          if (targets.count(q))
            {
              if (targets.size() != 1) return {false,"recurrent-spawn",q,{}};
            }
          else dependencies[q].insert(targets.begin(),targets.end());
        }
  std::vector<unsigned> seen(a->num_states(),0);
  std::function<bool(unsigned)> visit = [&](unsigned q)
    {
      if (seen[q] == 1) { out.state = q; return false; }
      if (seen[q] == 2) return true;
      seen[q] = 1;
      for (unsigned d : dependencies[q]) if (!visit(d)) return false;
      seen[q] = 2; out.order.push_back(q); return true;
    };
  for (unsigned q = 0; q < a->num_states(); ++q)
    if (!visit(q)) { out.pure = false; out.reason = "strict-dependency-cycle"; break; }
  return out;
}

static std::pair<unsigned,unsigned> configurations(const spot::twa_graph_ptr& a)
{
  using config = std::set<unsigned>;
  auto graph = spot::make_twa_graph(a->get_dict());
  graph->set_acceptance(0,spot::acc_cond::acc_code::t());
  std::vector<config> todo;
  std::map<config,unsigned> ids;
  auto state = [&](const config& c)
    {
      auto old = ids.find(c); if (old != ids.end()) return old->second;
      if (todo.size() >= 4096) throw std::runtime_error("configuration-budget");
      unsigned id = graph->new_state();todo.push_back(c);ids.emplace(c,id);return id;
    };
  config initial;
  for (unsigned q : a->univ_dests(a->get_init_state_number())) initial.insert(q);
  graph->set_init_state(state(initial));
  unsigned work = 0;
  for (unsigned src = 0; src < todo.size(); ++src)
    {
      std::map<config,bdd> choices{{config{},bddtrue}};
      auto current = todo[src];
      for (unsigned q : current)
        {
          std::map<config,bdd> next;
          for (const auto& c : choices)
            for (const auto& e : a->out(q))
              {
                if (++work > 65536) throw std::runtime_error("configuration-work-budget");
                bdd label = c.second & e.cond;
                if (label == bddfalse) continue;
                config target = c.first;
                for (unsigned d : a->univ_dests(e)) target.insert(d);
                auto old = next.find(target);
                if (old == next.end()) next.emplace(target,label); else old->second |= label;
              }
          choices = std::move(next);
        }
      for (const auto& c : choices) graph->new_edge(src,state(c.first),c.second);
    }
  spot::scc_info si(graph);
  unsigned nonsingleton = 0;
  for (unsigned sc = 0; sc < si.scc_count(); ++sc) nonsingleton += si.states_of(sc).size() > 1;
  return {graph->num_states(),nonsingleton};
}

static void self_test()
{
  auto a = spot::make_twa_graph(spot::make_bdd_dict());
  a->new_states(3);a->set_init_state(0);a->set_acceptance(0,spot::acc_cond::acc_code::t());
  a->new_edge(0,0,bddtrue);a->new_univ_edge(0,{1,2},bddtrue);
  a->new_edge(1,1,bddtrue);a->new_edge(2,2,bddtrue);
  if (!certify(a).pure || configurations(a).second) throw std::runtime_error("pure fixture failed");
  a->new_univ_edge(0,{0,1},bddtrue);
  if (certify(a).pure) throw std::runtime_error("spawn was admitted");
  auto b = spot::make_twa_graph(spot::make_bdd_dict());
  b->new_states(2);b->set_init_state(0);b->set_acceptance(0,spot::acc_cond::acc_code::t());
  b->new_edge(0,1,bddtrue);b->new_edge(1,0,bddtrue);
  if (certify(b).pure || !configurations(b).second) throw std::runtime_error("cycle was admitted");
  if (!syntax(spot::parse_infix_psl("F(Ga & X(Fb))").f)
      || !syntax(spot::parse_infix_psl("(a U Xb) & FG c").f)
      || syntax(spot::parse_infix_psl("GF a").f)
      || syntax(spot::parse_infix_psl("G(a -> F b)").f))
    throw std::runtime_error("pure-persistence syntax certificate failed");
  std::cout << "7 pure-persistence graph/syntax checks passed\n";
}

int main(int argc,char** argv)
{
  if (argc == 1) { self_test(); return 0; }
  auto a = spot::parse_aut(argv[1],spot::make_bdd_dict());
  if (!a || a->format_errors(std::cerr) || !a->aut) return 2;
  auto c = certify(a->aut);
  std::cout << "{\"pure\":" << c.pure << ",\"reason\":\"" << c.reason
            << "\",\"state\":" << c.state << ",\"states\":" << a->aut->num_states();
  if (argc > 2)
    {
      auto formula = spot::parse_infix_psl(argv[2]);
      if (formula.format_errors(std::cerr)) return 2;
      std::cout << ",\"syntactic\":" << syntax(spot::negative_normal_form(formula.f));
    }
  std::cout << ",\"order\":[";
  for (unsigned i = 0; i < c.order.size(); ++i) std::cout << (i ? "," : "") << c.order[i];
  std::cout << ']';
  try
    {
      auto g = configurations(a->aut);
      if (c.pure && g.second) throw std::logic_error("certified non-singleton SCC");
      std::cout << ",\"configurations\":" << g.first << ",\"nonsingleton_sccs\":" << g.second;
    }
  catch (const std::runtime_error& e) { std::cout << ",\"enumeration_limit\":\"" << e.what() << '"'; }
  std::cout << "}\n";
}
