// Copyright (C) 2026 The COLA Authors. GPL-3.0-or-later.
#include "late_monitor.hpp"
#include "cola.hpp"
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/twaalgos/isdet.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/postproc.hh>
#include <map>
#include <stdexcept>

namespace cola
{
  namespace
  {
    using mark = spot::acc_cond::mark_t;
    using code = spot::acc_cond::acc_code;
    struct limit { const char* reason; };

    bool positive_atoms(const code& f)
    {
      if(f.is_t()||f.is_f())return true;
      auto root=f.back().sub.op;
      if(root==spot::acc_cond::acc_op::Inf||root==spot::acc_cond::acc_op::Fin)return true;
      if(root==spot::acc_cond::acc_op::And)
        {for(const auto& c:f.top_conjuncts())if(!positive_atoms(c))return false;return true;}
      if(root==spot::acc_cond::acc_op::Or)
        {for(const auto& c:f.top_disjuncts())if(!positive_atoms(c))return false;return true;}
      return false;
    }

    spot::twa_graph_ptr synchronous(
      const std::vector<spot::const_twa_graph_ptr>& inputs, const code& acceptance,
      const late_monitor_options& options)
    {
      auto out = spot::make_twa_graph(inputs.front()->get_dict());
      std::vector<unsigned> offsets;
      unsigned colours = 0;
      for (const auto& a : inputs)
        {
          offsets.push_back(colours); colours += a->num_sets(); out->copy_ap_of(a);
          if (colours > mark::max_accsets()) throw limit{"acceptance-capacity"};
        }
      out->set_acceptance(colours,acceptance);
      using tuple = std::vector<unsigned>;
      std::map<tuple,unsigned> ids;std::vector<tuple> pending;
      auto state = [&](const tuple& t)
        {
          auto old=ids.find(t);if(old!=ids.end())return old->second;
          if(pending.size()>=options.max_states)throw limit{"state-budget"};
          unsigned q=out->new_state();ids.emplace(t,q);pending.push_back(t);return q;
        };
      tuple initial;for(const auto& a:inputs)initial.push_back(a->get_init_state_number());
      out->set_init_state(state(initial));
      struct choice { tuple target; bdd guard; mark colours{}; };
      unsigned work=0;
      for(unsigned src=0;src<pending.size();++src)
        {
          auto current=pending[src];std::vector<choice> choices{{{},bddtrue,{}}};
          for(unsigned i=0;i<inputs.size();++i)
            {
              std::vector<choice> next;
              for(const auto& c:choices)for(const auto& e:inputs[i]->out(current[i]))
                {
                  if(++work>options.max_edges)throw limit{"edge-work-budget"};
                  bdd guard=c.guard&e.cond;if(guard==bddfalse)continue;
                  auto target=c.target;target.push_back(e.dst);
                  auto colours=c.colours;if(e.acc)colours|=e.acc<<offsets[i];
                  next.push_back({std::move(target),guard,colours});
                }
              choices=std::move(next);
            }
          for(const auto& c:choices)
            {
              if(out->num_edges()>=options.max_edges)throw limit{"edge-budget"};
              out->new_edge(src,state(c.target),c.guard,c.colours);
            }
        }
      out->merge_edges();return out;
    }

    spot::twa_graph_ptr normalise(spot::twa_graph_ptr a)
    {
      spot::simplify_acceptance_here(a);spot::postprocessor p;
      p.set_type(spot::postprocessor::Generic);p.set_pref(spot::postprocessor::Deterministic);
      p.set_level(spot::postprocessor::Low);return spot::complete(p.run(a));
    }
  }

  late_monitor_result determinise_with_global_monitors(
    const spot::const_twa_graph_ptr& skeleton,
    const std::vector<spot::twa_graph_ptr>& monitors,
    const code& mixed_acceptance,const late_monitor_options& options)
  {
    late_monitor_result result;
    try
      {
        if(!skeleton->is_existential())throw limit{"alternating-skeleton"};
        if(!positive_atoms(mixed_acceptance))throw limit{"negative-mark-literal"};
        unsigned monitor_colours=0;
        for(const auto& d:monitors)
          {
            if(d->get_dict()!=skeleton->get_dict())throw limit{"different-dictionaries"};
            if(!spot::is_deterministic(d)||!spot::is_complete(d))throw limit{"monitor-not-global-deterministic"};
            monitor_colours+=d->num_sets();
          }
        unsigned k=skeleton->num_sets();
        if(k+monitor_colours>mark::max_accsets())throw limit{"acceptance-capacity"};
        mark declared{};
        for(unsigned c=0;c<k+monitor_colours;++c)declared.set(c);
        if(mixed_acceptance.used_sets()-declared)throw limit{"undeclared-acceptance-colour"};
        unsigned profiles=1;
        for(unsigned i=0;i<monitor_colours;++i)
          { if(profiles>options.max_profiles/2)throw limit{"profile-budget"};profiles*=2; }
        if(profiles>options.max_profiles)throw limit{"profile-budget"};
        result.profiles=profiles;
        std::vector<spot::const_twa_graph_ptr> components;
        std::vector<unsigned> offsets;
        unsigned allocated=0;
        for(unsigned valuation=0;valuation<profiles;++valuation)
          {
            mark present{},missing{};
            for(unsigned bit=0;bit<monitor_colours;++bit)
              ((valuation&(1U<<bit))?present:missing).set(k+bit);
            auto local=mixed_acceptance.remove(missing,true).remove(present,false);
            auto instance=spot::make_twa_graph(skeleton,spot::twa::prop_set{});
            instance->set_acceptance(k,local);
            instance->purge_unreachable_states();
            if(!is_elevator_automaton(instance))throw limit{"non-elevator-profile"};
            spot::option_map om;om.set(USE_SIMULATION,0);om.set(USE_DELAYED_SIMULATION,0);
            om.set(USE_STUTTER,0);om.set(USE_OBSERVED_RANKS,1);om.set(USE_SCC_INFO,1);
            om.set(USE_EXACT_STATE_LANGUAGES,1);
            auto det=spot::is_deterministic(instance)?instance:determinize_televator(instance,om);
            if(!spot::is_deterministic(det)||!spot::are_equivalent(instance,det))throw limit{"profile-verification-failed"};
            det=normalise(det);offsets.push_back(allocated);allocated+=det->num_sets();
            if(allocated+monitor_colours>mark::max_accsets())throw limit{"acceptance-capacity"};
            components.push_back(det);
          }
        unsigned global_base=allocated;
        code acceptance=code::f();
        for(unsigned v=0;v<profiles;++v)
          {
            code term=components[v]->acc().get_acceptance()<<offsets[v];
            for(unsigned bit=0;bit<monitor_colours;++bit)
              term&=(v&(1U<<bit))?code::inf({global_base+bit}):code::fin({global_base+bit});
            acceptance|=term;
          }
        for(const auto& d:monitors)components.push_back(d);
        auto out=synchronous(components,acceptance,options);
        // Independent early-product oracle, used only for this experimental
        // boundary's verification, never as the input to determinisation.
        std::vector<spot::const_twa_graph_ptr> early{skeleton};
        for(const auto& d:monitors)early.push_back(d);
        auto oracle=synchronous(early,mixed_acceptance,options);
        if(!spot::is_deterministic(out)||!spot::are_equivalent(oracle,out))throw limit{"global-verification-failed"};
        result.automaton=normalise(out);result.reason="verified";
      }
    catch(const limit& e){result.reason=e.reason;}
    catch(const std::runtime_error& e)
      {
        if(std::string(e.what()).find("Too many acceptance sets used.")!=0)throw;
        result.reason="acceptance-capacity";
      }
    return result;
  }
}
