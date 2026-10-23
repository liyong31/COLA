#include "late_monitor.hpp"
#include <spot/twaalgos/contains.hh>
#include <spot/tl/parse.hh>
#include <iostream>
#include <stdexcept>

using code=spot::acc_cond::acc_code;

static void require(bool b,const char* why){if(!b)throw std::runtime_error(why);}

static spot::twa_graph_ptr source(spot::bdd_dict_ptr dict)
{
  auto b=spot::make_twa_graph(dict);b->new_states(2);b->set_init_state(0);
  b->set_acceptance(1,code::inf({0}));auto p=bdd_ithvar(b->register_ap("p"));
  b->new_edge(0,0,bddtrue);b->new_edge(0,1,p,{0});b->new_edge(1,1,p,{0});return b;
}

static spot::twa_graph_ptr monitor(spot::bdd_dict_ptr dict,const char* name)
{
  auto d=spot::make_twa_graph(dict);d->new_state();d->set_init_state(0);
  d->set_acceptance(1,code::inf({0}));auto p=bdd_ithvar(d->register_ap(name));
  d->new_edge(0,0,p,{0});d->new_edge(0,0,!p);return d;
}

int main()
{
  unsigned checked=0;
  auto dict=spot::make_bdd_dict();auto b=source(dict),d=monitor(dict,"q");
  for(unsigned truth=0;truth<16;++truth)
    {
      code mixed=code::f();
      for(unsigned v=0;v<4;++v)
        if(truth&(1U<<v))mixed|=((v&1)?code::inf({0}):code::fin({0}))
                              &((v&2)?code::inf({1}):code::fin({1}));
      auto result=cola::determinise_with_global_monitors(b,{d},mixed);
      require(bool(result.automaton)&&result.profiles==2,"parametric construction failed");
      // The source has an always rejecting infinite run. An Inf(0) run
      // exists exactly for FG p; this distinguishes existential rejection
      // from complementing the language of the accepting source.
      auto branch=[&](unsigned monitor_value)
        {
          if(truth&(1U<<(2*monitor_value)))return std::string("1");
          return std::string((truth&(1U<<(2*monitor_value+1)))?"FG p":"0");
        };
      auto expected=spot::parse_infix_psl("(GF q & ("+branch(1)+")) | (FG!q & ("+branch(0)+"))");
      require(spot::are_equivalent(result.automaton,expected.f),"independent parametric oracle mismatch");
      ++checked;
    }
  auto r=monitor(dict,"r");
  auto multiple=cola::determinise_with_global_monitors(b,{d,r},code("(Inf(0)&Inf(1))|(Fin(0)&Inf(2))"));
  require(multiple.automaton&&multiple.profiles==4
          &&spot::are_equivalent(multiple.automaton,spot::parse_infix_psl("GF r | (FG p & GF q)").f),
          "multiple global monitors mismatch");++checked;
  for(unsigned kind=0;kind<3;++kind)
    {
      cola::late_monitor_options options;
      if(kind==0)options.max_profiles=1;
      if(kind==1)options.max_states=0;
      if(kind==2)options.max_edges=0;
      auto result=cola::determinise_with_global_monitors(b,{d},code("Inf(0)&Inf(1)"),options);
      require(!result.automaton,"parametric budget was ignored");++checked;
    }
  auto partial=spot::make_twa_graph(dict);partial->new_state();partial->set_init_state(0);
  partial->set_acceptance(1,code::inf({0}));auto q=bdd_ithvar(partial->register_ap("q"));partial->new_edge(0,0,q,{0});
  require(!cola::determinise_with_global_monitors(b,{partial},code("Inf(0)&Inf(1)")).automaton,
          "partial global monitor admitted");++checked;
  auto foreign=monitor(spot::make_bdd_dict(),"q");
  require(!cola::determinise_with_global_monitors(b,{foreign},code("Inf(0)&Inf(1)")).automaton,
          "foreign monitor dictionary admitted");++checked;
  require(!cola::determinise_with_global_monitors(b,{d},code("Inf(4)")).automaton,
          "undeclared acceptance colour admitted");++checked;
  auto hard=spot::make_twa_graph(dict);hard->new_states(2);hard->set_init_state(0);
  hard->set_acceptance(1,code::inf({0}));
  for(unsigned q=0;q<2;++q)
    {hard->new_edge(q,0,bddtrue);hard->new_edge(q,1,bddtrue,{0});}
  auto unsupported=cola::determinise_with_global_monitors(hard,{d},code("Inf(0)&Inf(1)"));
  require(!unsupported.automaton&&unsupported.reason=="non-elevator-profile",
          "unsupported acceptance profile was admitted");++checked;
  auto plain=cola::determinise_with_global_monitors(b,{},code::inf({0}));
  require(plain.automaton&&plain.profiles==1&&spot::are_equivalent(plain.automaton,spot::parse_infix_psl("FG p").f),
          "empty-monitor boundary mismatch");++checked;
  auto unused=spot::make_twa_graph(b,spot::twa::prop_set{});
  unsigned unreachable=unused->new_state();unused->new_edge(unreachable,unreachable,bddtrue,{0});
  auto clean=cola::determinise_with_global_monitors(unused,{d},code("Inf(0)&Inf(1)"));
  require(clean.automaton&&spot::are_equivalent(clean.automaton,spot::parse_infix_psl("FG p & GF q").f),
          "unreachable parametric skeleton mismatch");++checked;
  std::cout<<checked<<" acceptance-parametric global-monitor checks passed\n";
}
