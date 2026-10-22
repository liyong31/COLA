// Compare existing late Boolean composition with early TELA product.
#include "cola.hpp"
#include <spot/twaalgos/product.hh>
#include <spot/twaalgos/postproc.hh>
#include <spot/twaalgos/cleanacc.hh>
#include <spot/twaalgos/complete.hh>
#include <spot/twaalgos/contains.hh>
#include <spot/tl/parse.hh>
#include <chrono>
#include <iostream>
#include <stdexcept>

static spot::twa_graph_ptr skeleton(spot::bdd_dict_ptr dict)
{
  auto a=spot::make_twa_graph(dict);a->new_states(3);a->set_init_state(0);
  a->set_acceptance(1,spot::acc_cond::acc_code::fin({0}));
  auto p=bdd_ithvar(a->register_ap("a")),q=bdd_ithvar(a->register_ap("b"));
  a->new_edge(0,0,bddtrue,{0});a->new_edge(0,1,p,{0});
  a->new_edge(1,2,q);a->new_edge(2,2,q);return a;
}

static spot::twa_graph_ptr monitor(spot::bdd_dict_ptr dict,unsigned depth)
{
  auto a=spot::make_twa_graph(dict);unsigned size=1U<<depth;
  a->new_states(size);a->set_init_state(0);
  a->set_acceptance(1,spot::acc_cond::acc_code::inf({0}));
  auto x=bdd_ithvar(a->register_ap("x")),y=bdd_ithvar(a->register_ap("y"));
  for(unsigned q=0;q<size;++q)
    for(unsigned letter=0;letter<4;++letter)
      {
        auto guard=((letter&1)?x:!x)&((letter&2)?y:!y);
        spot::acc_cond::mark_t marks{};
        if(q==size-1&&(letter&2))marks.set(0);
        a->new_edge(q,((q<<1)|(letter&1))&(size-1),guard,marks);
      }
  a->merge_edges();return a;
}

static spot::twa_graph_ptr normalise(spot::twa_graph_ptr a)
{
  spot::simplify_acceptance_here(a);spot::postprocessor p;
  p.set_type(spot::postprocessor::Generic);p.set_pref(spot::postprocessor::Deterministic);
  p.set_level(spot::postprocessor::Low);return spot::complete(p.run(a));
}

static spot::twa_graph_ptr translate(bool early,unsigned depth,bool diagnostics,
                                     spot::bdd_dict_ptr dict=spot::make_bdd_dict(),bool minimise=false)
{
  auto b=skeleton(dict),d=monitor(dict,depth);
  spot::option_map options;options.set(USE_SIMULATION,0);options.set(USE_DELAYED_SIMULATION,0);
  options.set(USE_STUTTER,0);options.set(USE_OBSERVED_RANKS,1);options.set(USE_SCC_INFO,1);
  auto start=std::chrono::steady_clock::now();
  if(minimise)d=normalise(d);
  spot::twa_graph_ptr result;unsigned intermediate=0,raw_states=0,raw_colours=0,b_states=0;
  if(early)
    {
      auto product=spot::product(b,d);intermediate=product->num_states();
      if(!cola::is_elevator_automaton(product))throw std::runtime_error("early product is not elevator");
      result=cola::determinize_televator(product,options);
    }
  else
    {
      intermediate=b->num_states();auto deterministic=cola::determinize_televator(b,options);
      b_states=deterministic->num_states();result=spot::product(deterministic,d);
      if(result->num_states()>b_states*d->num_states())throw std::runtime_error("late product bound violated");
    }
  raw_states=result->num_states();raw_colours=result->num_sets();result=normalise(result);
  auto elapsed=std::chrono::duration<double,std::milli>(std::chrono::steady_clock::now()-start).count();
  if(diagnostics)
    std::cerr<<"construction-ms: "<<elapsed<<"\ninput-states: "<<intermediate
             <<"\nmonitor-states: "<<d->num_states()<<"\nskeleton-deterministic-states: "<<b_states
             <<"\nraw-states: "<<raw_states<<"\nraw-colours: "<<raw_colours<<'\n';
  return result;
}

int main(int argc,char** argv)
{
  if(argc==1)
    {
      for(unsigned depth=0;depth<3;++depth)
        {
          auto dict=spot::make_bdd_dict();
          auto early=translate(true,depth,false,dict),late=translate(false,depth,false,dict);
          std::string kernel="y";
          for(unsigned i=0;i<depth;++i)kernel="x & X("+kernel+")";
          auto formula=spot::parse_infix_psl("F(a & XG b) & GF("+kernel+")");
          if(!spot::are_equivalent(early,late)||!spot::are_equivalent(late,formula.f))
            throw std::runtime_error("late monitor oracle mismatch");
        }
      std::cout<<"3 late-monitor oracle and product-bound checks passed\n";return 0;
    }
  if(argc!=3&&argc!=4)return 2;
  unsigned depth=std::stoul(argv[2]);if(depth>6)return 2;
  std::string mode=argv[1];if(mode!="early"&&mode!="late")return 2;
  bool minimise=argc==4&&std::string(argv[3])=="minimised";
  if(argc==4&&!minimise)return 2;
  auto result=translate(mode=="early",depth,true,spot::make_bdd_dict(),minimise);
  spot::print_hoa(std::cout,result);return 0;
}
