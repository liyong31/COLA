#!/bin/sh
set -eu

LTLD=${LTLD:-./ltl2dela}
TMP=${TMPDIR:-/tmp}/ltl2dela-smoke-$$
mkdir -p "$TMP"
trap 'rm -rf "$TMP"' EXIT HUP INT TERM

run()
{
  name=$1
  formula=$2
  shift 2
  "$LTLD" --stats "$@" -f "$formula" -o "$TMP/$name.hoa"
  autfilt --is-deterministic "$TMP/$name.hoa" >/dev/null
}

# Direct deterministic fragments.
run safety 'G(a -> X b)'
run recurrence 'GF a'
run persistence 'FG a'

# Master-Theorem-style G-profile examples.
run gprofile 'GF(a | G b)' --profile-depth=4 --profile-budget=16
run response '(G(a -> F b)) & (FG c)' --profile-depth=4 --profile-budget=16

# Recurrent U/M/R/W guards are candidate profile separators.
run until_profile 'GF(c & (a U b))' --profile-depth=4 --profile-budget=16
run mixed '(GF(a | G b)) & G(c -> F d)' --profile-depth=5 --profile-budget=24

echo "ltl2dela smoke tests passed"


compare_exact()
{
  name=$1
  formula=$2
  "$LTLD" -f "$formula" -o "$TMP/$name-exact.hoa"
  "$LTLD" --no-exact-languages -f "$formula" -o "$TMP/$name-approx.hoa"
  autfilt -q "$TMP/$name-exact.hoa"     --equivalent-to="$TMP/$name-approx.hoa" >/dev/null
}

# Exact/approximate ordering and pruning must preserve the language.
compare_exact exact_gprofile 'GF(a | G b)'
compare_exact exact_until 'GF(c & (a U b))'
compare_exact exact_mixed '(GF(a | G b)) & G(c -> F d)'


# Stress formulas intended to create several recurrent obligations and expose
# differences between cold/narrow and hot/wide deterministic accepting SCCs.
compare_exact adaptive_conj   '(GF(a | G b)) & (GF(c | G d)) & G(e -> F f)'
compare_exact adaptive_until   'GF((a U b) & (c U d)) & G(e -> F g)'


compare_recurrence()
{
  name=$1
  formula=$2
  "$LTLD" -f "$formula" -o "$TMP/$name-special.hoa"
  "$LTLD" --no-recurrence -f "$formula" -o "$TMP/$name-generic.hoa"
  autfilt -q "$TMP/$name-special.hoa"     --equivalent-to="$TMP/$name-generic.hoa" >/dev/null
  autfilt --is-deterministic "$TMP/$name-special.hoa" >/dev/null
}

# Exact GF identities handled structurally before Delta2/Buchi.
compare_recurrence gf_x        'GF X a'
compare_recurrence gf_f        'GF F a'
compare_recurrence gf_until    'GF(a U b)'
compare_recurrence gf_mrelease 'GF(a M b)'
compare_recurrence gf_or       'GF((a U b) | (c U d))'
compare_recurrence gf_future   'GF(a & F b)'
compare_recurrence gf_futures  'GF(a & F b & F c)'

# Dedicated two-state flat-Until monitor.
compare_recurrence flat_until1 'GF(c & (a U b))'
compare_recurrence flat_until2 'GF((c | d) & ((a & e) U (b | f)))'
compare_recurrence flat_mrelease 'GF(c & (a M b))'


compare_master()
{
  name=$1
  formula=$2
  "$LTLD" -f "$formula" -o "$TMP/$name-master.hoa"
  "$LTLD" --no-master-profiles -f "$formula" -o "$TMP/$name-nomaster.hoa"
  autfilt -q "$TMP/$name-master.hoa"     --equivalent-to="$TMP/$name-nomaster.hoa" >/dev/null
  autfilt --is-deterministic "$TMP/$name-master.hoa" >/dev/null
}

# Explicit post-commitment profile facts must preserve the language while
# simplifying recurrent obligations under a shared asymptotic context.
compare_master master_fg1  '(FG b) & GF(a | G b)'
compare_master master_fg2  '(FG (b | c)) & GF(a & F(b | c))'
compare_master master_gfn1 '(GF !b) & GF(a | G b)'
compare_master master_gfn2 '(GF !b) & GF(F !b & (a U c))'
compare_master master_multi '(FG b) & (GF !c) & GF((a | G b) & F !c)'


compare_master()
{
  name=$1
  formula=$2
  "$LTLD" -f "$formula" -o "$TMP/$name-master.hoa"
  "$LTLD" --no-master-profiles -f "$formula" -o "$TMP/$name-nomaster.hoa"
  autfilt -q "$TMP/$name-master.hoa"     --equivalent-to="$TMP/$name-nomaster.hoa" >/dev/null
  autfilt --is-deterministic "$TMP/$name-master.hoa" >/dev/null
}

# Pre-Buchi Master-profile splitting should preserve language while exposing
# asymptotic modes before any hard Buchi SCC is constructed.
compare_master master_g1 'GF(a | G b)'
compare_master master_g2 'GF((a U c) | G b)'
compare_master master_g3 'GF((a & G b) | (c & G d))'
compare_master master_bundle 'FG b & GF(a | G b)'
compare_master master_nested '(GF(a | G b)) & (GF(c | G d))'


# Exact extraction of stable G-obligations from recurrence.
compare_recurrence gf_g          'GF G a'
compare_recurrence gf_and_g      'GF(a & G b)'
compare_recurrence gf_many_g     'GF(a & G b & G c)'
compare_recurrence gf_or_g       'GF(a | G b)'

compare_master master_nested_x 'X GF(a | G b)'
compare_master master_nested_bool '(c | X GF(a | G b)) & GF d'
compare_master master_nested_f 'F(c & GF(a | G b))'


compare_profile()
{
  name=$1
  formula=$2
  "$LTLD" -f "$formula" -o "$TMP/$name-profile.hoa"
  "$LTLD" --no-profiles -f "$formula" -o "$TMP/$name-noprofile.hoa"
  autfilt -q "$TMP/$name-profile.hoa"     --equivalent-to="$TMP/$name-noprofile.hoa" >/dev/null
  autfilt --is-deterministic "$TMP/$name-profile.hoa" >/dev/null
}

# Pre-Buchi syntactic Y-profile commitments.  These examples deliberately
# leave a nested G below a recurrent context that the exact top-level GF
# rewrites do not already eliminate.
compare_profile y_nested1 'GF((a U b) & (c | G d))'
compare_profile y_nested2 'GF((a U b) & (c | G(d | e)))'
compare_profile y_nested3 'GF((a M b) & (c | G d))'


# Profile-context reductions of guarded temporal operators.
compare_master master_u_fg  '(FG a) & GF(c & (a U b))'
compare_master master_m_fg  '(FG b) & GF(c & (a M b))'
compare_master master_w_gfn '(GF !a) & GF(c & (a W b))'
compare_master master_r_gfn '(GF !b) & GF(c & (a R b))'
