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
