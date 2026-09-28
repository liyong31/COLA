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
