# Certified OWL annotations in native determinisation

OWL is invoked with --state-labels. The decoder supports the measured OWL 21
SEJK16 and EKS20 accepting-state descriptions. Indexed fixed-point APs are
mapped through the HOA AP order; monitor formulas use original names.
An indexed-token lexer handles OWL strings such as p0Up1. Quoted AP names
and nested lists/records are preserved.

Every reconstructed state-language formula is checked against the input
automaton rooted at that state before it can justify deletion. Unsupported,
malformed or unverified names remain unknown. Certification examines at
most the first 256 state indices, matching the default frontend admission cap.

Certified formulas prove pair dominance and full older-prefix union coverage
through propositional BDDs over maximal temporal subformulas. A Boolean
implication is sufficient for the corresponding language inclusion. These
proofs precede the bounded exact-query policy and do not consume its budget.
Only younger runs are deleted; the oldest is retained. Original Emerson–Lei
colours and rank-discontinuation acceptance remain unchanged.

## Identical-input ablations

Both modes use the same labelled HOA input and the existing wider exact
policy/colour packing. Only --owl-annotations differs. Each process has a
10-second deadline, with two workers per raw campaign. Campaigns may overlap;
elapsed times are diagnostic, not runtime rankings.

| Polarity | Algorithm | Paired successes | Smaller / tied / larger | Off / on states |
| --- | --- | ---: | ---: | ---: |
| positive | SEJK16 | 225 | 0 / 225 / 0 | 1753 / 1753 |
| positive | EKS20 | 224 | 2 / 222 / 0 | 1998 / 1932 |
| negative | SEJK16 | 222 | 1 / 221 / 0 | 1898 / 1872 |
| negative | EKS20 | 222 | 1 / 221 / 0 | 1493 / 1460 |

Non-tied paired results:

- positive Parametrised.ltl:42 EKS20: 66 → 42 states.
- positive Liberouter04.ltl:43 EKS20: 76 → 34 states.
- negative Parametrised.ltl:45 SEJK16: 88 → 62 states.
- negative Parametrised.ltl:45 EKS20: 47 → 14 states.
- negative Parametrised-Hardness.ltl:5 SEJK16: backend-timeout → ok (1158 states).

| Polarity | Mode | Status | Count |
| --- | --- | --- | ---: |
| positive | off | acceptance-capacity | 4 |
| positive | off | frontend-timeout | 1 |
| positive | off | ok | 449 |
| positive | on | acceptance-capacity | 4 |
| positive | on | frontend-timeout | 1 |
| positive | on | ok | 449 |
| negative | off | acceptance-capacity | 3 |
| negative | off | backend-timeout | 1 |
| negative | off | frontend-timeout | 4 |
| negative | off | input-budget | 2 |
| negative | off | ok | 444 |
| negative | on | acceptance-capacity | 3 |
| negative | on | frontend-timeout | 4 |
| negative | on | input-budget | 2 |
| negative | on | ok | 445 |

Across raw on-mode outputs: 3329 certified state annotations, 0 rejected decoded annotations, 7406 successful pair proofs and 10182 union pruning events.
Counts include repeated proof uses across macrostates; they are not unique-language counts.

## Integrated portfolio

| Mode | Smaller / tied / larger | Previous / annotated total |
| --- | ---: | ---: |
| cola_ldgba | 0 / 227 / 0 | 1337 / 1337 |
| cola_combined | 0 / 227 / 0 | 1336 / 1336 |

All integrated outputs pass deterministic/completeness and independent language checks,
and no LDGBA candidate fails language validation. The annotated mode is default
when an OWL LDGBA tool is supplied; --no-ldgba-annotations supplies the ablation.

## Proof scope and regression evidence

The independent per-state equivalence check supplies the exactness certificate;
OWL toString() output is not trusted solely because it resembles a formula.
Unknown older formulas can be omitted from a proposed cover safely. The BDD
check is complete for the Boolean abstraction, not for arbitrary LTL implication.

This now supplies checked formula pruning. The remaining TACAS complexity
obligations are a certified deterministic prefix and a singly exponential bound
on the total basis/rank width and weak bookkeeping across SCCs. Formula names
alone do not prove those hypotheses; the conditional counting contract remains
in research/colour-elevator.tex.

The 26 C++ regressions include a genuinely joint union cover, actual union
pruning with all automaton-inclusion query budgets disabled, forged/malformed
names, indexed AP collisions, punctuation in AP names, symmetric monitor
fields and unspaced U/W/R/M tokens. The existing construction tests remain.

## Reproduction

```sh
make -C build-local -j4 check
python3 tests/benchmark-owl-annotations.py
python3 tests/benchmark-owl-annotations.py --negative \
  --artifacts build-local/owl-annotations-negative \
  --csv tests/owl-annotations-negative-results.csv
python3 tests/benchmark-slaa.py --tool PATH_TO_LTL3TELA \
  --ldgba-pruning --ldgba-portfolio --modes cola_ldgba cola_combined \
  --artifacts build-local/owl-annotations-integrated \
  --csv tests/owl-annotations-integrated.csv
python3 tests/summarize-owl-annotations.py
```

JSON manifests record measured source/binary hashes and raw input hashes.
Builds must finish before campaigns start. Interrupted decoder-development
measurements were discarded; only final stable-binary campaigns are reported.

[OWL options](https://github.com/owl-toolkit/owl#quick-start),
[TACAS 2017](https://arxiv.org/html/1701.06103v1).

The complete finite-witness rerun has 387 equivalent outputs and 585
budget/bypass checks, with no timeout or capacity failure.
