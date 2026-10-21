# Deterministic automaton sizes on OWL's literature collection

This is the historical comparison at commit `c809a2e`, before the subsequent
[GF/FG/DBA routing changes](ltl-routing-diagnosis.md). The
[updated matched comparison](ltl-fragment-summary.md) retains these reference
tool outputs and reruns both COLA modes.

Experiments performed locally on 21 October 2026. The aim is to compare the
sizes of deterministic automata for the same LTL formula, allowing general
Emerson–Lei acceptance rather than forcing every output into parity form.

**LTL3TELA produced the smallest automata most often on the common successful
subset, with a reliability caveat.** On the 222 formulas completed by all
configurations, it was tied for smallest or strictly smallest on 217 formulas,
versus Spot on 207. Against Spot it produced 11 smaller outputs, 211 equal
outputs and no larger outputs. Its total of 991 states is 6.3% below Spot's
1058; the geometric mean paired state ratio is 0.9784. Most cases are ties.

| Configuration | Smallest, including ties (of 222) | Total complete states | Timeouts (of 227) | Crashes |
| --- | ---: | ---: | ---: | ---: |
| LTL3TELA | 217 | 991 | 4 | 1 |
| Spot | 207 | 1058 | 2 | 0 |
| DELAG | 194 | 1207 | 0 | 0 |
| OWL SLM21 | 183 | 1115 | 0 | 0 |
| COLA | 192 | 1337 | 2 | 0 |
| COLA reset | 191 | 1338 | 2 | 0 |

DELAG and OWL completed every input. On the two hardness formulas where
Spot, LTL3TELA and both COLA modes timed out, OWL produced 89 and 163 states
versus DELAG's 122 and 196. Those pairs passed language equivalence using
DELAG as the alternate reference. These formulas are outside the common
222-formula ranking, so availability and size should be considered together.

LTL3TELA crashed with SIGSEGV on SomenziB00 line 11,
`(Xa U Xb) | X(!a R !b)`. One isolated rerun reproduced return code -11;
the record is retained at `build-local/ltl3tela-crash-recheck.json`. This is
an observation about this build/configuration with Spot 2.14.1, not a claim
about every release or compiler. There were no detected language mismatches
or nondeterministic outputs among the translations that completed.

The reset option gives **no size improvement over default COLA on this
corpus**: 224 paired outputs have equal states and one grows from three to
four states (SickertEJK16 line 3, `GF(Fa | GXb | FG(a | XXb))`). Seven formula
runs actually complete reset monitors; none exhaust the finite-witness
budget. COLA's larger regression is structural: Boolean GF/FG combinations
can give products of up to 84 states where the other tools use one state.
The earlier nested-kernel benchmark gains therefore do not generalise to
this literature collection. Keep the reset feature optional.

For this collection, LTL3TELA is a strong size-oriented candidate when it
finishes, Spot is a close baseline, and DELAG/OWL cover hard cases that the
others miss under this time budget. A portfolio that retains the smallest
verified output would be preferable to claiming that one tool always wins.

See [the measured summary](ltl-size-summary.md) for outcomes, winners including
ties, paired wins/ties/losses, sizes by collection, and examples. The
[per-formula CSV](ltl-size-results.csv) contains full formulas, raw and
completed sizes, acceptance-set counts, routing counters and failure status.

## Corpus and tools

All eight `.ltl` files from OWL's
[literature collection at commit 632c2da](https://github.com/owl-toolkit/owl/tree/632c2da3ec982cdda340305afb9a3ddf45000491/data/formulas/literature)
are included unchanged in [ltl-size-corpus](ltl-size-corpus/README.md).
There are 237 entries and 227 distinct formula strings. Exact-string duplicates
are translated once; every original file/line membership is retained in the
CSV. There is no filtering by formula difficulty or applicability of the
finite-witness construction. This is the literature directory, not every
regression or generated formula in OWL's repository.

| Configuration | Version / construction | Command before `-f FORMULA` |
| --- | --- | --- |
| Spot | 2.14.1, deterministic generic | `ltl2tgba --deterministic --generic` |
| DELAG | OWL 21.0, MS17 | `owl ltl2dela -t MS17` |
| LTL3TELA | 2.1.1, deterministic mode | `ltl3tela -D1` |
| OWL | 21.0, SLM21 | `owl ltl2dela -t SLM21` |
| COLA | branch commit e1ed093, defaults | `ltl2dela` |
| COLA reset | same binary, optional finite witnesses | `ltl2dela --finite-witness --stats` |

The [OWL documentation](https://github.com/owl-toolkit/owl) identifies MS17
as the original DELAG construction and SLM21 as the default DELA translation.
Other options retain their defaults, including each tool's simplification
and portfolio choices. LTL3TELA's default `-b3` can select Spot/SPOTELA;
COLA also uses Spot internally and for fallback. These are comparisons of
tool configurations, not six entirely independent implementations.

Spot, COLA and LTL3TELA use the installed native arm64 Spot 2.14.1 library,
which supports at most 32 acceptance sets. COLA and LTL3TELA were built with
Apple Clang 17, C++17 and O2. OWL uses its official macOS amd64 21.0 native
release via Rosetta 2. Size counts remain comparable across these execution
architectures; wall times are not a controlled performance comparison.
The computer is an Apple M3 MacBook Air, 8 cores, 16 GB RAM, macOS 26.6.2.

LTL3TELA was built from
[02092ad](https://github.com/jurajmajor/ltl3tela/tree/02092adca492678407bd74b5d3bbe103d8c2b400).
Clang required moving two explicit template instantiations after their
definitions; [the exact build patch](ltl3tela-clang.patch) is retained. No
translation algorithm was changed. Versions, source and binary hashes are
recorded in [the environment manifest](ltl-size-environment.json).

## Method and interpretation

Every formula/tool translation runs in a separate process, sequentially,
with a 30-second timeout. Timeouts kill the process group. Outputs and stderr
are retained under `build-local/owl-comparison/CASE_ID/`. Results checkpoint
after each tool, and the runner supports `--resume` with configuration checks.

Spot `autfilt` counts reachable states, symbolic edges and acceptance sets,
and checks determinism. The primary sizes then apply the same completion
and unreachable-state removal to every output. No shared minimisation or
acceptance conversion is applied. Raw sizes are also retained: a partial
automaton can save one rejecting sink, which should not be mistaken for a
construction advantage. A smaller state count can trade off against more
edges or a more complex acceptance condition; all three counts are available.

Other outputs are language-checked against Spot using `autfilt
--equivalent-to`, with a separate 30-second timeout. If Spot translation
fails, the first other deterministic output becomes an explicitly labelled
alternate reference, and remaining available outputs are checked against it.
This supplies relative language agreement; it is not a formal proof that the
reference implements the input formula. The same limitation applies to a
Spot reference. Unchecked, inequivalent or nondeterministic outputs never
enter a verified size ranking.

The main ranking uses the common successful cohort across all six
configurations. Pairwise tables also use every successful formula for that
pair, so a failed third tool does not remove their evidence. Failures are
reported separately, never counted as small outputs or assigned a fabricated
size. Geometric mean ratios compare corresponding formulas to Spot; totals
and maxima are supplied because a few very large automata can dominate sums.
Best counts include ties. Separate strict-best counts avoid turning ties
into claims of superiority. Exact duplicates have no additional weight.

The CSV's elapsed times are single-run diagnostic wall times, including
startup, output and timeout polling. They are not repeated median benchmarks
and should not determine a speed ranking, particularly across Rosetta and
native binaries. The experiment answers a size question on a finite corpus;
it does not establish a universal smallest-automaton translator or optimality
of any output.

## Reproduction

Build this branch as described in [the finite-witness report](finite-witness-benchmarks.md).
Download the official OWL macOS amd64 release from
[release-21.0](https://github.com/owl-toolkit/owl/releases/tag/release-21.0),
and unpack it in `build-local/external/owl-21.0/`. Rosetta must already be
available to run that binary on Apple Silicon. On another platform, use a
matching distribution and record that change.

Download LTL3TELA at the pinned commit above into
`build-local/external/ltl3tela-master/`, apply `tests/ltl3tela-clang.patch`
with `patch -p1` in that source directory, and run `make`. Its Makefile uses
`g++ -std=c++17 -O2 ... -lspot -lbddx`; provide include/library paths if Spot
is not installed in the compiler's default search paths.

```sh
python3 tests/compare-ltl-sizes.py \
  --formulas tests/ltl-size-corpus \
  --cola build-local/.libs/ltl2dela \
  --cola-library build-local/src/.libs \
  --owl build-local/external/owl-21.0/bin/owl \
  --ltl3tela build-local/external/ltl3tela-master/ltl3tela \
  --csv tests/ltl-size-results.csv --artifacts build-local/owl-comparison

python3 tests/summarize-ltl-sizes.py tests/ltl-size-results.csv \
  --output tests/ltl-size-summary.md
```

Use a fresh CSV/artifact destination when reproducing an existing committed
campaign. Use `--resume` only to continue the same configuration and retained
HOA artifacts. `--limit N` supports small setup pilots, not the full ranking.
