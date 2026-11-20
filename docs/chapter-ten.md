# Chapter 10: greedy algorithms

## §10.1 Theory

[BranchingGreedy](../src/AoP/BranchingGreedy.agda) verifies a branch-selection algorithm from a monotone cost extension and an exchange witness. The abstract relational derivations still need an audit.

## §10.2 Tab compression

[Detab](../src/AoP/Detab.agda) expands tabs to blanks at fixed tab stops. [EntabMinimum](../src/AoP/EntabMinimum.agda) proves that the buffered encoder produces a shortest representation at every positive width. [TabPrefixExample](../src/AoP/TabPrefixExample.agda) checks the width-eight example that rules out unrestricted prefix pruning: five glyphs and a tab encode eight columns in six characters, but the seven-column prefix requires at least seven characters. The exercises also examine alternative objectives and the intermediate loop derivation.

| Exercise | Calculation and scope |
| --- | --- |
| 10.1 | [ProjectedLoop](../src/AoP/ProjectedLoop.agda) proves the streaming loop equivalent to projecting the output of the accumulating loop. The invariant allows an arbitrary saved output prefix and column state; specializing to the empty prefix gives the exercise equation. |
| 10.2 | [TabCountObjective](../src/AoP/TabCountObjective.agda) checks a width-two counterexample. Both `TAB` and `BLANK TAB` expand to two blanks. One tab is the maximum over every valid encoding, yet the second encoding is longer. |
| 10.3 | [BlankTie](../src/AoP/BlankTie.agda) proves snoc-length monotonicity and refines the shortest encoder with a postprocessing pass: replace each tab spanning one column with a blank. Expansion and encoded length are preserved at every positive width, so shortestness transfers. |
| 10.4 | [FillPrefixes](../src/AoP/FillPrefixes.agda) proves the empty-input law for the fill-restricted prefix relation. For unrestricted prefixes it proves the empty and snoc laws and refutes the fill law at width one: the empty prefix of a filled empty line differs from the one-blank output. The restricted fill and snoc calculations remain open. |

## §10.3 Minimum tardiness

[ScheduleCertificate](../src/AoP/ScheduleCertificate.agda) certifies the backward greedy algorithm against all permutations. [TardinessExample](../src/AoP/TardinessExample.agda) checks all six schedules of a three-job instance. The following entries separate the book’s calculations and variations from that correctness result.

| Exercise | Derivation or variant to audit |
| --- | --- |
| 10.5 | [ScheduleAlgebraOrder](../src/AoP/ScheduleAlgebraOrder.agda) proves monotonicity using job lists related by permutation as representatives of one bag. Their durations sum to the same time, so the appended job incurs the same penalty; maximum preserves the prefix cost comparison. |
| 10.6 | [ScheduleCostFactor](../src/AoP/ScheduleCostFactor.agda) proves (10.4) for empty and extended schedules: the cost is the maximum of the final job’s penalty and the prefix cost, with both components zero in the empty case. |
| 10.7 | Derive the insertion comparison using fixed-point induction. |
| 10.8 | Derive the bag-algebra equation for permutation generation. |
| 10.9 | Derive the equal-weight schedule and its sorting time bound. |
| 10.10 | Generalize the objective to signed lateness and a bottom cost for the empty schedule. |
| 10.11 | [SumTardiness](../src/AoP/SumTardiness.agda) refutes the chapter’s backward minimum-final-penalty rule for the sum objective. Two jobs due at zero have durations 3 and 1 and weights 2 and 1. Selecting the short job last gives total 10; reversing them gives 9. This concerns that specific rule. |

## §10.4 TeX decimal output

[TeXExternal](../src/AoP/TeXExternal.agda) specifies shortest round-tripping output and verifies particular values. The general shortest printer and the stricter closest-output tie rule remain open.

| Exercise | Remaining construction |
| --- | --- |
| 10.12 | [DigitInterval](../src/AoP/DigitInterval.agda) proves uniqueness for a nonnegative rational scaled fraction `n/w`, with positive denominator. After clearing denominators the digit must satisfy `d*w ≤ n < (d+1)*w`; two distinct digits would force `n < n`. |
| 10.13 | Derive the printer using integer arithmetic throughout. |
| 10.14 | Isolate the nonintegral-quotient hypothesis on the scale and remove it. |
| 10.15 | Characterize the selected shortest decimal and refine ties by distance to the represented value. |

This inventory tracks all 15 numbered exercises. The unnumbered worked examples and intermediate derivations still need a separate audit.
