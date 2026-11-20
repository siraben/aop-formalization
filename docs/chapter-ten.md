# Chapter 10: greedy algorithms

## §10.1 Theory

[BranchingGreedy](../src/AoP/BranchingGreedy.agda) verifies a branch-selection algorithm from a monotone cost extension and an exchange witness. The abstract relational derivations still need an audit.

## §10.2 Tab compression

[Detab](../src/AoP/Detab.agda) expands tabs to blanks at fixed tab stops. [EntabMinimum](../src/AoP/EntabMinimum.agda) proves that the buffered encoder produces a shortest representation at every positive width. The exercises also examine alternative objectives and the intermediate loop derivation.

| Exercise | Calculation and scope |
| --- | --- |
| 10.1 | [ProjectedLoop](../src/AoP/ProjectedLoop.agda) proves the streaming loop equivalent to projecting the output of the accumulating loop. The invariant allows an arbitrary saved output prefix and column state; specializing to the empty prefix gives the exercise equation. |
| 10.2 | [TabCountObjective](../src/AoP/TabCountObjective.agda) checks a width-two counterexample. Both `TAB` and `BLANK TAB` expand to two blanks. One tab is the maximum over every valid encoding, yet the second encoding is longer. |
| 10.3 | Prove cost monotonicity of extension and derive the variant preferring a single blank on ties. |
| 10.4 | Prove the three prefix/fill laws and identify the failure when the fill constraint is removed. |

## §10.3 Minimum tardiness

[ScheduleCertificate](../src/AoP/ScheduleCertificate.agda) certifies the backward greedy algorithm against all permutations. [TardinessExample](../src/AoP/TardinessExample.agda) checks all six schedules of a three-job instance. The following entries separate the book’s calculations and variations from that correctness result.

| Exercise | Derivation or variant to audit |
| --- | --- |
| 10.5 | Monotonicity of the cost algebra with the remaining bag held fixed. |
| 10.6 | Factor schedule cost through maximum and the two component functions. |
| 10.7 | Derive the insertion comparison using fixed-point induction. |
| 10.8 | Derive the bag-algebra equation for permutation generation. |
| 10.9 | Derive the equal-weight schedule and its sorting time bound. |
| 10.10 | Generalize the objective to signed lateness and a bottom cost for the empty schedule. |
| 10.11 | Investigate greedy selection for the sum of penalties. |

## §10.4 TeX decimal output

[TeXExternal](../src/AoP/TeXExternal.agda) specifies shortest round-tripping output and verifies particular values. The general shortest printer and the stricter closest-output tie rule remain open.

| Exercise | Remaining construction |
| --- | --- |
| 10.12 | Prove uniqueness of the integer digit satisfying the interval bound. |
| 10.13 | Derive the printer using integer arithmetic throughout. |
| 10.14 | Isolate the nonintegral-quotient hypothesis on the scale and remove it. |
| 10.15 | Characterize the selected shortest decimal and refine ties by distance to the represented value. |

This inventory tracks all 15 numbered exercises. The unnumbered worked examples and intermediate derivations still need a separate audit.
