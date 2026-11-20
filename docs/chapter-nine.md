# Chapter 9: dynamic programming

## §9.1 Theory

[TaggedThinning](../src/AoP/TaggedThinning.agda) checks both injection laws in exercise 9.5. When every input candidate has the same tag, every retained candidate has that tag. Removing the tags gives a thinning under that branch’s comparison, and every such thinning can be lifted back. [DisjointFibres](../src/AoP/DisjointFibres.agda) shows that the two ranges are disjoint exactly when restricting the right range to the complement of the left leaves it unchanged. Given a decision procedure for membership in the left range, the inverse fibre of the copair is obtained by selecting the corresponding tagged fibre. The final derivation of Proposition 9.1 remains open.

## §9.2 The string edit problem

[ScriptLengthOrder](../src/AoP/ScriptLengthOrder.agda) verifies exercise 9.6. Prepending one command to each script preserves their length comparison, even when the commands differ. This proves the point-free cons monotonicity law for the shortest-script objective.

## §9.3 Optimal bracketing

[MatrixBracketCost](../src/AoP/MatrixBracketCost.agda) checks the size and cost functions in exercise 9.10. A matrix product of sizes `i × k` and `k × j` has size `i × j` and adds `i·k·j` scalar multiplications to the two subtree costs. For input dimensions `2 × 3`, `3 × 4`, and `4 × 5`, the two bracketings cost 64 and 90, respectively. The type indices ensure that each intermediate product has compatible dimensions. The cost counts ordinary dense scalar multiplications.

[AssociativeBrackets](../src/AoP/AssociativeBrackets.agda) proves exercise 9.12. Folding the nonempty list of leaves equals folding the bracketing tree directly. The intermediate append law uses associativity alone; nonempty lists eliminate the need for a unit.

[BracketMinimum](../src/AoP/BracketMinimum.agda) gives an exhaustive bracketing solver and [AppendOptimal](../src/AoP/AppendOptimal.agda) proves optimality for the list-append cost model. The same-input optimal-subtree argument and enumerator support comparison with the book’s interval algorithm.

## §9.4 Data compression

[DictionarySearch](../src/AoP/DictionarySearch.agda) certifies a least-cost encoding by bounded exhaustive search. The dictionary dynamic program and its derivation remain open.

## Numbered exercise inventory

| Exercise | Subject and checked scope |
| --- | --- |
| 9.1 | Open: specialize the general dynamic-programming theorem to the first theorem. |
| 9.2 | Open: weaken both dynamic-programming hypotheses using context. |
| 9.3 | Open: general proof of Theorem 9.2. |
| 9.4 | Open: construct a thinning comparison from the objective and examine its implementation cost. |
| 9.5 | Both tag laws and the concrete disjoint-range calculation above; final composition open. |
| 9.6 | Script-length cons monotonicity above. |
| 9.7 | Open: derive the relational tail condition for string editing. |
| 9.8 | Open: decimal-addition size and work model. |
| 9.9 | Open: decimal-multiplication size and work model. |
| 9.10 | Dimension-indexed matrix costs above. |
| 9.11 | [AppendOptimal](../src/AoP/AppendOptimal.agda): right association attains the append-work lower bound. |
| 9.12 | Associative nonempty fold fusion above. |
| 9.13 | Open: calculate the loop over initial segments via snoc recursion and derive (9.9). |
| 9.14 | Open research exercise: derive a thinning fold for bracketing via converse flattening. |
| 9.15 | Open: optimize over permutations as well as bracketings for commutative operations. |
| 9.16 | Open: prove the dictionary cost algebra monotone. |
| 9.17 | Open: prove the decoder’s initial-segment simulation law. |
| 9.18 | Open: explain failure of the proposed prefix comparison. |
| 9.19 | [UniformCodeCost](../src/AoP/UniformCodeCost.agda): with common charge `w`, bit cost equals code length times `w`. Minimizing the number of elements therefore suffices, including `w = 0` when all codes tie. This justifies the objective simplification; the dynamic encoder remains open. |
| 9.20 | Open research exercise: derive a dictionary thinning fold on codes with an initial literal. |

The inventory covers all 20 numbered exercises. The audit of unnumbered examples and intermediate derivations continues.
