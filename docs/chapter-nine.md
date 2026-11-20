# Chapter 9: dynamic programming

## §9.1 Theory

[TaggedThinning](../src/AoP/TaggedThinning.agda) checks the left-injection thinning law in exercise 9.5. Thinning a set of left-tagged candidates can only retain left-tagged values. Removing their tags gives a thinning under the left comparison, and any such thinning can be lifted back. The right-injection law, disjoint-range calculation, and full proposition remain open.

## §9.2 The string edit problem

[ScriptLengthOrder](../src/AoP/ScriptLengthOrder.agda) verifies exercise 9.6. Prepending one command to each script preserves their length comparison, even when the commands differ. This proves the point-free cons monotonicity law for the shortest-script objective.

## §9.3 Optimal bracketing

[MatrixBracketCost](../src/AoP/MatrixBracketCost.agda) checks the size and cost functions in exercise 9.10. A matrix product of sizes `i × k` and `k × j` has size `i × j` and adds `i·k·j` scalar multiplications to the two subtree costs. For input dimensions `2 × 3`, `3 × 4`, and `4 × 5`, the two bracketings cost 64 and 90, respectively. The type indices ensure that each intermediate product has compatible dimensions. The cost counts ordinary dense scalar multiplications.

[AssociativeBrackets](../src/AoP/AssociativeBrackets.agda) proves exercise 9.12. Folding the nonempty list of leaves equals folding the bracketing tree directly. The intermediate append law uses associativity alone; nonempty lists eliminate the need for a unit.

[BracketMinimum](../src/AoP/BracketMinimum.agda) gives an exhaustive bracketing solver and [AppendOptimal](../src/AoP/AppendOptimal.agda) proves optimality for the list-append cost model. A full inventory of numbered exercises, unnumbered examples and intermediate derivations remains open.
