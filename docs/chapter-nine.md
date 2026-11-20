# Chapter 9: dynamic programming

## §9.3 Optimal bracketing

[MatrixBracketCost](../src/AoP/MatrixBracketCost.agda) checks the size and cost functions in exercise 9.10. A matrix product of sizes `i × k` and `k × j` has size `i × j` and adds `i·k·j` scalar multiplications to the two subtree costs. For input dimensions `2 × 3`, `3 × 4`, and `4 × 5`, the two bracketings cost 64 and 90, respectively. The type indices ensure that each intermediate product has compatible dimensions. The cost counts ordinary dense scalar multiplications.

[BracketMinimum](../src/AoP/BracketMinimum.agda) gives an exhaustive bracketing solver and [AppendOptimal](../src/AoP/AppendOptimal.agda) proves optimality for the list-append cost model. A full inventory of numbered exercises, unnumbered examples and intermediate derivations remains open.
