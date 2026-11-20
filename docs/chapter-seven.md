# Chapter 7: optimisation problems

## §7.1 Minimum and maximum

[TwoMinima](../src/AoP/TwoMinima.agda) proves exercise 7.8 for concrete reflexive relations `R` and `S`. If `R a b` and `S b a`, the set `{a,b}` has `a` as an `R`-minimum and `b` as an `S`-minimum. Conversely, any set witnessing those two minima gives the two comparisons. The reverse implication uses only membership and the lower-bound property; reflexivity enters when constructing the witness.

The complete exercise and worked-example inventory for this chapter remains open. Existing case-study entry points include [PartyExample](../src/AoP/PartyExample.agda), [CylinderExample](../src/AoP/CylinderExample.agda), and [VanExample](../src/AoP/VanExample.agda).
