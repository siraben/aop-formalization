# Chapter 7: optimisation problems

## §7.1 Minimum and maximum

[TwoMinima](../src/AoP/TwoMinima.agda) proves exercise 7.8 for concrete reflexive relations `R` and `S`. If `R a b` and `S b a`, the set `{a,b}` has `a` as an `R`-minimum and `b` as an `S`-minimum. Conversely, any set witnessing those two minima gives the two comparisons. The reverse implication uses only membership and the lower-bound property; reflexivity enters when constructing the witness.

[MinimumComparison](../src/AoP/MinimumComparison.agda) derives exercises 7.9–7.10. Taking the second relation in 7.8 to be universal recovers `R a b` from a set containing `b` with `a` as an `R`-minimum. Testing inclusion of minima on that witness recovers inclusion of the underlying relations. Only `R` needs to be reflexive for this direction.

The complete exercise and worked-example inventory for this chapter remains open. Existing case-study entry points include [PartyExample](../src/AoP/PartyExample.agda), [CylinderExample](../src/AoP/CylinderExample.agda), and [VanExample](../src/AoP/VanExample.agda).
