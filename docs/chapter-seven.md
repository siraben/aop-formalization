# Chapter 7: optimisation problems

## §7.1 Minimum and maximum

[TwoMinima](../src/AoP/TwoMinima.agda) proves exercise 7.8 for concrete reflexive relations `R` and `S`. If `R a b` and `S b a`, the set `{a,b}` has `a` as an `R`-minimum and `b` as an `S`-minimum. Conversely, any set witnessing those two minima gives the two comparisons. The reverse implication uses only membership and the lower-bound property; reflexivity enters when constructing the witness.

[MinimumComparison](../src/AoP/MinimumComparison.agda) derives exercises 7.9–7.10. Taking the second relation in 7.8 to be universal recovers `R a b` from a set containing `b` with `a` as an `R`-minimum. Testing inclusion of minima on that witness recovers inclusion of the underlying relations. Only `R` needs to be reflexive for this direction.

[UniqueMinimum](../src/AoP/UniqueMinimum.agda) checks exercise 7.11 for reflexive relations. Antisymmetry gives at most one minimum on each set. Conversely, the shared two-element witness from 7.8 turns uniqueness into antisymmetry. The reflexivity hypothesis matters for this converse: a two-cycle without self-loops has no minima and fails antisymmetry.

[LowerMinimum](../src/AoP/LowerMinimum.agda) proves exercises 7.5 and 7.12 for preorders. Transitivity makes every predecessor of a lower bound another lower bound; reflexivity supplies the converse witness. A member of a set is a minimum exactly when it precedes some minimum of that set.

[PrincipalMaximum](../src/AoP/PrincipalMaximum.agda) proves exercise 7.14. The maxima of the predecessors of `a` are exactly the elements `b` satisfying both `R b a` and `R a b`. This allows distinct maxima in a preorder.

[MinimumMeet](../src/AoP/MinimumMeet.agda) checks exercises 7.6 and 7.13. A minimum for the intersection of two relations is precisely a member minimizing both. Restricting a preorder to pairs with equal images under a function also preserves reflexivity and transitivity.

The complete exercise and worked-example inventory for this chapter remains open. Existing case-study entry points include [PartyExample](../src/AoP/PartyExample.agda), [CylinderExample](../src/AoP/CylinderExample.agda), and [VanExample](../src/AoP/VanExample.agda).
