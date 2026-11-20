# Chapter 8: dynamic programming

## §8.1 Thinning

Thinning retains a subset of candidates. Each original candidate must have a retained candidate that is at least as good under the chosen relation. For example, when the relation is equality, removing the last representative of a value would leave that value uncovered.

| Exercise | Construction and scope |
| --- | --- |
| 8.1 | [ThinIdentity](../src/AoP/ThinIdentity.agda) proves both directions: thinning by equality is exactly extensional equality of the input and output sets. |
| 8.2 | [Thinning](../src/AoP/Thinning.agda) proves reflexivity and transitivity of thinning from the corresponding laws of the comparison relation. |
| 8.3 | `min-after-thin` in [Thinning](../src/AoP/Thinning.agda) lifts a retained minimum to the original set using comparison inclusion and transitivity of the objective. |
| 8.4 | [ThinUnion](../src/AoP/ThinUnion.agda) shows that adding back any subset of the original candidates preserves a thinning. It proves the intermediate union membership inclusion. When the comparisons coincide, taking the same thinning twice witnesses the reverse inclusion up to extensional equality. |
| 8.5 | [SingletonThinning](../src/AoP/SingletonThinning.agda) proves that retaining just `a` is a valid thinning exactly when `a` is a minimum. Under equality the full Boolean set is a valid thinning of itself, yet neither singleton is valid. |
| 8.6 | [FibreThinning](../src/AoP/FibreThinning.agda) proves that thinning the results of one input is unchanged by restricting comparisons to pairs sharing a generating input. The input itself witnesses the extra condition for each coverage edge. |
| 8.7 | [ThinFamily](../src/AoP/ThinFamily.agda) proves (8.4) for indexed families with both power-relator coverage conditions. The converse fails: the union of the Boolean singletons can thin to `{false}` under universal comparison, but any thinning of `{true}` must retain `true`. |
| 8.8 | [GreedySingleton](../src/AoP/GreedySingleton.agda) specializes the cons-list thinning theorem to programs that choose a local minimum at every suffix. Exercise 8.5 turns local optimality into singleton thinning and the resulting global thinning back into global optimality. The abstract relator case remains open. |
| 8.9 | [MinimalThinning](../src/AoP/MinimalThinning.agda) proves that retaining all minimal members of a set is a valid thinning under a well-supported preorder. Exercise 7.31 supplies a retained member below each input member. |

## §8.2 Paths in a layered network

[FibreMinimumPrune](../src/AoP/FibreMinimumPrune.agda) verifies the local pruning step of exercise 8.11. Group candidates by their intermediate state. When each inhabited enabled group has a minimum and cost dominance within a group implies simulation dominance, retaining the group minima is a valid thinning. The full fold derivation and exercise 8.10’s branching variants remain open.

The numbered exercise and intermediate derivation inventory for the rest of Chapter 8 remains open.
