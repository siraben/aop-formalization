# Chapter 3: paired folds and Horner’s rule

This inventory covers §§3.1–3.2. The [one-pass average](../src/AoP/Average.agda) illustrates pairing two independent folds; the [steep-list test](../src/AoP/Steep.agda) uses a pair in which one result depends on the other. For Horner’s rule, compare the [list triangle](../src/AoP/Horner.agda) with the [depth-labelled tree](../src/AoP/TipDepths.agda). Both derivations eliminate an intermediate structure by moving an operation through the final reduction.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 3.1 | [Average](../src/AoP/Average.agda): evaluating the sum and count algebras on their respective projections gives the paired update for both list constructors. |
| 3.2 | [ProductComparison](../src/AoP/ProductComparison.agda): the two mapped projections give a natural comparison from `F (A × B)` to `F A × F B`. |
| 3.3 | [Steep](../src/AoP/Steep.agda): maintain the suffix sum to test each entry with one comparison. |
| 3.4 | [AuxiliaryFold](../src/AoP/AuxiliaryFold.agda): use the auxiliary fold result at each child and recover the desired answer by projection. |
| 3.5 | [BalanceFold](../src/AoP/BalanceFold.agda): return each subtree’s size alongside its balance flag. Integer cross-products test the inclusive one-third and two-thirds bounds. |
| 3.6–3.7 | [Predecessors](../src/AoP/Predecessors.agda) derives the descending list; [FactorialFusion](../src/AoP/FactorialFusion.agda) multiplies it without allocating the list. |
| 3.8 | [MutualFold](../src/AoP/MutualFold.agda): mutual recursion for an initial algebra in `Fun`, with banana-split and the auxiliary fold as corollaries. |
| 3.9 | [Slice](../src/AoP/Slice.agda): applying `tri tail` drops `i` elements from row `i`. |
| 3.10 | [Hyperproduct](../src/AoP/Hyperproduct.agda): use commutativity to distribute squaring over multiplication, then fuse the triangle of repeated squarings. |
| 3.11 | [GeneralHorner](../src/AoP/GeneralHorner.agda): derive the generalized Horner rule in `Fun` for a natural transformation of layers and a compatible reduction. |
| 3.12 | [HornerMultiplier](../src/AoP/HornerMultiplier.agda): the constant-coefficient case forces the update to be multiplication by the evaluation point. |
| 3.13 | [PositionSum](../src/AoP/PositionSum.agda): derive the position-weighted sum from a triangle. Shifting a suffix one place adds its ordinary sum to its weighted sum. |
| 3.14 | [WeightedPaths](../src/AoP/WeightedPaths.agda): carry the total weight and weighted path length together. Increasing every tip depth by one adds the subtree’s total weight. |
