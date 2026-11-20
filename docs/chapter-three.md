# Chapter 3: paired folds, Horner’s rule, and TeX decimal input

This inventory lists exercises 3.1–3.51 and selected worked derivations in §§3.1–3.5. The [one-pass average](../src/AoP/Average.agda) illustrates pairing two independent folds; the [steep-list test](../src/AoP/Steep.agda) uses a pair in which one result depends on the other. For Horner’s rule, compare the [list triangle](../src/AoP/Horner.agda) with the [depth-labelled tree](../src/AoP/TipDepths.agda). Both derivations eliminate an intermediate structure by moving an operation through the final reduction.

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

## §3.3: decimal input for TeX

Given decimal digits after the point, return the nearest count of units of size `1/65536`, rounding ties upward. [TeXFraction](../src/AoP/TeXFraction.agda) folds the digits from the right with one extra binary digit of precision, then rounds once. Its refinement from exact valuation assumes the floor-and-shift identity. For example, `.00007` and `.00008` both round to 5 units, but prefixing a zero makes their rounded values differ.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 3.15 | [DecimalTriangle](../src/AoP/DecimalTriangle.agda): derive the decimal valuation fold from a triangle, assuming exact division by ten preserves zero and addition. |
| 3.16 | Open: characterize all decimal inputs for each output at quarter-unit precision. |
| 3.17 | Open: prove that retaining the first 17 decimal digits preserves the rounded result for every finite input. |
| 3.18–3.19 | [FloorRule](../src/AoP/FloorRule.agda): equality follows from equality of lower bounds in a partial order. The floor rule then follows given transfer of the integer threshold across positive division and integral translation; the concrete arithmetic instance remains open. |
| 3.20 | [FloorCounterexample](../src/AoP/FloorCounterexample.agda): exact half-integers witness failure for a fractional offset and for a fractional divisor. |
| 3.21 | [ExtendUpdate](../src/AoP/ExtendUpdate.agda): extend an update along an injection given an image test that supplies a preimage. |
| 3.22 | [RoundingCollision](../src/AoP/RoundingCollision.agda): two reachable decimal suffixes with the same rounded value give distinct results after the same digit is prefixed. |

## §3.4: conditions and conditionals

[Conditions](../src/AoP/Conditions.agda) distributes an input paired with a Boolean tag into two branches. Both branches retain the input. The calculation of equation 3.3 moves a function after a conditional into both branches. [BranchTags](../src/AoP/BranchTags.agda) checks the precomposition and equal-branch equations 3.4–3.5 pointwise. The abstract categorical calculations for these equations remain open.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 3.23, 3.27 | [StrictInitial](../src/AoP/StrictInitial.agda): the projection triangle gives both inverse equations; pairing `id` with an arrow to `0` then proves that its source is initial. |
| 3.24 | [RelDistribution](../src/AoP/RelDistribution.agda): no relation can invert the comparison that merges two copies of a singleton. The module uses the description of products and coproducts in `Rel` as tagged unions. |
| 3.25–3.26 | [BranchTags](../src/AoP/BranchTags.agda): recover a predicate from its tag and prove that mapping over the payload preserves the tag, in `Fun`. |
| 3.28 | [DistributedCase](../src/AoP/DistributedCase.agda): derive the product/case identity in `Fun` using cancellation of distribution. |
| 3.29 | [Quad](../src/AoP/Quad.agda): encode two Booleans as one of four tags, verify both round trips, and recover conjunction. |
| 3.30 | [FilterMap](../src/AoP/FilterMap.agda): derive the filter/map law by moving `map` past concatenation and simplifying each singleton-or-empty contribution. |

## §3.5: concatenation and currying

[Currying](../src/AoP/Currying.agda) implements concatenation as a fold whose result accepts a suffix. The [tip traversal calculation](../src/AoP/TipTraversal.agda) applies the same idea to trees: the two suffix functions at a fork compose, preserving left-to-right order and eliminating repeated list appends.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 3.31 | [AppendEquation](../src/AoP/AppendEquation.agda) splits equation 3.6 into its two constructor laws and recombines them in `Fun`. |
| 3.32 | Open: derive distributivity from cartesian closure and coproducts. |
| 3.33–3.34 | [ExponentialCases](../src/AoP/ExponentialCases.agda): exponentials indexed by zero, one and a coproduct, and global elements of function spaces; pointwise inverse laws in `Fun`. |
| 3.35 | [PreorderExponential](../src/AoP/PreorderExponential.agda): in a preorder with finite meets, an exponential `b^a` is a greatest `x` satisfying `x ∧ a ≼ b`. Both implications of this characterization are checked. |
| 3.36–3.37 | Open: construct the exponential functor in an arbitrary cartesian closed category and treat cartesian closure of the functor category in 3.37. |
| 3.38 | [MapNaturality](../src/AoP/MapNaturality.agda): list map is natural contravariantly in the input element type and covariantly in the output. |
| 3.39 | [ListStrength](../src/AoP/ListStrength.agda): derive the right-list product by currying and mapping, with the left-list variant. |
| 3.40 | [FunStrength](../src/AoP/FunStrength.agda) proves the book’s strength condition on `Fun`. [SwapStrength](../src/AoP/SwapStrength.agda) gives a functor on `Fun × Fun` with no possible strength component. |
| 3.41 | Open: state and prove the general sufficient conditions for unique solution with a parameter. |
| 3.42–3.43 | [Iteration](../src/AoP/Iteration.agda): unique iteration, addition by iterating successor, and composition by adding counts. |
| 3.44 | [IndexedBranches](../src/AoP/IndexedBranches.agda): a strictly positive tree with a branch per index and its structural fold. |
| 3.45 | [AccumulatorFusion](../src/AoP/AccumulatorFusion.agda): evaluating a fused function-valued fold at a neutral accumulator recovers the initial answer. |
| 3.46–3.47 | [ConversionFold](../src/AoP/ConversionFold.agda) derives linear snoc-list conversion; [ReverseAccumulator](../src/AoP/ReverseAccumulator.agda) derives reversal with a suffix accumulator. |
| 3.48–3.49 | [DepthAccumulator](../src/AoP/DepthAccumulator.agda) propagates tip depth down the tree. [MinimumDepth](../src/AoP/MinimumDepth.agda) prunes subtrees with a remaining-distance bound. |
| 3.50–3.51 | [SnocLoop](../src/AoP/SnocLoop.agda) proves state-loop uniqueness. [LoopConversion](../src/AoP/LoopConversion.agda) implements each representation’s fold by a loop on the other. |
