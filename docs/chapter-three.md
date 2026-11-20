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
| 3.16 | [QuarterCells](../src/AoP/QuarterCells.agda) characterizes positive outputs using the decimal value `a/d` with positive denominator. Half-up rounding of `4a/d` gives `n` exactly on `[(2n−1)/8,(2n+1)/8)`: for outputs 1, 2, 3 the cut points are `.125`, `.375`, `.625`, `.875`. Both implications are checked by clearing the denominator and cancelling the rounding offset. [QuarterZero](../src/AoP/QuarterZero.agda) proves that the zero cell consists exactly of nonnegative values strictly below `1/8`; the tie at `1/8` belongs to output 1. [QuarterDigits](../src/AoP/QuarterDigits.agda) evaluates a digit list as a place-value numerator over a power of ten and specializes both cell equivalences to those values. The digits `[1,2,5]` give `125/1000`. [QuarterRound](../src/AoP/QuarterRound.agda) computes the rounded output with a proof that the input belongs to its cell. The reference calculation scans the numerator of `(8a+d)/(2d)` one unit at a time, moving to the next cell exactly at its lower endpoint. [QuarterUnique](../src/AoP/QuarterUnique.agda) proves that cells with different indices are disjoint, so a certificate for any proposed index determines the scanner’s output. |
| 3.17 | [SeventeenGrid](../src/AoP/SeventeenGrid.agda) checks `10^17 = 131072 × 5^17`. In units of `10^−17`, each rounding boundary is an integer; `preserve` proves that discarding a proper fractional tail preserves every such threshold test, including ties. [DecimalTailBound](../src/AoP/DecimalTailBound.agda) proves `num ds < den ds` for every finite decimal tail, discharging the proper-fraction premise even for strings of nines. [SixteenDigitsFail](../src/AoP/SixteenDigitsFail.agda) checks the first midpoint `.00000762939453125` directly with `intern`: the 17-digit input gives one unit, while its 16-digit prefix gives zero. [DivisionThreshold](../src/AoP/DivisionThreshold.agda) connects the primitive integer division used by `cshift` and `halve` to threshold inequalities: with countdown `j` and divisor `k+1`, reaching quotient `t+1` takes `j+1+t*(k+1)` ticks. [TeXStateBound](../src/AoP/TeXStateBound.agda) proves that every suffix accumulator lies below `131072`: even digit 9 keeps the numerator below `10 × 131072` before division. The general `intern`/`take 17` equation remains open. |
| 3.18–3.19 | [FloorRule](../src/AoP/FloorRule.agda): equality follows from equality of lower bounds in a partial order. The floor rule then follows given transfer of the integer threshold across positive division and integral translation; [FractionThreshold](../src/AoP/FractionThreshold.agda) proves the threshold equivalence for a nonnegative mixed rational `n+r/d`, `r<d`, natural offset `a`, and positive divisor `b`: multiplying by `d` places the remainder strictly within its denominator block. [SignedFloorThreshold](../src/AoP/SignedFloorThreshold.agda) moves the negative terms to the opposite side before clearing denominators, giving the same threshold equivalence for signed offsets, whole parts and thresholds represented by differences of naturals. The worked value `−9/8` meets threshold `−2` and fails threshold `−1`. This arithmetic covers mixed rationals. |
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
| 3.32 | [DistributiveHoms](../src/AoP/DistributiveHoms.agda) derives the hom-set bijection for `(A + B) × C`: curry, split at the coproduct, then uncurry each branch. Reassembling the two branches gives an arrow out of `(A × C) + (B × C)` with the same target. `distribute` checks both inverse laws for this correspondence using propositional equality of arrows. [RepresentingIso](../src/AoP/RepresentingIso.agda) proves the general final step: a natural invertible correspondence of outgoing arrows yields inverse arrows between the representing objects. [InverseNaturality](../src/AoP/InverseNaturality.agda) reverses a naturality square using the section and retraction laws, so the inverse steps need no separate naturality assumptions. [DistributiveSquare](../src/AoP/DistributiveSquare.agda) composes those squares: postcomposition commutes with the distributivity bijection when currying and splitting are natural in the target. [ClosedDistributivity](../src/AoP/ClosedDistributivity.agda) applies that correspondence to both identities, obtaining inverse arrows between `(A + B) × C` and `(A × C) + (B × C)`. This instantiation assumes small object and hom types, categorical equality reflecting propositional equality of arrows, and target-natural currying and coproduct bijections. |
| 3.33–3.34 | [ExponentialCases](../src/AoP/ExponentialCases.agda): exponentials indexed by zero, one and a coproduct, and global elements of function spaces; pointwise inverse laws in `Fun`. |
| 3.35 | [PreorderExponential](../src/AoP/PreorderExponential.agda): in a preorder with finite meets, an exponential `b^a` is a greatest `x` satisfying `x ∧ a ≼ b`. Both implications of this characterization are checked. |
| 3.36 | [ExponentialFunctor](../src/AoP/ExponentialFunctor.agda): curry `f ∘ eval` to lift `f` to function spaces. Evaluation and uniqueness give the identity and composition laws in an arbitrary category with the specified exponentials. |
| 3.37 | Open: treat cartesian closure of the functor category. |
| 3.38 | [MapNaturality](../src/AoP/MapNaturality.agda): list map is natural contravariantly in the input element type and covariantly in the output. |
| 3.39 | [ListStrength](../src/AoP/ListStrength.agda): derive the right-list product by currying and mapping, with the left-list variant. |
| 3.40 | [FunStrength](../src/AoP/FunStrength.agda) proves the book’s strength condition on `Fun`. [SwapStrength](../src/AoP/SwapStrength.agda) gives a functor on `Fun × Fun` with no possible strength component. |
| 3.41 | [ParameterRecursion](../src/AoP/ParameterRecursion.agda) proves existence and pointwise uniqueness for container trees: each recursive request selects an immediate child and updates the parameter, and the algebra respects pointwise equality on child results. The parameter need not decrease. [ParameterFold](../src/AoP/ParameterFold.agda) extends the construction to arbitrary endofunctors on `Fun` with an initial input algebra and a natural parameter-routing transformation. Folding into `P → B` gives a solution; uniqueness uses extensionality only for that function space. A formulation over an arbitrary cartesian closed category remains open. |
| 3.42–3.43 | [Iteration](../src/AoP/Iteration.agda): unique iteration, addition by iterating successor, and composition by adding counts. |
| 3.44 | [IndexedBranches](../src/AoP/IndexedBranches.agda): a strictly positive tree with a branch per index and its structural fold. |
| 3.45 | [AccumulatorFusion](../src/AoP/AccumulatorFusion.agda): evaluating a fused function-valued fold at a neutral accumulator recovers the initial answer. |
| 3.46–3.47 | [ConversionFold](../src/AoP/ConversionFold.agda) derives linear snoc-list conversion; [ReverseAccumulator](../src/AoP/ReverseAccumulator.agda) derives reversal with a suffix accumulator. |
| 3.48–3.49 | [DepthAccumulator](../src/AoP/DepthAccumulator.agda) propagates tip depth down the tree. [MinimumDepth](../src/AoP/MinimumDepth.agda) prunes subtrees with a remaining-distance bound. |
| 3.50–3.51 | [SnocLoop](../src/AoP/SnocLoop.agda) proves state-loop uniqueness. [LoopConversion](../src/AoP/LoopConversion.agda) implements each representation’s fold by a loop on the other. |
