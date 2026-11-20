# Chapter 2: categories, functors, and transformations

[Browse the Agda sources](../src/AoP/Chapter02) · [Type-check this chapter](../src/AoP/Chapter02/Index.agda)

Chapter 1 obtained programs by following constructors. Chapter 2 asks why the resulting equations determine a program uniquely. Start with composition, then learn which equations survive a change of representation. In §2.6 those two ideas give a calculation that fuses a fold with its consumer.

## §2.1 Categories: calculating with arrows

Read `g ∘ f` from right to left: first run `f`, then `g`. Suppose `f ∘ g ≈ id`. To see why `g` is left-cancellable, take `g ∘ u ≈ g ∘ v` and calculate:

```text
u ≈ id ∘ u ≈ (f ∘ g) ∘ u ≈ f ∘ (g ∘ u)    left unit, hypothesis, associativity
  ≈ f ∘ (g ∘ v)                              substitute the proposed equality
  ≈ (f ∘ g) ∘ v ≈ id ∘ v ≈ v                reverse the first three steps
```

Here `≈` is equality of arrows in the chosen category. No inspection of individual inputs is needed. See [Cancellation](../src/AoP/Chapter02/Cancellation.agda).

For examples of categories, [PartialGraphCategory](../src/AoP/Chapter02/PartialGraphCategory.agda) models a partial function by a relation with at most one output per input. Composing two arrows retains a witness for the intermediate value. If two composite runs start at the same input, the first arrow forces their intermediate values to agree and the second forces their outputs to agree. [TotalPartialEmbedding](../src/AoP/Chapter02/TotalPartialEmbedding.agda) embeds `Fun` into `Par`: for `g` after `f`, the witness at `x` is `f x`. Equality of embedded graphs recovers pointwise equality of the original functions. [RelationGraphCategory](../src/AoP/Chapter02/RelationGraphCategory.agda) completes `Fun → Par → Rel`: forgetting the uniqueness proof preserves composition and reflects equality of partial arrows. In `Rel` a three-step path carries two intermediate points; associativity changes the nesting of those witnesses and preserves the path. [GraphInclusionTrace](../src/AoP/Chapter02/GraphInclusionTrace.agda) shows both inclusions are strict on Boolean arrows. A guard returns `true` on `true` and has no output on `false`, so no total function has its graph. Composing that guard with a relation that can return either bit produces two distinct outputs on `true`, so no partial function has the composite graph.

## §2.2 Functors: preserving composition

A functor acts on objects and arrows. Its composition law lets us replace `F (g ∘ f)` by `F g ∘ F f`; its identity law handles an empty sequence of steps.

[SquareProductFunctors](../src/AoP/Chapter02/SquareProductFunctors.agda) checks the identity and composition laws for two actions on pairs. The square functor uses one function on both coordinates: successor takes `(1,4)` to `(2,5)`. The product bifunctor takes a pair of functions: successor and identity take the same input to `(2,4)`. [InitialSegmentImage](../src/AoP/Chapter02/InitialSegmentImage.agda) calculates a relational example: the existential image of `{1,4}` under `≤` is `{0,1,2,3,4}`. Every number through 4 has 4 as a witness. More generally, the image of any predicate on naturals under `≤` is its least downward-closed superset. [MembershipImageUnion](../src/AoP/Chapter02/MembershipImageUnion.agda) treats the next example: taking the existential image of a family of subsets under membership forms their union. An output witness identifies both a chosen subset and the element’s membership in it. `include` and `least` show that this union contains each chosen subset and lies inside every common superset. The existential witness ranges over predicates in `Set₁`.

## §2.3 Natural transformations: moving an operation past a map

[PrefixTransformation](../src/AoP/Chapter02/PrefixTransformation.agda) packages cons-list prefix enumeration as a natural transformation from lists to lists of lists. For `x ∷ xs`, the empty prefix stays empty. Each other prefix begins with `x`: two applications of map composition move relabelling across that head, leaving the induction hypothesis for `xs`.

[ForkNaturality](../src/AoP/Chapter02/ForkNaturality.agda) gives a natural transformation from identity to the square functor. Duplicating `2` and applying successor to both coordinates gives `(3,3)`. The naturality equation lets us instead take successor once and duplicate the result. [MembershipImageSquare](../src/AoP/Chapter02/MembershipImageSquare.agda) proves the membership square for any relation `R`: choosing an input in `X` and following an `R` edge yields exactly the members of the existential image of `X`. The forward proof uses the image itself as the intermediate subset; the reverse proof recovers the input and edge from extensional equality with that image.

[PostWhiskering](../src/AoP/Chapter02/PostWhiskering.agda) gives the general calculation for applying a functor `H` to a natural transformation. Combine the first two mapped edges using the composition law, apply `H` to the original square, then expand the other composite into its two mapped edges. [UnionImageNaturality](../src/AoP/Chapter02/UnionImageNaturality.agda) checks the corresponding image calculation directly on predicates: following `R` from the union of a family gives precisely the union of its relational images. A witness identifies a chosen subset `X`, a member `a` of `X`, and an edge from `a` to the output. Both routes retain this evidence in different orders.

## §2.4 Universal objects: proving equality by uniqueness

[UniversalObjects](../src/AoP/Chapter02/UniversalObjects.agda) gives a singleton as a terminal object in `Fun`. [EmptyZeroObject](../src/AoP/Chapter02/EmptyZeroObject.agda) proves that the empty type is both initial and terminal in `Par` and `Rel`. An edge into the empty type would require an output there; an edge out would require an input there. In each case the empty graph supplies the unique arrow.

## §2.5 Products and coproducts

[ProductProjectionFunctors](../src/AoP/Chapter02/ProductProjectionFunctors.agda) constructs the two projection functors from a product category. Each selects one coordinate on objects and arrows. Given two functors with a common source, `Together.pair` applies them side by side; either projection recovers the corresponding original arrow action.

[SpanProduct](../src/AoP/Chapter02/SpanProduct.agda) constructs the category of spans with fixed endpoints `A` and `B`. A span is a common source with one arrow to each endpoint. A map between two spans preserves both arrows. `Pair.pair` reads pairing off the unique map to a terminal span: the two preservation equations give its projections, and terminality gives uniqueness. Conversely, `terminal` uses the pairing and projection laws to construct that terminal span in any category. Given one such span for every pair of objects, [SpanProductFunctor](../src/AoP/Chapter02/SpanProductFunctor.agda) derives the product bifunctor. The action on `(f,g)` pairs `f ∘ left` with `g ∘ right`. To prove composition, `path` observes the composite through either projection and cancels each of the two pairings in turn; uniqueness gives equality of the whole arrows. `absorption` follows the calculation in (2.8): fuse precomposition through the pair, then cancel its two projections to get `(f × g) ∘ ⟨p,q⟩ = ⟨f ∘ p,g ∘ q⟩`. `via-absorption` specializes `p` and `q` to the legs of the inner product arrow to recover the composition law. The two projection naturality squares then follow from cancellation: projecting `cross f g` on the left gives `f ∘ left`; projecting on the right gives `g ∘ right`.

[CoproductByDuality](../src/AoP/Chapter02/CoproductByDuality.agda) reads these proofs in the [opposite category](../src/AoP/Chapter02/OppositeCategory.agda), where the two projection arrows become injections. The absorption equation becomes `cases f g ∘ map h k = cases (f ∘ h) (g ∘ k)`: mapping each branch before handling it agrees with composing its own map and handler. `compose` likewise recovers the coproduct composition law.

[PartialGraphCoproduct](../src/AoP/Chapter02/PartialGraphCoproduct.agda) proves the coproduct property for arbitrary partial graphs. A tagged input selects exactly one branch; single-valuedness follows from that branch alone. Agreement on both injections determines the handler on every input, without deciding whether either branch is defined.

In `Rel` the same disjoint union also serves as a product. [RelSumProduct](../src/AoP/Chapter02/RelSumProduct.agda) takes the converses of the injections as projections. To pair two relations with a common input, tag each possible output by the branch that produced it. Projecting selects exactly that branch’s outputs; since every output carries a tag, the two projections determine the entire relation.

For partial functions presented as `Maybe` computations, [PartialProduct](../src/AoP/Chapter02/PartialProduct.agda) pairs outputs by distinguishing left-only, right-only, and both-defined cases. [PartialProductDecision](../src/AoP/Chapter02/PartialProductDecision.agda) explains the constructive scope of this case split. Pair an always-defined left leg with a right leg defined exactly when `P` holds. A shared tag supplies evidence for `P`; a left-only tag rules it out by single-valuedness. Thus extending this tagged construction uniformly to arbitrary partial graphs with these projections would decide every small `P`. [ExecutablePartialGraph](../src/AoP/Chapter02/ExecutablePartialGraph.agda) gives the exact criterion for using `Maybe` on an individual partial graph: at each input one can either supply an output and its edge, or refute the existence of any output. `encode` builds the computation from that decision; `decide` obtains the decision by inspecting a sound and complete computation.

[PolynomialSubstitution](../src/AoP/Chapter02/PolynomialSubstitution.agda) checks closure of unary polynomial expressions under composition. Replace each variable of `F` with `G`; `nest` and `flat` translate in both directions between values of the substituted expression and values of `F (G X)`. Both round trips preserve the original value, and `natural` shows that mapping preserves this translation. For `A + X × A`, only the first component of the right branch changes under a map on `X`.

## §2.6 Initial algebras: deriving fold fusion

Write `roll : F I → I` for the constructor of an initial algebra, `x : F X → X` and `y : F Y → Y` for two ways to process a layer. Suppose `m : X → Y` satisfies `m ∘ x ≈ y ∘ F m`. Can we calculate `m ∘ fold x` without first building an `X` result? Test whether it satisfies the defining equation of `fold y`:

```text
(m ∘ fold x) ∘ roll
≈ m ∘ (fold x ∘ roll)           associativity
≈ m ∘ (x ∘ F (fold x))          fold computation at x
≈ (m ∘ x) ∘ F (fold x)          associativity
≈ (y ∘ F m) ∘ F (fold x)        the hypothesis on m
≈ y ∘ (F m ∘ F (fold x))        associativity
≈ y ∘ F (m ∘ fold x)            functor composition
```

Thus `m ∘ fold x` is an algebra map from `I` to `Y`. Initiality supplies exactly one such map, so `m ∘ fold x ≈ fold y`. In Agda the middle calculation is `paste` in `AlgebraCategory`; `fusion` in `InitialAlgebraFolds` applies uniqueness to that composite. Initiality matters at the last step: merely satisfying the same equation would not give equality without it.

[AlgebraCategory](../src/AoP/Chapter02/AlgebraCategory.agda) constructs `Alg(F)` for an endofunctor on any category. An arrow changes the carrier while preserving the interpretation of one `F`-layer. The `paste` calculation proves closure under composition: slide the first carrier arrow through the source interpretation, then the second through the intermediate interpretation, and combine the two layer actions by functoriality.

[InitialAlgebraFolds](../src/AoP/Chapter02/InitialAlgebraFolds.agda) derives the fold laws in any category where `Alg(F)` has an initial object. Its unique arrow into a target algebra gives the fold. Composing that arrow with a homomorphism gives another arrow from the initial object, so uniqueness proves fusion. Folding into the algebra whose operation is `F` applied to the constructor gives a destructor; `roll-out` and `out-roll` check both inverse equations.

[NatAlgebraFold](../src/AoP/Chapter02/NatAlgebraFold.agda) applies this construction to `1 + X`. Testing the homomorphism square at the left injection gives `h 0 = seed`; testing it at the right injection gives `h (suc n) = step (h n)`. Conversely those two equations cover every layer. Their unique solution is the Chapter 1 iterator `foldn`, which supplies the arrow out of the initial algebra.

For strings, [InitialAlgebraBridge](../src/AoP/Chapter02/InitialAlgebraBridge.agda) turns the existing [list fold](../src/AoP/Chapter02/ListAlgebra.agda) into the unique arrow out of the character-list algebra. The empty string selects the seed; a cons layer passes its head character and the folded tail to the step. The bridge works in both directions for every endofunctor on `Fun`, keeping the same carrier function and computation proof.

[ModularAdditionHom](../src/AoP/Chapter02/ModularAdditionHom.agda) proves the addition homomorphism for every positive modulus `b`. Reducing `x + y` gives the same bounded residue as adding the two reduced operands modulo `b`. [RemainderUnique](../src/AoP/Chapter02/RemainderUnique.agda) justifies the key step: removing a whole copy of `b` leaves the remainder unchanged. For modulus 5, `8 + 9 = 17` reduces to 2; reducing the operands first gives `3 + 4 = 7`, also 2.

## §2.7 Changing the parameter of a datatype

[ChangeAlgebraParameter](../src/AoP/Chapter02/ChangeAlgebraParameter.agda) isolates the fusion step of (2.13) for any category. Given a natural transformation from layer functor `F` to `G`, pull a `G`-algebra back by changing the layer before interpreting it. When both initial algebras exist, folding into the pulled-back `G` constructor relabels an `F` value. `consume` proves that relabelling and then folding agrees with folding directly into the pulled-back consumer. [InitialTypeFunctor](../src/AoP/Chapter02/InitialTypeFunctor.agda) assembles these changes into a functor. Its input is the curried layer family: each parameter selects an endofunctor, each parameter arrow selects a natural transformation, and each selected endofunctor has a chosen initial algebra. For identity, the fold reduces to folding the constructor, so reflection applies. For composition, `consume` fuses the two folds; composing their changes of layer yields the fold for the composite parameter arrow. `constructor-square` shows why relabelling commutes with construction: unfold the defining fold once to relabel the recursive fields and the parameter in a single layer, then apply the target constructor.

[ListTypeFunctorFusion](../src/AoP/Chapter02/ListTypeFunctorFusion.agda) identifies the fold in (2.13) with ordinary `map` by its two constructor equations. Folding a consumer after relabelling changes only its cons step: it receives `f a` instead of `a`. Choosing a second relabelling as the consumer derives `relabel g (relabel f xs) = relabel (g ∘ f) xs` by fusion. Choosing addition instead gives the sum example in (2.14): summing after mapping successor over `[1,3,2]` becomes the single fold `2 + (4 + (3 + 0)) = 9`.

## Exercises

The register covers the 40 numbered exercises. The audit of unnumbered examples continues.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 2.1 | [Retractions](../src/AoP/Chapter02/Retractions.agda): applying the proposed right-unit law to the identity determines the arrow. |
| 2.2 | [ArrowEndpoints](../src/AoP/Chapter02/ArrowEndpoints.agda) types `k ∘ h ∘ f ∘ h` along the path `A → B → A → B → C`. For `g ∘ k ∘ h`, the output of `k` is `C` but the input of `g` is `A`; the mismatch is proved for the distinct node labels. |
| 2.3 | [Retractions](../src/AoP/Chapter02/Retractions.agda): use a chosen section to factor through its retraction, and prove the dual extension law. |
| 2.4–2.5 | [Cancellation](../src/AoP/Chapter02/Cancellation.agda): cancel a section on the left and a retraction on the right. If a composite is epic, its outer arrow is epic; if monic, its inner arrow is monic. |
| 2.6 | [PreorderCategory](../src/AoP/Chapter02/PreorderCategory.agda): every arrow cancels in both directions. On naturals, `1 → 0` has no return arrow. |
| 2.7 | [RelEpic](../src/AoP/Chapter02/RelEpic.agda): a shared input can hit two outputs without distinguishing them. Adding a private input for each output yields an epic relation that still has a multivalued input. |
| 2.8 | [ArrowCategory](../src/AoP/Chapter02/ArrowCategory.agda) constructs the arrow category by pasting commuting squares and proves that a square with two monic components is monic. [SquareMonic](../src/AoP/Chapter02/SquareMonic.agda) proves the top component must be monic by testing against identity arrows. If the base category has an initial object, the bottom component must also be monic, giving an exact componentwise criterion in that case. |
| 2.9–2.10 | [FunctorIso](../src/AoP/Chapter02/FunctorIso.agda) maps both inverse equations. [PreorderFunctor](../src/AoP/Chapter02/PreorderFunctor.agda) constructs a functor from a monotone map and reads monotonicity back from its action on arrows. |
| 2.11 | [HomAction](../src/AoP/Chapter02/HomAction.agda): precompose at the source and postcompose at the target. The proofs check identity, composition, and congruence on all three arrows. |
| 2.12 | [TreeFunctor](../src/AoP/Chapter02/TreeFunctor.agda): the tip mapping of §1.4 gives an endofunctor on functions. |
| 2.13 | [UniversalImage](../src/AoP/Chapter02/UniversalImage.agda): universal direct image preserves identity and composition. A missing preimage distinguishes it from ordinary direct image. |
| 2.14 | [SwapNatural](../src/AoP/Chapter02/SwapNatural.agda): construct both product functors, the swap transformation, and its inverse. |
| 2.15 | [SingletonImage](../src/AoP/Chapter02/SingletonImage.agda): prove singleton naturality for direct image; refute it for universal image. |
| 2.16 | [ProductNaturality](../src/AoP/Chapter02/ProductNaturality.agda): choosing one element per set commutes with taking direct images. The reverse inclusion collects a preimage for each choice. |
| 2.17 | [Whiskering](../src/AoP/Chapter02/Whiskering.agda): precompose a transformation with a functor and reuse the original square on each mapped arrow. |
| 2.18 | [PartialHead](../src/AoP/Chapter02/PartialHead.agda): a defined head and an undefined tail distinguish the two sides of the proposed naturality square. |
| 2.19 | [FunctorCategory](../src/AoP/Chapter02/FunctorCategory.agda) verifies the category laws componentwise. [WalkingArrow](../src/AoP/Chapter02/WalkingArrow.agda) converts between transformations and squares for two-object diagrams. [DiagramEvaluation](../src/AoP/Chapter02/DiagramEvaluation.agda) evaluates diagrams at the generating arrow and proves this functor is full, faithful, and surjective on objects. [ArrowDiagram](../src/AoP/Chapter02/ArrowDiagram.agda) constructs the reverse functor and proves that constructing a diagram and evaluating it recovers each arrow and square. [DiagramRoundTrip](../src/AoP/Chapter02/DiagramRoundTrip.agda) constructs inverse transformations between each original and rebuilt diagram, and proves the comparison is natural in the diagram. |
| 2.20 | [ConstantArrow](../src/AoP/Chapter02/ConstantArrow.agda): choosing an element of the source factors a constant arrow through the terminal object. |
| 2.21 | [EmptyTargets](../src/AoP/Chapter02/EmptyTargets.agda) classifies targets in `Fun` up to source isomorphism: exactly the uninhabited types qualify. A constant map from the two Booleans refutes the property for any inhabited target. [EmptyProductTargets](../src/AoP/Chapter02/EmptyProductTargets.agda) proves that both components must be uninhabited in `Fun × Fun`: test each component with a constant Boolean map and use the empty source in the other component. [EmptyRelationTargets](../src/AoP/Chapter02/EmptyRelationTargets.agda) rules out every target in `Rel`: the empty relation from `Bool` has inhabited source and cannot have a left inverse, since no composite through it contains the identity pair at `true`. |
| 2.22 | [TerminalDiagrams](../src/AoP/Chapter02/TerminalDiagrams.agda): in the book’s preorder orientation, a terminal object is a least element. |
| 2.23 | [ProductCategory](../src/AoP/Chapter02/ProductCategory.agda): construct the product category and pair initial or terminal objects componentwise. |
| 2.24 | [TerminalDiagrams](../src/AoP/Chapter02/TerminalDiagrams.agda): the constant diagram at the target’s terminal object is terminal in the functor category. |
| 2.25 | [OrderProducts](../src/AoP/Chapter02/OrderProducts.agda): maximum and minimum satisfy the product and coproduct bounds in the natural-number preorder. |
| 2.26 | [ProductUnit](../src/AoP/Chapter02/ProductUnit.agda), [ProductSymmetry](../src/AoP/Chapter02/ProductSymmetry.agda), and [ProductAssociator](../src/AoP/Chapter02/ProductAssociator.agda) derive the inverse and naturality laws from product projections. |
| 2.27 | [ExchangeLaw](../src/AoP/Chapter02/ExchangeLaw.agda): pairing commutes with case analysis by product and coproduct uniqueness. |
| 2.28 | [ProjectionEpic](../src/AoP/Chapter02/ProjectionEpic.agda): injections are monic; projections can fail to be epic with an empty factor. |
| 2.29 | [ArrowProducts](../src/AoP/Chapter02/ArrowProducts.agda): pair the sources and targets, then pair commuting squares. Both projections and uniqueness hold componentwise. |
| 2.30 | [PartialProduct](../src/AoP/Chapter02/PartialProduct.agda): construct the unique pairing of partial functions, accounting for inputs where only one function is defined. |
| 2.31 | [LazyPair](../src/AoP/Chapter02/LazyPair.agda): observing the outer constructor distinguishes two lazy pairs whose projections agree. |
| 2.32–2.33 | [ThreeOperations](../src/AoP/Chapter02/ThreeOperations.agda) encodes the three operations in one functor layer. [IdentityAlgebra](../src/AoP/Chapter02/IdentityAlgebra.agda) constructs the identity functor’s initial algebra on the empty type. [IdentityInitialObject](../src/AoP/Chapter02/IdentityInitialObject.agda) proves the general criterion: an initial object with identity as its operation is an initial identity-algebra. Conversely, the operation of any initial identity-algebra is itself an algebra endomorphism, so it equals identity by uniqueness. Maps to `(X,id)` then give the unique carrier maps to every `X`. |
| 2.34–2.36 | [FoldRetraction](../src/AoP/Chapter02/FoldRetraction.agda) constructs folds from sections, derives the sliding law, and represents any function from an initial carrier in `Fun` as the first projection of a fold. [AbstractFoldRetraction](../src/AoP/Chapter02/AbstractFoldRetraction.agda) gives the categorical proofs: undo the encoded children before constructing a new node, then reapply the encoding. Functoriality cancels the undo/encode pair. For 2.36 the pairing of the result with the original subtree supplies the section; the proof needs only the two projection equations. |
| 2.37 | [CantorDiagonal](../src/AoP/Chapter02/CantorDiagonal.agda) proves that no small carrier can encode all its subsets with membership-preserving decoding. This checks the diagonal obstruction; the predicates live a universe above their carrier, so this module does not exhibit a small powerset endofunctor. |
| 2.38 | [ConstantInitial](../src/AoP/Chapter02/ConstantInitial.agda) identifies the initial algebra for a constant layer and the sum functor for the two-parameter example. |
| 2.39 | [ParametricFold](../src/AoP/Chapter02/ParametricFold.agda) derives the naturality square for a change of parameter in `Fun`. [ParametricFoldSquare](../src/AoP/Chapter02/ParametricFoldSquare.agda) proves the square in any category given the two initial algebras and the algebra square for the result arrow `h`. Both paths fold into the same target: on one side fuse `h` with the source fold; on the other apply type functor fusion to the target fold after relabelling. [FoldTransformation](../src/AoP/Chapter02/FoldTransformation.agda) assembles these squares into the natural transformation `T ∘ G ⇒ H`, assuming the consumer algebra at each index commutes with each index arrow. |
| 2.40 | [FreeSubstitution](../src/AoP/Chapter02/FreeSubstitution.agda) and [FreeMonad](../src/AoP/Chapter02/FreeMonad.agda) derive the substitution and monad laws for an endofunctor on `Fun` with the required initial algebras. [TreeMonad](../src/AoP/Chapter02/TreeMonad.agda) checks the binary-tree instance. |

[← Chapter 1](chapter-one.md) · [Contents](../README.md#results-by-book-section) · [Chapter 3 →](chapter-three.md)
