# Chapter 2: categories, functors, and transformations

This inventory covers the 40 numbered exercises in Chapter 2. The unnumbered examples still need a separate audit.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 2.1 | [Retractions](../src/AoP/Retractions.agda): applying the proposed right-unit law to the identity determines the arrow. |
| 2.2 | [ArrowEndpoints](../src/AoP/ArrowEndpoints.agda) types `k ∘ h ∘ f ∘ h` along the path `A → B → A → B → C`. For `g ∘ k ∘ h`, the output of `k` is `C` but the input of `g` is `A`; the mismatch is proved for the distinct node labels. |
| 2.3 | [Retractions](../src/AoP/Retractions.agda): use a chosen section to factor through its retraction, and prove the dual extension law. |
| 2.4–2.5 | [Cancellation](../src/AoP/Cancellation.agda): cancel a section on the left and a retraction on the right. If a composite is epic, its outer arrow is epic; if monic, its inner arrow is monic. |
| 2.6 | [PreorderCategory](../src/AoP/PreorderCategory.agda): every arrow cancels in both directions. On naturals, `1 → 0` has no return arrow. |
| 2.7 | [RelEpic](../src/AoP/RelEpic.agda): a shared input can hit two outputs without distinguishing them. Adding a private input for each output yields an epic relation that still has a multivalued input. |
| 2.8 | [ArrowCategory](../src/AoP/ArrowCategory.agda) constructs the arrow category by pasting commuting squares and proves that a square with two monic components is monic. [SquareMonic](../src/AoP/SquareMonic.agda) proves the top component must be monic by testing against identity arrows. If the base category has an initial object, the bottom component must also be monic, giving an exact componentwise criterion in that case. |
| 2.9–2.10 | [FunctorIso](../src/AoP/FunctorIso.agda) maps both inverse equations. [PreorderFunctor](../src/AoP/PreorderFunctor.agda) constructs a functor from a monotone map and reads monotonicity back from its action on arrows. |
| 2.11 | [HomAction](../src/AoP/HomAction.agda): precompose at the source and postcompose at the target. The proofs check identity, composition, and congruence on all three arrows. |
| 2.12 | [TreeFunctor](../src/AoP/TreeFunctor.agda): the tip mapping of §1.4 gives an endofunctor on functions. |
| 2.13 | [UniversalImage](../src/AoP/UniversalImage.agda): universal direct image preserves identity and composition. A missing preimage distinguishes it from ordinary direct image. |
| 2.14 | [SwapNatural](../src/AoP/SwapNatural.agda): construct both product functors, the swap transformation, and its inverse. |
| 2.15 | [SingletonImage](../src/AoP/SingletonImage.agda): prove singleton naturality for direct image; refute it for universal image. |
| 2.16 | [ProductNaturality](../src/AoP/ProductNaturality.agda): choosing one element per set commutes with taking direct images. The reverse inclusion collects a preimage for each choice. |
| 2.17 | [Whiskering](../src/AoP/Whiskering.agda): precompose a transformation with a functor and reuse the original square on each mapped arrow. |
| 2.18 | [PartialHead](../src/AoP/PartialHead.agda): a defined head and an undefined tail distinguish the two sides of the proposed naturality square. |
| 2.19 | [FunctorCategory](../src/AoP/FunctorCategory.agda) verifies the category laws componentwise. [WalkingArrow](../src/AoP/WalkingArrow.agda) converts between transformations and squares for two-object diagrams. [DiagramEvaluation](../src/AoP/DiagramEvaluation.agda) evaluates diagrams at the generating arrow and proves this functor is full, faithful, and surjective on objects. [ArrowDiagram](../src/AoP/ArrowDiagram.agda) constructs the reverse functor and proves that constructing a diagram and evaluating it recovers each arrow and square. [DiagramRoundTrip](../src/AoP/DiagramRoundTrip.agda) constructs inverse transformations between each original and rebuilt diagram, and proves the comparison is natural in the diagram. |
| 2.20 | [ConstantArrow](../src/AoP/ConstantArrow.agda): choosing an element of the source factors a constant arrow through the terminal object. |
| 2.21 | Open: classify empty objects in the three categories. |
| 2.22 | [TerminalDiagrams](../src/AoP/TerminalDiagrams.agda): in the book’s preorder orientation, a terminal object is a least element. |
| 2.23 | [ProductCategory](../src/AoP/ProductCategory.agda): construct the product category and pair initial or terminal objects componentwise. |
| 2.24 | [TerminalDiagrams](../src/AoP/TerminalDiagrams.agda): the constant diagram at the target’s terminal object is terminal in the functor category. |
| 2.25 | [OrderProducts](../src/AoP/OrderProducts.agda): maximum and minimum satisfy the product and coproduct bounds in the natural-number preorder. |
| 2.26 | [ProductUnit](../src/AoP/ProductUnit.agda), [ProductSymmetry](../src/AoP/ProductSymmetry.agda), and [ProductAssociator](../src/AoP/ProductAssociator.agda) derive the inverse and naturality laws from product projections. |
| 2.27 | [ExchangeLaw](../src/AoP/ExchangeLaw.agda): pairing commutes with case analysis by product and coproduct uniqueness. |
| 2.28 | [ProjectionEpic](../src/AoP/ProjectionEpic.agda): injections are monic; projections can fail to be epic with an empty factor. |
| 2.29 | [ArrowProducts](../src/AoP/ArrowProducts.agda): pair the sources and targets, then pair commuting squares. Both projections and uniqueness hold componentwise. |
| 2.30 | [PartialProduct](../src/AoP/PartialProduct.agda): construct the unique pairing of partial functions, accounting for inputs where only one function is defined. |
| 2.31 | [LazyPair](../src/AoP/LazyPair.agda): observing the outer constructor distinguishes two lazy pairs whose projections agree. |
| 2.32–2.33 | [ThreeOperations](../src/AoP/ThreeOperations.agda) encodes the three operations in one functor layer. [IdentityAlgebra](../src/AoP/IdentityAlgebra.agda) constructs the identity functor’s initial algebra on the empty type. |
| 2.34–2.36 | [FoldRetraction](../src/AoP/FoldRetraction.agda) constructs folds from sections, derives the sliding law, and represents any function from an initial carrier in `Fun` as the first projection of a fold. |
| 2.37 | [CantorDiagonal](../src/AoP/CantorDiagonal.agda) proves that no small carrier can encode all its subsets with membership-preserving decoding. This checks the diagonal obstruction; the predicates live a universe above their carrier, so this module does not exhibit a small powerset endofunctor. |
| 2.38 | [ConstantInitial](../src/AoP/ConstantInitial.agda) identifies the initial algebra for a constant layer and the sum functor for the two-parameter example. |
| 2.39 | [ParametricFold](../src/AoP/ParametricFold.agda) derives the naturality square for a change of parameter in `Fun` by two applications of fold fusion. |
| 2.40 | [FreeSubstitution](../src/AoP/FreeSubstitution.agda) and [FreeMonad](../src/AoP/FreeMonad.agda) derive the substitution and monad laws for an endofunctor on `Fun` with the required initial algebras. [TreeMonad](../src/AoP/TreeMonad.agda) checks the binary-tree instance. |
