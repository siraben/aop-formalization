# Chapter 2: categories, functors, and transformations

This inventory covers the exercises in §§2.1–2.4. Later sections and the unnumbered examples still need an exercise-by-exercise and example-by-example audit.

| Exercise | Checked construction or remaining work |
| --- | --- |
| 2.1 | [Retractions](../src/AoP/Retractions.agda): applying the proposed right-unit law to the identity determines the arrow. |
| 2.2 | Open: check which composites in the diagram have matching endpoints. |
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
