# Chapter 6: recursive programs

This inventory tracks the 37 numbered exercises in Chapter 6. The [sorting inventory](sorting-coverage.md) separately tracks the §6.6 algorithms and intermediate equations.

| Exercise | Construction and scope |
| --- | --- |
| 6.1 | Open: derive the decimal digit printer that divides by ten and accumulates remainders, including the singleton digit for zero. [DecimalInverse](../src/AoP/DecimalInverse.agda) proves inverse laws for a separate positive-number printer. |
| 6.2 | [FixedPoint](../src/AoP/FixedPoint.agda) isolates the use of local completeness: the collection of prefixpoints must have an infimum. The remainder of the proof uses its two order laws, transitivity, and monotonicity. |
| 6.3 | [Kleene](../src/AoP/Kleene.agda) constructs the ascending chain from the empty relation. Its union is a fixed point under the stated continuity assumption and lies below every prefixpoint. |
| 6.4 | [FixedPoint](../src/AoP/FixedPoint.agda) gives the prefixpoint bound. [Kleene](../src/AoP/Kleene.agda) proves fixed-point induction by bounding each finite approximation. |
| 6.5 | The two inequalities of the fixed-point equation are checked in [FixedPoint](../src/AoP/FixedPoint.agda). The categorical identification with Lambek’s lemma remains open. |
| 6.6 | [RelationalFusion](../src/AoP/RelationalFusion.agda) checks the two independent fusion implications for cons-list folds. The general recursion-operator derivation remains open. |
| 6.7 | [FoldComparison](../src/AoP/FoldComparison.agda) derives the general order argument from leastness of the first fold and the computation law of the second. [FoldReachability](../src/AoP/FoldReachability.agda) checks the cons-list case with a common base. A Boolean example starts at false; allowing one additional step on true leaves the fold results unchanged. |
| 6.8 | [DifunctionalClosure](../src/AoP/DifunctionalClosure.agda) builds finite derivations by completing rectangles. The proof establishes the fixed-point equation and leastness among all difunctional extensions. |

[BinaryOctal](../src/AoP/BinaryOctal.agda) checks exercise 6.9 in §6.3. Unfold a low-bit-first word into triples, padding the last group with zeroes, then fold each triple into one octal digit. The proof establishes preservation of numeric value for every input, including the empty word. The worked example converts `110101₂` to `65₈`, both denoting 53.

[SimpleHylo](../src/AoP/SimpleHylo.agda) checks the cons-list case of exercise 6.10. For a fixed input, two successful producer runs must emit the same list. A simple consumer then gives the same result on that list. Inputs with no finite run need no result. The general theorem for arbitrary initial types remains open.

[HalvingRun](../src/AoP/HalvingRun.agda) checks the common termination and uniqueness argument for exercise 6.11. Every positive argument decreases when halved. The computed result is independent of the supplied bound, satisfies the bit-step recurrence, and agrees with every solution of those equations. [HalvingDigits](../src/AoP/HalvingDigits.agda) proves that doubling the quotient and adding the low bit reconstructs the input. Any interpretation respecting that digit step therefore equals the halving program. [HalvingPower](../src/AoP/HalvingPower.agda) instantiates that proof for exponentiation by squaring. Splitting the exponent into two equal halves gives the square; an odd low bit adds one multiplication by the base. [ModulusBound](../src/AoP/ModulusBound.agda) proves the corresponding range invariant for positive divisor `b`: shifting a remainder below `b` gives a value below `2b`, so at most one subtraction restores the bound. [ModulusStep](../src/AoP/ModulusStep.agda) implements the update and accounts for the shifted value exactly: it equals either the new remainder or the divisor plus that remainder. [BinaryModulus](../src/AoP/BinaryModulus.agda) lifts that certificate through the entire halving recursion: each bit doubles the number of old divisor copies, and a subtraction contributes one additional copy. For every natural input `n` and positive divisor `b`, the returned `r` is below `b` and adding copies of `b` to `r` gives `n`. The checked example gives `53 mod 5 = 3`.

[AccessibleFixed](../src/AoP/AccessibleFixed.agda) proves both directions of exercise 6.12 for predicates. A state satisfies `Box X` when all its predecessors satisfy `X`. Accessibility induction puts every accessible state in every fixed predicate. Conversely, both accessibility and the full predicate are fixed, so uniqueness up to mutual inclusion makes every state accessible.

[AccessibleTransfer](../src/AoP/AccessibleTransfer.agda) proves exercise 6.13. If every two-step `R` path can be replaced by an `S` step followed by an `R` step with the same endpoint, well-foundedness of `S` implies well-foundedness of `R`. The induction at `x` establishes accessibility of every `R`-child of `x`.

[AccessibleExtremes](../src/AoP/AccessibleExtremes.agda) checks exercise 6.14. Every point is accessible for the empty relation. A self-edge rules out accessibility at that point, which handles identity and the universal relation on inhabited carriers. Every relation on an empty carrier is vacuously well-founded.

[AccessibleMeet](../src/AoP/AccessibleMeet.agda) checks exercise 6.15 for accessibility. Restricting a relation preserves accessibility, so a meet is well-founded if either factor is. On two vertices, each one-way edge alone is well-founded; their union admits an endless alternating path.

[AccessibilityMeasure](../src/AoP/AccessibilityMeasure.agda) proves exercise 6.16 for type-valued relations. Pulling a well-founded relation back along any function preserves accessibility: each recursive call descends to a predecessor of its measure. The measure may take the same value at distinct inputs.

[TreeMemberPath](../src/AoP/TreeMemberPath.agda) checks the two tree cases of exercise 6.17. Membership gives a path to a node carrying the sought label, and following such a path proves membership. A path ends at a tip in a tip-labelled tree; it may end at any fork in a fork-labelled tree. [ListMemberPath](../src/AoP/ListMemberPath.agda) checks the intermediate list equation `inlist = head ∘ tail*` in both directions: drop zero or more cells, then read the head of the resulting suffix. [MemberFold](../src/AoP/MemberFold.agda) derives list membership using the singleton and cons cases of the nonempty-list fold. For an inhabited element type, no ordinary relational cons-list fold directly returning an element can implement membership: a successful fold on a singleton needs a result on the empty tail, which has no members.

[ContainerEmpty](../src/AoP/ContainerEmpty.agda) checks a container case of exercise 6.21. If every value has a member, there are no values over the empty element type. Conversely, if each shape has decidably inhabited positions, emptiness over the empty element type implies that every value has a member. The general Boolean-allegory proof remains open.

Exercises 6.18–6.20 remain open: the equivalent formulation of the membership law, maximality of membership as a lax transformation, and the corresponding maximal transformation between two relators. See the [sorting inventory](sorting-coverage.md) for exercises 6.22–6.30.

### §6.7 Closure

| Exercise | Construction and scope |
| --- | --- |
| 6.31 | [Closure](../src/AoP/Closure.agda) proves the one-step fixed-point law, prefixpoint induction and least reflexive-transitive extension for finite paths. |
| 6.32 | Open: both least-fixed-point equations for composition with a closure. |
| 6.33 | [ClosureIterate](../src/AoP/ClosureIterate.agda) proves both directions using `once` and `again`. The identity fold reads the starting vertex; the relational fold takes one edge per `again`. |
| 6.34 | [ClosureChain](../src/AoP/ClosureChain.agda) represents paths by nonempty lists with the destination first. Its relational fold keeps both endpoints and checks each prepended edge. Reading the head of a chain recovers exactly the destinations reachable from its starting vertex. |
| 6.35 | Open: the rolling, diagonal and substitution rules of the μ-calculus. |
| 6.36 | Open: use the diagonal rule to derive closure of a union. |
| 6.37 | Open: specialize the union law to a coreflexive restriction. |

Unnumbered examples and intermediate derivations still need a full audit.
