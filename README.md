# Algebra of Programming in Agda

A constructive Agda companion to Richard Bird and Oege de Moor’s *Algebra of Programming*. The book is not included. To check the whole development, run `nix flake check`; [`Everything.agda`](src/Everything.agda) imports the proofs.

**Start with a worked problem.** In the [company-party example](src/AoP/PartyExample.agda), Ada supervises Bo and Cy. May Ada and Bo both attend? No. Should Ada attend? Not necessarily: the two reports together score more. Load the example to see the two checked guest lists, then follow [the general derivation](src/AoP/Party.agda) to see why comparing two plans per subtree suffices. For a smaller equational calculation, try [Horner’s rule](src/AoP/Horner.agda).

**Coverage.** The table lists checked results, not completed chapters. Some rows give the book’s general theorem, others a list instance, a reference solver, or only a specification. Those distinctions matter: proving optimality of an exhaustive solver does not verify the book’s faster algorithm.

| Book sections | Agda | Checked statements |
| --- | --- | --- |
| §1.2 | [Naturals](src/AoP/Naturals.agda) | Natural folds and uniqueness; factorial and Fibonacci pair invariants; higher-order fold for Ackermann |
| §1.3 | [Snoc](src/AoP/Snoc.agda) | Snoc-list fold and concatenation; accumulator conversions between cons- and snoc-lists, proved mutually inverse |
| §1.4 | [Trees](src/AoP/Trees.agda) | Binary and mutually recursive rose/forest folds; currying as application along the left spine |
| §1.5 | [Inverses](src/AoP/Inverses.agda) | Calculate a left inverse of unzip by a function-valued fold, and the opposite inverse on aligned lists |
| §1.6 | [Naturality](src/AoP/Naturality.agda) | Naturality of concat, reverse, zip and snoc-list prefixes |
| §1.7 | [PointFree](src/AoP/PointFree.agda) | Derive filtering by tagging with predicate results, selecting on the second component, and projecting the first |
| §2.1 | [Categories](src/AoP/Categories.agda) | Categories with an equivalence on arrows; instantiate the laws for functions using pointwise equality |
| §2.2 | [Functors](src/AoP/Functors.agda) | Functors between categories; list map preserves arrow equivalence, identity and composition |
| §2.3 | [Transformations](src/AoP/Transformations.agda) | Naturality squares, reversal on lists, and a calculation pasting two squares for vertical composition |
| §2.4 | [UniversalObjects](src/AoP/UniversalObjects.agda) | Initial and terminal objects, their fusion laws, and their empty-set and singleton instances in Fun |
| §2.5 | [Products](src/AoP/Products.agda) | Pairing and case analysis in Fun: uniqueness and fusion laws |
| §2.5 | [Polynomial](src/AoP/Polynomial.agda) | Interpret constants, identity, sums and products; functor laws; list roll/unroll isomorphism |
| §2.6 | [Initial](src/AoP/Initial.agda) | Algebras for an arbitrary endofunctor on Fun; derive reflection, fusion, and both directions of Lambek’s isomorphism from initiality |
| §§2.6–2.7 | [ListAlgebra](src/AoP/ListAlgebra.agda) | Instantiate the initial-algebra interface for cons-lists; obtain the map on labels as a catamorphism |
| §§2.6, 3.1 | [Folds](src/AoP/Folds.agda) | List-fold uniqueness; fusion and banana-split derived from uniqueness |
| §3.2 | [Horner](src/AoP/Horner.agda) | Fuse a list reduction with a Ruby triangle, yielding Horner's one-pass rule |
| §3.3 | [TeXFraction](src/AoP/TeXFraction.agda) | Integer decimal-to-fixed-point conversion; derive the fold given the floor/shift lemma |
| §3.4 | [Conditions](src/AoP/Conditions.agda) | Derive a conditional from distributivity and coproduct case analysis; verify branch equations and postcomposition |
| §3.5 | [Currying](src/AoP/Currying.agda) | Exponential universal property in Fun; curried list concatenation as a function-valued fold |
| §§4.1–4.2 | [Shunting](src/AoP/Shunting.agda) | Function graphs are entire and simple; calculate both implications of the left shunting rule |
| §4.3 | [Tabulation](src/AoP/Tabulation.agda) | Reconstruct a relation from its two columns; derive uniqueness of mediators for proposition-valued membership |
| §4.4 | [Joins](src/AoP/Joins.agda) | Universal properties of indexed joins and meets; composition distributes over joins on either side |
| §§4.1, 4.4 | [Relations](src/AoP/Relations.agda) | Modular law and both implications of the universal property of right division |
| §4.5 | [Complement](src/AoP/Complement.agda) | Order reversal, De Morgan’s law and division by negation; the classical direction takes double-negation stability explicitly |
| §4.6 | [Power](src/AoP/Power.agda) | Power transpose, fusion with a function, and existential image preserving identities and composition |
| §§5.1–5.2 | [RelationalProducts](src/AoP/RelationalProducts.agda) | Product of relations preserves inclusion, identity, converse, and composition |
| §5.3 | [RelationalSums](src/AoP/RelationalSums.agda) | Tag-preserving coproduct of relations; identity, composition, monotonicity and converse laws |
| §5.4 | [PowerRelator](src/AoP/PowerRelator.agda) | Two-sided coverage of subsets, extensional identity, converse, and factorization through a middle subset |
| §5.5 | [RelationalFusion](src/AoP/RelationalFusion.agda) | Derive the two fold-fusion inclusions independently from local simulations of nil and cons |
| §5.5 | [Relations](src/AoP/Relations.agda), [Refinement](src/AoP/Refinement.agda) | Inductive relational fold; derive a deterministic implementation from branch refinements; filter refines subsequence selection |
| §5.6 | [Subsequences](src/AoP/Subsequences.agda) | Enumerate subsequences by a fold; prove membership is equivalent to the skip/keep relational specification |
| §5.6 | [Splits](src/AoP/Splits.agda) | Enumerate the inverse of list concatenation, including cuts at either endpoint; prove soundness and completeness |
| §5.6 | [Permutations](src/AoP/Permutations.agda) | Enumerate all insertion positions and prove permutation enumeration sound and complete, including repeated elements |
| §5.7 | [LaxMembership](src/AoP/LaxMembership.agda) | Membership is lax natural for power lifting; the opposite inclusion holds for function graphs |
| §§6.1, 6.4 | [Binary](src/AoP/Binary.agda) | Binary carry, increment correctness, and evaluation as a left inverse of unary-to-binary encoding |
| §6.2 | [FixedPoint](src/AoP/FixedPoint.agda) | Knaster–Tarski: the infimum of the prefixpoints is the least fixed point, up to mutual inequality |
| §6.3 | [Hylo](src/AoP/Hylo.agda) | List hylomorphism as unfold followed by fold; prove both fixed-point inclusions and leastness |
| §6.4 | [Squaring](src/AoP/Squaring.agda) | Calculate exponentiation by squaring over binary digits using associativity and a left unit |
| §6.5 | [Inductive](src/AoP/Inductive.agda) | Accessibility of every recursive child makes the relational list hylomorphism the unique fixed point |
| §6.6 | [Selection](src/AoP/Selection.agda) | Select a least element from nonempty input, with evidence that exactly one occurrence was removed; [SelectionSort](src/AoP/SelectionSort.agda) iterates selection and proves sortedness and preservation of multiplicities |
| §6.7 | [Closure](src/AoP/Closure.agda) | Finite paths, closure induction, and the least preorder containing a relation |
| §7.2 | [MonotoneMinimum](src/AoP/MonotoneMinimum.agda) | A unary function preserves minima of direct images exactly when it is monotone; recover monotonicity using two-element sets |
| §7.2 | [GreedyFold](src/AoP/GreedyFold.agda) | Relational list-fold greedy theorem: matching steps from better tails makes every locally minimal run globally optimal |
| §7.3 | [Party](src/AoP/Party.agda), [worked example](src/AoP/PartyExample.agda) | Company-party planning on rose trees; compute a feasible maximum-score guest plan, tracking whether each supervisor attends |
| §7.4 | [Cylinder](src/AoP/Cylinder.agda) | Minimum-cost path from a given entry row, with up/stay/down moves; [CylinderEntry](src/AoP/CylinderEntry.agda) chooses the best start among a nonempty list of entry rows |
| §7.5 | [Reserves](src/AoP/Reserves.agda) | Model secure transaction blocks and prove they split at an intermediate balance; [SecureBlock](src/AoP/SecureBlock.agda) decides whether any starting reserve works. [VanSchedule](src/AoP/VanSchedule.agda) finds a feasible schedule with the fewest internal visits by exhaustive partition search; the book’s greedy implementation remains open |
| §§7.1, 8.1 | [Thinning](src/AoP/Thinning.agda) | Feasible minima, thinning as a preorder, and soundness and completeness of thin-introduction |
| §8.1 | [ThinningFold](src/AoP/ThinningFold.agda) | For a relational list fold, derive global coverage from local pruning and a step-matching condition |
| §8.2 | [LayeredPaths](src/AoP/LayeredPaths.agda) | Why a shortest-path table groups candidates by starting vertex; extending routes preserves that pruning invariant |
| §8.3 | [Bump](src/AoP/Bump.agda) | Implement thinning by comparing adjacent survivors; prove no candidates are invented and every discarded candidate is dominated |
| §8.4 | [Knapsack](src/AoP/Knapsack.agda) | Reference solver for 0–1 knapsack with capacity-indexed packs and a proof of maximum value; [KnapsackFrontier](src/AoP/KnapsackFrontier.agda) proves why pruning preserves optima, and [KnapsackSearch](src/AoP/KnapsackSearch.agda) verifies repeated pruning after each item (unsorted tables) |
| §8.5 | [Paragraph](src/AoP/Paragraph.agda) | Model nonempty lines and paragraphs, prove both line-break choices preserve word order, and define additive whitespace cost; [LineBreaks](src/AoP/LineBreaks.agda) enumerates all break patterns; [ParagraphMinimum](src/AoP/ParagraphMinimum.agda) returns a minimum-waste feasible layout or proves none fits (exhaustive reference solver) |
| §8.6 | [Bitonic](src/AoP/Bitonic.agda) | Choose outward or return legs for each interior city; prove minimum directed natural-number cost by exhaustive recurrence |
| §9.1 | [Bellman](src/AoP/Bellman.agda) | Unary-subproblem principle of optimality: branchwise monotone extension preserves the validity of replacing each child by a minimum |
| §9.2 | [EditScript](src/AoP/EditScript.agda) | Decode copy/delete/insert scripts to their endpoints; prove symmetry and feasibility of endpoint-indexed scripts; [EditMinimum](src/AoP/EditMinimum.agda) tabulates suffix pairs row by row, storing a shortest witness and its optimality proof in each cell |
| §9.3 | [Bracketing](src/AoP/Bracketing.agda) | Cost and size of expression trees; same-input subtree replacement, with a checked concatenation example |
| §9.4 | [Compression](src/AoP/Compression.agda) | Decode literals and overlapping backward references; prove literal encodings round-trip and reject an initial pointer |
| §10.1 | [Greedy](src/AoP/Greedy.agda) | Single-branch optimality from exchange and monotone extension, for unary decompositions |
| §10.2 | [Detab](src/AoP/Detab.agda) | Tab expansion at positive fixed width; derive the one-pass version by maintaining a column invariant; [TabFree](src/AoP/TabFree.agda) characterizes the image of expansion; [Entab](src/AoP/Entab.agda) proves buffered encoding round-trips on that image and [EntabMinimum](src/AoP/EntabMinimum.agda) proves shortestness against every competing encoding at any positive tab width |
| §10.3 | [Tardiness](src/AoP/Tardiness.agda) | Fuse elapsed time and maximum weighted tardiness into a single schedule evaluator; [check all six example schedules](src/AoP/TardinessExample.agda); [ScheduleSearch](src/AoP/ScheduleSearch.agda) proves an exhaustive scheduler optimal for arbitrary job lists; [BackwardSchedule](src/AoP/BackwardSchedule.agda) implements the backward-greedy algorithm and proves termination and permutation correctness; [BackwardOptimal](src/AoP/BackwardOptimal.agda) proves that it meets every penalty cap attainable by any permutation. [ScheduleCertificate](src/AoP/ScheduleCertificate.agda) checks it against the exhaustive solver’s specification; [BackwardExample](src/AoP/BackwardExample.agda) computes the optimal order |
| §10.4 | [TeXExternal](src/AoP/TeXExternal.agda) | Specify shortest round-tripping decimals; check the zero and half-unit cases (not the general printer) |

The [appendix list product](src/AoP/ListProduct.agda) enumerates one choice from each of a list of menus, with proofs of soundness and completeness.

`R : B ← A` takes the output first: `R b a` is evidence that `b` is a possible result for `a`. Thus `S ∘ R` runs `R` first. Inclusion `R ⊆ S` maps witnesses rather than comparing predicates by definitional equality. `⦅ e ∣ f ⦆` denotes the list catamorphism with base `e` and step `f`; Agda reserves `⦇ ⦈` for idiom brackets.

**Reading the calculations.** Read the expressions down the left margin between `begin` and `∎`. A step `≡⟨ law ⟩` names its justification; `≡⟨⟩` means the neighbouring expressions agree by definition. Compare [snoc-list associativity](src/AoP/Snoc.agda) with §1.3, or [Horner promotion](src/AoP/Horner.agda) with §3.2. Prefer a chain for a derivation; keep `refl` or a named law when it already explains the whole step.

Run `nix flake check` to type-check all modules with `--safe --without-K`, or `nix develop` followed by `agda -i src src/Everything.agda` to work interactively. Only Agda builtins are required.

Outstanding work includes the general dynamic-programming and greedy theorems, the quadratic bitonic-tour algorithm, optimal dictionary encoding and the general TeX printer. The table is not a claim that every exercise or derivation has been formalized.
