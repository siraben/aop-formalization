# Algebra of Programming in Agda

Agda formalization of definitions, calculations, and programs from Richard Bird and Oege de Moor’s *Algebra of Programming*.

Run `nix flake check` to type-check [`Everything.agda`](src/Everything.agda), which imports all modules. For interactive work, run `nix develop` and open a `.agda` file in your editor. The proofs use Agda builtins with `--safe --without-K`.

In the [company-party example](src/AoP/PartyExample.agda), a supervisor and a direct report cannot both attend. Ada scores 8; her reports Bo and Cy score 5 each. The best guest list is `[Bo, Cy]`, or `[Ada]` if the president must attend. The [proof](src/AoP/Party.agda) calculates the best plan for each subtree under both choices for its supervisor.

## Results by book section

Exercise inventories: [Chapter 1](docs/chapter-one.md) · [Chapter 2](docs/chapter-two.md) · [Chapter 3](docs/chapter-three.md) · [Chapter 4](docs/chapter-four.md) · [Chapter 5](docs/chapter-five.md) · [Chapter 6](docs/chapter-six.md) · [Chapter 7](docs/chapter-seven.md) · [Chapter 8](docs/chapter-eight.md) · [Chapter 9](docs/chapter-nine.md) · [Chapter 10](docs/chapter-ten.md) · [§6.6 sorting](docs/sorting-coverage.md).

| Book sections | Agda | Checked statements |
| --- | --- | --- |
| §1.2 | [Naturals](src/AoP/Naturals.agda) | Natural folds and uniqueness; factorial and Fibonacci pair invariants; higher-order fold for Ackermann; [PositiveFold](src/AoP/PositiveFold.agda) gives an unsatisfiable recursion equation and the positive-number fold isomorphism; [SquareFold](src/AoP/SquareFold.agda) derives squaring by repeated addition; [LastSatisfying](src/AoP/LastSatisfying.agda) finds the greatest index passing a Boolean test |
| §1.3 | [Snoc](src/AoP/Snoc.agda) | Snoc-list fold and concatenation; accumulator conversions between cons- and snoc-lists, proved mutually inverse; [CountingFolds](src/AoP/CountingFolds.agda) expresses left iteration, take, and drop as right folds |
| §1.4 | [Trees](src/AoP/Trees.agda) | Binary and mutually recursive rose/forest folds; currying as application along the left spine. [CurriedExpression](src/AoP/CurriedExpression.agda) checks both representations of `f(g(a,b),h(c),d)`, its size, and its depth |
| §1.5 | [Inverses](src/AoP/Inverses.agda) | Calculate a left inverse of unzip by a function-valued fold, and the opposite inverse on aligned lists; [DecimalDigits](src/AoP/DecimalDigits.agda) evaluates numerals without leading zeros and specifies the inverse printer |
| §1.6 | [Naturality](src/AoP/Naturality.agda) | Naturality of concat, reverse, zip and snoc-list prefixes; [NaturalShapes](src/AoP/NaturalShapes.agda) gives the relabelling laws for exercises 1.18–1.19 and checks the empty-input obstruction in 1.18 |
| §1.7 | [PointFree](src/AoP/PointFree.agda) | Derive filtering by tagging with predicate results, selecting on the second component, and projecting the first |
| §2.1 | [Categories](src/AoP/Categories.agda) | Categories with an equivalence on arrows; instantiate the laws for functions using pointwise equality. [Retractions](src/AoP/Retractions.agda) proves uniqueness of identity and the dual factorization laws for a section and retraction; [Cancellation](src/AoP/Cancellation.agda) proves the monic and epic cancellation laws. [PreorderCategory](src/AoP/PreorderCategory.agda) gives an arrow that is both monic and epic and has no inverse |
| §2.2 | [Functors](src/AoP/Functors.agda) | List map and [binary tree map](src/AoP/TreeFunctor.agda) preserve arrow equivalence, identity and composition. [FunctorIso](src/AoP/FunctorIso.agda) shows how mapping an inverse gives an inverse of the mapped arrow; [PreorderFunctor](src/AoP/PreorderFunctor.agda) identifies functors between preorders with monotone maps. [UniversalImage](src/AoP/UniversalImage.agda) checks identity and composition for the universal image and distinguishes it from the ordinary image |
| §2.3 | [Transformations](src/AoP/Transformations.agda) | Naturality squares, reversal on lists, and a calculation pasting two squares for vertical composition. [SingletonImage](src/AoP/SingletonImage.agda) proves singleton naturality for direct image and gives a counterexample for universal image |
| §2.4 | [UniversalObjects](src/AoP/UniversalObjects.agda) | Initial and terminal objects, their fusion laws, and their empty-set and singleton instances in Fun |
| §2.5 | [Products](src/AoP/Products.agda) | Pairing and case analysis in Fun: uniqueness and fusion laws |
| §2.5 | [Polynomial](src/AoP/Polynomial.agda) | Interpret constants, identity, sums and products; functor laws; list roll/unroll isomorphism |
| §2.6 | [Initial](src/AoP/Initial.agda) | Algebras for an arbitrary endofunctor on Fun; derive reflection, fusion, and both directions of Lambek’s isomorphism from initiality |
| §§2.6–2.7 | [ListAlgebra](src/AoP/ListAlgebra.agda) | Instantiate the initial-algebra interface for cons-lists; obtain the map on labels as a catamorphism |
| §§2.6, 3.1 | [Folds](src/AoP/Folds.agda) | List-fold uniqueness; fusion and banana-split derived from uniqueness. [Average](src/AoP/Average.agda) computes the sum and length in one traversal. [Steep](src/AoP/Steep.agda) tests whether each entry exceeds the sum of the following entries in one list traversal |
| §3.2 | [Horner](src/AoP/Horner.agda) | Fuse a list reduction with a Ruby triangle, yielding Horner's one-pass rule. [TipDepths](src/AoP/TipDepths.agda) derives the maximum tree depth without constructing the depth-labelled intermediate tree |
| §3.3 | [TeXFraction](src/AoP/TeXFraction.agda) | Integer decimal-to-fixed-point conversion; derive the fold given the floor/shift lemma |
| §3.4 | [Conditions](src/AoP/Conditions.agda) | Derive a conditional from distributivity and coproduct case analysis; verify branch equations and postcomposition |
| §3.5 | [Currying](src/AoP/Currying.agda) | Exponential universal property in Fun; curried list concatenation as a function-valued fold. [TipTraversal](src/AoP/TipTraversal.agda) derives left-to-right tip traversal by composing suffix functions at each fork |
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
| §6.2 | [FixedPoint](src/AoP/FixedPoint.agda) | Knaster–Tarski: the infimum of the prefixpoints is the least fixed point, up to mutual inequality. [DifunctionalClosure](src/AoP/DifunctionalClosure.agda) constructs the least extension closed under completing three-edge rectangles. [FoldReachability](src/AoP/FoldReachability.agda) proves a list-fold bound by checking only reachable tail states (exercise 6.7) |
| Exercises 6.3–6.4 | [Kleene](src/AoP/Kleene.agda) | Construct the least fixed point of a continuous operator as the union of its finite approximations. Prove a bound on the union by showing each step preserves the bound |
| §6.3 | [Hylo](src/AoP/Hylo.agda) | List hylomorphism as unfold followed by fold; prove both fixed-point inclusions and leastness |
| §6.4 | [Squaring](src/AoP/Squaring.agda) | Calculate exponentiation by squaring over binary digits using associativity and a left unit |
| §6.5 | [Inductive](src/AoP/Inductive.agda) | Accessibility of every recursive child makes the relational list hylomorphism the unique fixed point |
| §6.6 | [Selection](src/AoP/Selection.agda) | Select a least element from nonempty input, with evidence that exactly one occurrence was removed; [SelectionSort](src/AoP/SelectionSort.agda) iterates selection and proves sortedness and preservation of multiplicities. [Quicksort](src/AoP/Quicksort.agda) splits around a pivot, unfolds a tree and flattens it in order. [Derivations and exercises](docs/sorting-coverage.md) |
| §6.7 | [Closure](src/AoP/Closure.agda) | Finite paths, closure induction, and the least preorder containing a relation |
| §7.2 | [MonotoneMinimum](src/AoP/MonotoneMinimum.agda) | A unary function preserves minima of direct images exactly when it is monotone; recover monotonicity using two-element sets |
| §7.2 | [GreedyFold](src/AoP/GreedyFold.agda) | Relational list-fold greedy theorem: matching steps from better tails makes every locally minimal run globally optimal |
| §7.3 | [Party](src/AoP/Party.agda), [worked example](src/AoP/PartyExample.agda) | Company-party planning on rose trees; compute a feasible maximum-score guest plan, tracking whether each supervisor attends |
| §7.4 | [Cylinder](src/AoP/Cylinder.agda) | Minimum-cost path from a given entry row, with up/stay/down moves; [CylinderEntry](src/AoP/CylinderEntry.agda) chooses the best start among a nonempty list of entry rows |
| §7.5 | [Reserves](src/AoP/Reserves.agda) | Model secure transaction blocks and prove they split at an intermediate balance; [SecureBlock](src/AoP/SecureBlock.agda) decides whether any starting reserve works. [VanSchedule](src/AoP/VanSchedule.agda) finds a feasible schedule with the fewest internal visits by exhaustive partition search; [VanRefinement](src/AoP/VanRefinement.agda) meets the same minimum-visit specification by repeatedly taking the longest secure prefix. [VanFold](src/AoP/VanFold.agda) checks feasibility of the book’s right-to-left construction using the reserve-search test. [CachedVan](src/AoP/CachedVan.agda) updates the first block’s stock and headroom requirements at each gap; [VaultCapacity](src/AoP/VaultCapacity.agda) proves their sum is the minimum required capacity. [CachedVanOptimal](src/AoP/CachedVanOptimal.agda) certifies that this right-to-left scheduler minimizes internal visits on every nonempty serviceable stream |
| §§7.1, 8.1 | [Thinning](src/AoP/Thinning.agda) | Feasible minima, thinning as a preorder, and soundness and completeness of thin-introduction |
| §8.1 | [ThinningFold](src/AoP/ThinningFold.agda) | For a relational list fold, derive global coverage from local pruning and a step-matching condition |
| §8.2 | [LayeredPaths](src/AoP/LayeredPaths.agda) | Why a shortest-path table groups candidates by starting vertex; extending routes preserves that pruning invariant |
| 8.14 | [Connected thinning derivation](docs/connected-thinning.md) | Derive the minimum-block partition, fuse selection of block minima, and check the streaming cut on three elements |
| §8.3 | [Bump](src/AoP/Bump.agda) | Implement thinning by comparing adjacent survivors; prove no candidates are invented and every discarded candidate is dominated |
| §8.4 | [Knapsack](src/AoP/Knapsack.agda) | The [worked knapsack derivation](docs/knapsack.md) traces taking, skipping, merging, and thinning candidate packs. [KnapsackPackBridge](src/AoP/KnapsackPackBridge.agda) returns original items and proves the same maximum-value specification as exhaustive search for natural weights and values. |
| §8.5 | [Paragraph](src/AoP/Paragraph.agda) | Model nonempty lines and paragraphs, prove both line-break choices preserve word order, and define additive whitespace cost; [LineBreaks](src/AoP/LineBreaks.agda) enumerates all break patterns; [ParagraphMinimum](src/AoP/ParagraphMinimum.agda) returns a minimum-waste feasible layout or proves none fits (exhaustive reference solver) |
| §8.6 | [Bitonic](src/AoP/Bitonic.agda) | Choose outward or return legs for each interior city; [BitonicTable](src/AoP/BitonicTable.agda) computes a minimum-cost directed tour using a triangular table of endpoint pairs; [four-stop example](src/AoP/BitonicExample.agda) |
| §9.1 | [Bellman](src/AoP/Bellman.agda) | Unary-subproblem principle of optimality: branchwise monotone extension preserves the validity of replacing each child by a minimum |
| §9.1 | [BranchingDP](src/AoP/BranchingDP.agda) | Bellman optimality for shape-indexed subproblems with attainable child minima and a monotone cost algebra |
| §9.2 | [EditScript](src/AoP/EditScript.agda) | Decode copy/delete/insert scripts to their endpoints; prove symmetry and feasibility of endpoint-indexed scripts; [EditMinimum](src/AoP/EditMinimum.agda) tabulates suffix pairs row by row, storing a shortest witness and its optimality proof in each cell |
| §9.3 | [Bracketing](src/AoP/Bracketing.agda) | Cost and size of expression trees; same-input subtree replacement; [BracketMinimum](src/AoP/BracketMinimum.agda) finds a least-cost bracketing by exhaustive enumeration; [AppendOptimal](src/AoP/AppendOptimal.agda) proves right association minimizes list-append cost; the [thinning derivation](docs/bracketing.md) explains the certified solver and a matrix-chain counterexample to cheapest-suffix pruning |
| §9.4 | [Compression](src/AoP/Compression.agda) | Decode literals and overlapping backward references; prove literal encodings round-trip; [DictionarySearch](src/AoP/DictionarySearch.agda) computes a minimum-cost encoding by bounded exhaustive search |
| §10.1 | [Greedy](src/AoP/Greedy.agda) | Single-branch optimality from exchange and monotone extension, for unary decompositions |
| §10.1 | [BranchingGreedy](src/AoP/BranchingGreedy.agda) | Prove global optimality of recursive branch selection from an exchange witness and a monotone cost algebra |
| §10.2 | [Detab](src/AoP/Detab.agda) | Tab expansion at positive fixed width; derive the one-pass version by maintaining a column invariant; [TabFree](src/AoP/TabFree.agda) characterizes the image of expansion; [Entab](src/AoP/Entab.agda) proves buffered encoding round-trips on that image and [EntabMinimum](src/AoP/EntabMinimum.agda) proves shortestness against every competing encoding at any positive tab width |
| §10.3 | [Tardiness](src/AoP/Tardiness.agda) | Fuse elapsed time and maximum weighted tardiness into a single schedule evaluator; [check all six example schedules](src/AoP/TardinessExample.agda); [ScheduleSearch](src/AoP/ScheduleSearch.agda) proves an exhaustive scheduler optimal for arbitrary job lists; [BackwardSchedule](src/AoP/BackwardSchedule.agda) implements the backward-greedy algorithm and proves termination and permutation correctness; [BackwardOptimal](src/AoP/BackwardOptimal.agda) proves that it meets every penalty cap attainable by any permutation. [ScheduleCertificate](src/AoP/ScheduleCertificate.agda) checks it against the exhaustive solver’s specification; [BackwardExample](src/AoP/BackwardExample.agda) computes the optimal order. The [scheduling guide](docs/scheduling.md) works through the last-job calculation, equal weights, and signed lateness |
| §10.4 | [TeXExternal](src/AoP/TeXExternal.agda) | [Two-pass integer printer](src/AoP/TeXBoundedPrinter.agda) returns a shortest round-tripping decimal for every TeX target; [worked derivation](docs/tex-rounding.md) |

The [appendix list product](src/AoP/ListProduct.agda) enumerates one choice from each of a list of menus, with proofs of soundness and completeness.

## Notation

- `R : B ← A` relates an input `a` to a possible output `b`, written `R b a`. Composition `S ∘ R` applies `R` first.
- `R ⊆ S` sends each witness of `R b a` to a witness of `S b a`.
- `⦅ e ∣ f ⦆` is the list fold with base `e` and step `f`.
- Between `begin` and `∎`, each `≡⟨ law ⟩` cites the law for that step; `≡⟨⟩` uses definitional equality. See [snoc-list associativity](src/AoP/Snoc.agda) and [Horner’s rule](src/AoP/Horner.agda).

## Open work

The [dictionary encoder guide](docs/dictionary.md) derives the minimum-cost prefix table and its longest-pointer refinement. [Chapter 9](docs/chapter-nine.md) records the relational hypotheses for the dynamic-programming theorem. Exercise 9.20’s [alternative thinning fold](src/AoP/DictionaryStateMinimum.agda) groups partial encodings by their ability to extend the final pointer. [GreedyHyloCriterion](src/AoP/GreedyHyloCriterion.agda) derives the greedy optimality test for concrete relations from feasibility and the hylomorphism laws. [TeXPrinterAgreement](src/AoP/TeXPrinterAgreement.agda) proves the single-loop and two-pass printers return identical digits for every TeX target. The chapter inventories identify remaining abstract derivations and worked examples.
