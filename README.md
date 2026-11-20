# Algebra of Programming in Agda

A constructive formalization of selected results from Richard Bird and Oege de Moor’s *Algebra of Programming*. Start at [`Everything.agda`](src/Everything.agda). The book is not included.

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
| §2.5 | [Products](src/AoP/Products.agda) | Pairing and case analysis in Fun: uniqueness and fusion laws |
| §2.5 | [Polynomial](src/AoP/Polynomial.agda) | Interpret constants, identity, sums and products; functor laws; list roll/unroll isomorphism |
| §2.6 | [Initial](src/AoP/Initial.agda) | Algebras for an arbitrary endofunctor on Fun; derive reflection, fusion, and both directions of Lambek’s isomorphism from initiality |
| §§2.6, 3.1 | [Folds](src/AoP/Folds.agda) | List-fold uniqueness; fusion and banana-split derived from uniqueness |
| §3.2 | [Horner](src/AoP/Horner.agda) | Fuse a list reduction with a Ruby triangle, yielding Horner's one-pass rule |
| §§4.1, 4.4 | [Relations](src/AoP/Relations.agda) | Modular law and both implications of the universal property of right division |
| §5.5 | [Relations](src/AoP/Relations.agda), [Refinement](src/AoP/Refinement.agda) | Inductive relational fold; derive a deterministic implementation from branch refinements; filter refines subsequence selection |
| §6.2 | [FixedPoint](src/AoP/FixedPoint.agda) | Knaster–Tarski: the infimum of the prefixpoints is the least fixed point, up to mutual inequality |
| §§7.1, 8.1 | [Thinning](src/AoP/Thinning.agda) | Feasible minima, thinning as a preorder, and soundness and completeness of thin-introduction |

`R : B ← A` takes the output first: `R b a` is evidence that `b` is a possible result for `a`. Thus `S ∘ R` runs `R` first. Inclusion `R ⊆ S` maps witnesses rather than comparing predicates by definitional equality. `⦅ e ∣ f ⦆` denotes the list catamorphism with base `e` and step `f`; Agda reserves `⦇ ⦈` for idiom brackets.

**Reading the calculations.** Read the expressions down the left margin between `begin` and `∎`. A step `≡⟨ law ⟩` names its justification; `≡⟨⟩` means the neighbouring expressions agree by definition. Compare [snoc-list associativity](src/AoP/Snoc.agda) with §1.3, or [Horner promotion](src/AoP/Horner.agda) with §3.2. Prefer a chain for a derivation; keep `refl` or a named law when it already explains the whole step.

Run `nix flake check` to type-check all modules with `--safe --without-K`, or `nix develop` followed by `agda -i src src/Everything.agda` to work interactively. Only Agda builtins are required.

This is not a chapter-by-chapter transcription; in particular most recursive-program and optimization examples, and chapters 9–10, are not yet covered.
