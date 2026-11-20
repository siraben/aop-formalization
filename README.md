# Algebra of Programming in Agda

A constructive formalization of selected results from Richard Bird and Oege de Moor’s *Algebra of Programming*. Start at [`Everything.agda`](src/Everything.agda). The book is not included.

| Book sections | Agda | Checked statements |
| --- | --- | --- |
| §§2.6, 3.1 | [Folds](src/AoP/Folds.agda) | List-fold uniqueness; fusion and banana-split derived from uniqueness |
| §§4.1, 4.4 | [Relations](src/AoP/Relations.agda) | Modular law and both implications of the universal property of right division |
| §5.5 | [Relations](src/AoP/Relations.agda) | Inductive relational fold for cons-lists |

`R : B ← A` takes the output first: `R b a` is evidence that `b` is a possible result for `a`. Thus `S ∘ R` runs `R` first. Inclusion `R ⊆ S` maps witnesses rather than comparing predicates by definitional equality. `⦅ e ∣ f ⦆` denotes the list catamorphism with base `e` and step `f`; Agda reserves `⦇ ⦈` for idiom brackets.

Run `nix flake check` to type-check all modules with `--safe --without-K`, or `nix develop` followed by `agda -i src src/Everything.agda` to work interactively. Only Agda builtins are required.

This is not a chapter-by-chapter transcription; in particular the recursive-program and optimization chapters (6–10) are not yet covered.
