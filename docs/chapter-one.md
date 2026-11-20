# Chapter 1: folds, inverses, and polymorphism

[Browse the Agda sources](../src/AoP/Chapter01) · [Type-check this chapter](../src/AoP/Chapter01/Index.agda)

Start with constructors: how many ways can a value be built? Then ask what a program should do in each constructor case. Those two questions lead from counting to folds (§§1.1–1.4). The last three sections use the resulting laws to invert programs, move maps through them, and simplify a filter.

## §1.1 Counting alternatives and pairs

[SmallDatatypes](../src/AoP/Chapter01/SmallDatatypes.agda) enumerates seven-bit ASCII, constructs the Boolean sum and product examples, checks their list lengths (130 and 256), and defines negation, switch, paired and curried conjunction, and optional values.

For a sum, first pick the tag: there are `128 + 2 = 130` ways to return a seven-bit character or a Boolean. For a product, pick both components: there are `128 × 2 = 256` pairs. The constructors explain which arithmetic operation to use.

## §1.2 Deriving a natural-number fold

For §1.2, [ArithmeticFolds](../src/AoP/Chapter01/ArithmeticFolds.agda) constructs addition, multiplication, and exponentiation by fixing their first argument. It also shows that the solutions of `f n ≡ f (suc n)` are exactly the constant functions. [Naturals](../src/AoP/Chapter01/Naturals.agda) covers fold uniqueness and the factorial and Fibonacci pair invariants.

**Calculate the factorial step.** A natural-number fold gets its previous result, but `fact (suc n)` also needs the index `n`. Ask the fold for both. Write `H n = (n, fact n)`. Then

```text
H 0       = (0, 1)                          by fact at zero
H (suc n) = (suc n, fact (suc n))          by the specification of H
          = (suc n, suc n * fact n)         by fact at successor
          = step (n, fact n)                where step (i,a) = (suc i, suc i * a)
          = step (H n)                      by the specification of H
```

The first and last lines supply the seed and recurrence. `foldn-unique` now identifies `H` pointwise with `foldn (0,1) step`; projecting the second field gives factorial. In the code, `factorial-invariant` checks the pair equation by induction.

## §1.3 Lists from either end

In §1.3, [SnocConcatTrace](../src/AoP/Chapter01/SnocConcatTrace.agda) calculates `[1,2,3] ++ [4,5]` using lists built from the rear. The recursion exposes `5` before `4`. The base case returns `[1,2,3]`; rebuilding appends `4` and then `5`, preserving their order. `read-back` checks the result against the ordinary cons-list `[1,2,3,4,5]`.

For §1.3, [DecimalPoint](../src/AoP/Chapter01/DecimalPoint.agda) evaluates the whole part with a snoc-list fold and the fractional part with a cons-list fold. The worked input `12.305` gives the exact ratio `12305/1000`. [NonemptyFolds](../src/AoP/Chapter01/NonemptyFolds.agda) derives `head` and shows why `foldr1` cannot change a singleton’s value. [Comprehension](../src/AoP/Chapter01/Comprehension.agda) proves that a guarded comprehension equals filtering followed by mapping; squaring the even numbers from 1 through 10 gives `[4,16,36,64,100]`.

## §1.4 Trees and forests

In §1.4, [RoseSizeTrace](../src/AoP/Chapter01/RoseSizeTrace.agda) counts the nodes of a tree with two children: a branch with one bud, and a leaf. The forest fold adds the child sizes `2 + 1`; the tree fold counts the root as well, giving `1 + (2 + 1) = 4`. Empty forests contribute zero.

For §1.4, [ForestList](../src/AoP/Chapter01/ForestList.agda) checks the numeric and character trees, proves forests and lists of rose trees are mutually convertible, and expresses the forest fold as a list fold.

## §1.5 When can a program be inverted?

For §1.5, [InverseDomains](../src/AoP/Chapter01/InverseDomains.agda) identifies the image of `unzip` with aligned pairs of lists. The same module shows why unrestricted decimal digit lists have no left-inverse printer: the empty sequence and a single zero evaluate to the same number.

## §1.6 Moving a map through a program

For §1.6, [PrefixEnumerationFold](../src/AoP/Chapter01/PrefixEnumerationFold.agda) constructs the prefix enumeration as a snoc-list fold. The last entry is always the entire input processed so far; extending that entry gives the next prefix. The worked three-item input yields `[], [a], [a,b], [a,b,c]`. [Naturality](../src/AoP/Chapter01/Naturality.agda) proves that mapping commutes with prefix enumeration, concatenation, reversal, and zip.

## §1.7 Calculating a filter

For §1.7, [FilterCalculation](../src/AoP/Chapter01/FilterCalculation.agda) derives ordinary filtering from tagging each item with its predicate result, selecting the true tags, and projecting their values. The steps name concat naturality, map composition, and the Boolean guard law. [FilterCombinators](../src/AoP/Chapter01/FilterCombinators.agda) checks the empty-list and singleton laws (1.3–1.5) and the general zip law (1.7): zipping two maps over the same input pairs their results element by element. [Conditions](../src/AoP/Chapter03/Conditions.agda) proves (1.10–1.11): preprocessing acts on the test and both branches; postprocessing acts on the branch results.

**Calculate the program.** Let `zs = zip xs (map p xs)`. For a tagged pair `z`, `keep z` returns `[z]` when the tag is true and `[]` otherwise. `pick z` uses the same test but returns `[fst z]` or `[]`. With these names, the Agda proof `Derivation.calculate` reads:

```text
map fst (filter snd zs)
= map fst (concat (map keep zs))             definition of filter
= concat (map (map fst) (map keep zs))       map through concat
= concat (map (λ z → map fst (keep z)) zs)   compose the two maps
= concat (map pick zs)                       check true and false separately
= concat (map pick (map (λ x → (x,p x)) xs)) zip a list with its predicate values
= concat (map (λ x → pick (x,p x)) xs)       compose the two maps
= filter p xs                                definition of filter
```

The guard step is where an element can disappear: for a false tag both sides give `[]`; for a true tag both give the singleton containing the original value. The other steps rearrange list traversals.

## Exercises

| Exercise | Construction or remaining work |
| --- | --- |
| 1.1 | [PositiveFold](../src/AoP/Chapter01/PositiveFold.agda): instantiating the proposed recursion at zero would give a natural equal to its successor. |
| 1.2 | [NestedSolutions](../src/AoP/Chapter01/NestedSolutions.agda) gives a family of solutions over naturals with truncated predecessor. In row zero every positive column can take the same arbitrary positive value. Two checked solutions give 1 and 2 at `(0,1)`, disproving uniqueness. |
| 1.3 | [PositiveFold](../src/AoP/Chapter01/PositiveFold.agda): iterate from one, convert between the two representations, and prove both round trips. |
| 1.4 | [SquareFold](../src/AoP/Chapter01/SquareFold.agda): maintain the side length and square area together. |
| 1.5 | [LastSatisfying](../src/AoP/Chapter01/LastSatisfying.agda): keep the greatest passing index in a growing interval. |
| 1.6 | [Naturals](../src/AoP/Chapter01/Naturals.agda): fold over rows of Ackermann's function and recover its three equations. |
| 1.7–1.8 | [Snoc](../src/AoP/Chapter01/Snoc.agda): `prepend` and `fromSnoc` implement conversion with a suffix accumulator. [ConversionFold](../src/AoP/Chapter01/ConversionFold.agda) derives the function-valued fold from singleton append and proves agreement with `prepend` for every suffix. [ConversionCost](../src/AoP/Chapter01/ConversionCost.agda) counts the cons cells allocated: `1 + … + n` for repeated append, `n` for the accumulator. |
| 1.9–1.10 | [Snoc](../src/AoP/Chapter01/Snoc.agda) proves the snoc append unit law; [Naturality](../src/AoP/Chapter01/Naturality.agda) defines curried cons-list append by a fold. The cons-list left unit holds by reduction. |
| 1.11–1.12 | [CountingFolds](../src/AoP/Chapter01/CountingFolds.agda): fold into a function awaiting an accumulator or count. Taking a prefix and dropping it produce pieces that append to the input. |
| 1.13–1.14 | [Trees](../src/AoP/Chapter01/Trees.agda) folds rose trees and proves both currying round trips. [CurriedExpression](../src/AoP/Chapter01/CurriedExpression.agda) checks the concrete seven-label expression and its depth. |
| 1.15 | [Inverses](../src/AoP/Chapter01/Inverses.agda): fold over the first list to obtain a function waiting for the second. [ZipInverseDomain](../src/AoP/Chapter01/ZipInverseDomain.agda) also proves necessity: every pair produced by `unzip` is aligned, so the truncating `zip` recovers both inputs exactly when their lengths agree. Zipping `[1,2]` with `[3]` yields `[(1,3)]`; unzipping it loses `2`. |
| 1.16 | [DecimalDigits](../src/AoP/Chapter01/DecimalDigits.agda): evaluate by a digit fold; `Printer` specifies the inverse by two laws. [DecimalSuccessor](../src/AoP/Chapter01/DecimalSuccessor.agda) implements printing by counting with carries and proves that evaluation recovers the positive input. [DecimalInverse](../src/AoP/Chapter01/DecimalInverse.agda) proves that every canonical numeral is reachable by successive increments, then uses that fact to recover the original digits after evaluation and printing. |
| 1.17 | [Naturality](../src/AoP/Chapter01/Naturality.agda): map commutes with concat, reverse, zip, and snoc-list prefix enumeration. |
| 1.18–1.19 | [NaturalShapes](../src/AoP/Chapter01/NaturalShapes.agda): relabelling laws for the proposed polymorphic functions. The first type has no total inhabitant; the second has a checked root-selection example. |

[Continue to Chapter 2: categories](chapter-two.md)
