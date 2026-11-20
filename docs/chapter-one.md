# Chapter 1: folds, inverses, and polymorphism

The numbered exercises below link to their checked constructions. For the section-level examples, the [README](../README.md) links to the main developments. The unnumbered examples are being checked section by section. For §1.1, [SmallDatatypes](../src/AoP/SmallDatatypes.agda) enumerates seven-bit ASCII, constructs the Boolean sum and product examples, checks their list lengths (130 and 256), and defines negation, switch, paired and curried conjunction, and optional values.

For §1.2, [ArithmeticFolds](../src/AoP/ArithmeticFolds.agda) constructs addition, multiplication, and exponentiation by fixing their first argument. It also shows that the solutions of `f n ≡ f (suc n)` are exactly the constant functions. [Naturals](../src/AoP/Naturals.agda) covers fold uniqueness and the factorial and Fibonacci pair invariants.

| Exercise | Construction or remaining work |
| --- | --- |
| 1.1 | [PositiveFold](../src/AoP/PositiveFold.agda): instantiating the proposed recursion at zero would give a natural equal to its successor. |
| 1.2 | Open: determine whether the nested recursion fixes a unique function. |
| 1.3 | [PositiveFold](../src/AoP/PositiveFold.agda): iterate from one, convert between the two representations, and prove both round trips. |
| 1.4 | [SquareFold](../src/AoP/SquareFold.agda): maintain the side length and square area together. |
| 1.5 | [LastSatisfying](../src/AoP/LastSatisfying.agda): keep the greatest passing index in a growing interval. |
| 1.6 | [Naturals](../src/AoP/Naturals.agda): fold over rows of Ackermann's function and recover its three equations. |
| 1.7–1.8 | [Snoc](../src/AoP/Snoc.agda): `prepend` and `fromSnoc` implement conversion with a suffix accumulator. [ConversionFold](../src/AoP/ConversionFold.agda) derives the function-valued fold from singleton append and proves agreement with `prepend` for every suffix. [ConversionCost](../src/AoP/ConversionCost.agda) counts the cons cells allocated: `1 + … + n` for repeated append, `n` for the accumulator. |
| 1.9–1.10 | [Snoc](../src/AoP/Snoc.agda) proves the snoc append unit law; [Naturality](../src/AoP/Naturality.agda) defines curried cons-list append by a fold. The cons-list left unit holds by reduction. |
| 1.11–1.12 | [CountingFolds](../src/AoP/CountingFolds.agda): fold into a function awaiting an accumulator or count. Taking a prefix and dropping it produce pieces that append to the input. |
| 1.13–1.14 | [Trees](../src/AoP/Trees.agda) folds rose trees and proves both currying round trips. [CurriedExpression](../src/AoP/CurriedExpression.agda) checks the concrete seven-label expression and its depth. |
| 1.15 | [Inverses](../src/AoP/Inverses.agda): fold over the first list to obtain a function waiting for the second. The reverse zip/unzip law uses aligned lengths. |
| 1.16 | [DecimalDigits](../src/AoP/DecimalDigits.agda): evaluate by a digit fold; `Printer` specifies the inverse by two laws. [DecimalSuccessor](../src/AoP/DecimalSuccessor.agda) implements printing by counting with carries and proves that evaluation recovers the positive input. [DecimalInverse](../src/AoP/DecimalInverse.agda) proves that every canonical numeral is reachable by successive increments, then uses that fact to recover the original digits after evaluation and printing. |
| 1.17 | [Naturality](../src/AoP/Naturality.agda): map commutes with concat, reverse, zip, and snoc-list prefix enumeration. |
| 1.18–1.19 | [NaturalShapes](../src/AoP/NaturalShapes.agda): relabelling laws for the proposed polymorphic functions. The first type has no total inhabitant; the second has a checked root-selection example. |
