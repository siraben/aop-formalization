# Why TeX needs the seventeenth decimal digit

The input is a finite list of digits representing a fraction `0.d₁…dₙ`. The output is a number of units of size `1/65536`, rounded to the nearest unit, with ties rounded upward. For example, the first midpoint is `1/131072 = .00000762939453125`. Removing its last digit changes the output from one unit to zero. [SixteenDigitsFail](../src/AoP/SixteenDigitsFail.agda) checks both outputs against the executable fold.

## From a digit to an integer update

[TeXFraction](../src/AoP/TeXFraction.agda) folds the digits from right to left. The empty suffix has state zero. Prepending digit `d` to a suffix in state `s` gives `⌊(131072d + s)/10⌋`. At the end, `halve` returns `⌊(s+1)/2⌋`. Keeping the extra binary digit until this last step matters: states 9 and 10 both round to 5, but prepending a zero gives states 0 and 1, which round differently.

[QuarterTrace](../src/AoP/QuarterTrace.agda) checks the calculation for `.25`. The state after processing the `5` is `65536`; after processing the `2`, it is `⌊(262144+65536)/10⌋ = 32768`. The final result is `16384` units, exactly one quarter.

## Why discarding a tail can work

Compare the state of the discarded suffix with zero. [TeXStateBound](../src/AoP/TeXStateBound.agda) proves both are below `131072`, so they agree on which multiples of `131072` they reach. The digit update does not have to make the states equal immediately. Instead, each retained digit reduces the spacing between the thresholds on which they agree.

Suppose that spacing is `2v` and divides `131072`. To reach `t·v` **after** division by ten, the numerator must reach `10·t·v = (5t)·(2v)` **before** division. This is an old threshold. Adding `131072d` to each state translates both by a whole number of old blocks. Hence the new states agree at spacing `v`. [DivisionThreshold](../src/AoP/DivisionThreshold.agda) verifies the threshold test for Agda’s integer division primitive; [DecimalGridStep](../src/AoP/DecimalGridStep.agda) combines it with translation for the actual digit update.

Starting at `2¹⁷`, seventeen halvings give spacing one. Two natural numbers that reach the same integer thresholds are equal: test each number as a threshold for the other. Applying `halve` then gives equal rounded outputs. For a complementary place-value calculation, [SeventeenGrid](../src/AoP/SeventeenGrid.agda) locates every midpoint on the `10⁻¹⁷` grid and [DecimalTailBound](../src/AoP/DecimalTailBound.agda) bounds the discarded fractional part strictly below one grid step.
