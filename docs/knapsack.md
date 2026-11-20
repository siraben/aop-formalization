# Knapsack: deriving a maximum from the first table entry

Given a list of items, choose a subsequence whose weight fits the capacity and whose value is greatest. Each input position can be chosen once. The development uses natural weights, values and capacities, including zero. [Packing.Best](../src/AoP/Knapsack.agda) pairs a legal selection of original items with a proof that every legal competitor is worth at most as much. The reference solver tries both taking and skipping whenever taking is legal.

## Which partial packs can be discarded?

Write a partial pack as `(weight,value)`. At capacity 3, `(3,5)` is worth more than `(1,4)`. If the next item is `(2,3)`, however, the first pack must skip it, while the second can reach `(3,7)`. Keeping only the most valuable partial pack loses the optimum.

The safe comparison tests **both** coordinates. A pack can replace another when it weighs no more and is worth at least as much. Skipping preserves both inequalities. Taking adds the same item to both packs; if the heavier resulting pack fits, the lighter one fits too. [KnapsackGuardStep](../src/AoP/KnapsackGuardStep.agda) proves this continuation argument and checks the counterexample above.

## One fold step, calculated

Use input `[(2,3),(3,5),(1,4)]` at capacity 3. The fold starts at the right with `[(0,0)]`. Processing `(1,4)` adds `(1,4)` before the empty pack. Processing `(3,5)` cannot extend `(1,4)`, but can extend the empty pack, giving the table `[(3,5),(1,4),(0,0)]`. Now prepend `(2,3)`:

| Operation | Candidate summaries, in order |
| --- | --- |
| Add `(2,3)` to each entry | `(5,8), (3,7), (2,3)` |
| Keep extensions that fit | `(3,7), (2,3)` |
| Skip the item | `(3,5), (1,4), (0,0)` |
| Merge by descending value | `(3,7), (3,5), (1,4), (2,3), (0,0)` |
| Thin adjacent candidates | `(3,7), (1,4), (0,0)` |

Adding a common value preserves the take stream’s order; removing overweight packs also preserves it. [KnapsackSortedBranches](../src/AoP/KnapsackSortedBranches.agda) checks the take stream. [KnapsackMerge](../src/AoP/KnapsackMerge.agda) checks the merge and proves that membership is exactly membership in one of the streams. During [thinning](../src/AoP/KnapsackSortedTable.agda), `(1,4)` displaces `(2,3)` and `(3,7)` displaces `(3,5)`. Neither survivor can displace the weight-zero pack. The first entry now has value 7.

## Why the head solves the original problem

[KnapsackTableCoverage](../src/AoP/KnapsackTableCoverage.agda) proves two facts by induction: every survivor has a legal take/skip history, and every legal history has a survivor that is no heavier and no less valuable. Skipping every item supplies a history even at capacity zero. Coverage therefore rules out an empty table. Since thinning preserves the descending order, the [first entry](../src/AoP/KnapsackHead.agda) is worth at least as much as every survivor and hence every legal history.

[KnapsackPackBridge](../src/AoP/KnapsackPackBridge.agda) replays that entry’s decisions against the original items to produce `Packing.Best`, the same specification used by exhaustive search. A [second checked example](../src/AoP/KnapsackItemExample.agda) distinguishes two items with identical summaries: at capacity 4, `red` and `blue` weigh 2 and are worth 3 each. The solver returns both names, worth 6, ahead of a single heavy item worth 5. The certificate establishes feasibility and optimal value; the development gives no general running-time bound for these list tables.
