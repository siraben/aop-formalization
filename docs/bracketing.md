# Finding the cheapest bracketing (§9.3, exercise 9.14)

Given a nonempty sequence of operands, choose parentheses without changing operand order. Each operand has a size summary. Combining two subtrees computes a new summary and adds a charge determined by the two child summaries. The [result certificate](../src/AoP/Chapter09/BracketFrontierMinimum.agda) gives a tree, an equality saying its leaves spell the input, and a proof that every tree spelling that input costs at least as much.

### Where the candidates come from

Read the input from right to left. A singleton has just one tree. To prepend `a` to `(b c)`, either make a new root `(a (b c))` or insert lower down, yielding `((a b) c)`. For a larger tree, the available positions are precisely its left spine. [Peeling](../src/AoP/Chapter09/BracketSpine.agda) recovers the first operand and an insertion witness from every compound tree. The [converse function theorem application](../src/AoP/Chapter09/FlattenConverseLaw.agda) uses this decomposition and the leaf equations to characterize all bracketings. [ConverseFlattenFold](../src/AoP/Chapter09/ConverseFlattenFold.agda) enumerates them.

### Why keeping the cheapest suffix fails

Take matrices `A : 1×2`, `B : 2×1`, `C : 1×2`, `D : 2×3`, counting scalar multiplications. The suffix `B(CD)` costs 12, while `(BC)D` costs 16. But prepending `A` can change the parentheses *inside* the suffix. The [checked insertion costs](../src/AoP/Chapter09/BracketPruneFailure.agda) are:

| Suffix | Possible costs after inserting `A` |
| --- | --- |
| `B(CD)` | 18, 11 |
| `(BC)D` | 22, 14, **10** |

Keeping just the cost-12 suffix would discard `((AB)C)D`: its three products cost `2 + 2 + 6 = 10`.

### What can safely be discarded

An insertion can enter the left child, but leaves each right subtree intact. Compare two trees for the same suffix by matching their left spines. Require equal size at the leftmost leaf and, at each matching fork, equal sizes and no greater cost on the right. These conditions imply no greater cost at the root. They also let the cheaper tree [match every insertion at the same depth](../src/AoP/Chapter09/BracketSpineDominance.agda), preserving the comparison for the next step.

When size equality is decidable, the [pruning pass](../src/AoP/Chapter09/PoolPruning.agda) can discard a candidate if a retained tree dominates it. The [fold](../src/AoP/Chapter09/BracketFrontier.agda) alternates insertion and pruning. Each retained tree is feasible, and [coverage](../src/AoP/Chapter09/BracketFrontierCoverage.agda) gives a retained competitor for every feasible tree. Selecting the cheapest survivor therefore gives a global minimum. In the [four-operand example](../src/AoP/Chapter09/BracketPoolExample.agda) all binary nodes cost one; pruning retains four trees out of five. This count illustrates the rule on one input. A general runtime bound remains unproved.
