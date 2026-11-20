# Thinning by connected blocks (exercise 8.14)

Given a finite list and a preorder `Q`, choose a partition into as few nonempty contiguous blocks as possible, subject to every two elements in each block being comparable. Return one least member of each block, in order. Every returned element must belong to the input, and every input element must have a returned representative below it under `Q`. Comparability must be decidable. An empty input returns no blocks and no representatives.

## Calculate a cut

Take `low ≤ left` and `low ≤ right`, with `left` and `right` incomparable. Scan `[left, low, right]`:

| After reading | Completed minima | Active block (input order) | Active minimum |
| --- | --- | --- | --- |
| `left` | `[]` | `[left]` | `left` |
| `low` | `[]` | `[left, low]` | `low` |
| `right` | `[low]` | `[right]` | `right` |

At the last letter, comparing `right` with the minimum `low` would admit it. Comparing with `left` rules it out. Closing the stream returns `[low, right]`. The incompatible endpoints rule out a one-block partition. [ConnectedPartitionTrace](../src/AoP/ConnectedPartitionTrace.agda) checks the two-block reference calculation; [ConnectedFusionTrace](../src/AoP/ConnectedFusionTrace.agda) checks the actual streaming states, whose active block is stored newest first.

## From the specification to the fold

1. **Choose the first block.** Connectedness survives deletion of elements, so once an extension fails, no longer prefix can qualify. [LongestConnectedBlock](../src/AoP/LongestConnectedBlock.agda) returns the longest connected prefix and the remaining input.
2. **Justify the greedy choice.** Compare with any rival partition. Its first block ends no later than the greedy block. Taking the extra letters removes whole rival blocks or shortens a connected block, so it never increases the number needed for the remainder. [ConnectedBlockExchange](../src/AoP/ConnectedBlockExchange.agda) proves this exchange; [ConnectedPartitionMinimum](../src/AoP/ConnectedPartitionMinimum.agda) iterates it using the all-singletons partition as an initial budget.
3. **Select representatives.** Within a connected block, compare the next member with the running minimum. Transitivity keeps the winner below everything already visited. [ConnectedPartitionThin](../src/AoP/ConnectedPartitionThin.agda) proves that one such minimum per block covers the entire input.
4. **Fuse selection with partitioning.** On extension, update the active block and its minimum. On rejection, save its minimum and begin a singleton block. [ConnectedPartitionFusion](../src/AoP/ConnectedPartitionFusion.agda) proves that projecting each completed block to its minimum commutes with both transitions; hence projecting after the fold gives the same result as saving just the minima during the fold.
5. **Connect the fold to the optimization problem.** [StreamingCutSequence](../src/AoP/StreamingCutSequence.agda) certifies each streaming cut and the final block. Its `agrees` theorem identifies all block boundaries with the minimum-count reference partition. [StreamingPartitionMinima](../src/AoP/StreamingPartitionMinima.agda) proves that the fused output contains a least member of each of those blocks in order. This allows ties without requiring independently selected minima to be equal.

## When one comparison decides extension

Suppose elements below a common upper bound are always comparable. Cache a greatest member `m` of the active block. If the newcomer is below `m`, then it and every old element are below `m` and hence comparable. If `m` is below the newcomer, transitivity places every old element below the newcomer. If the two are incomparable, `m` itself witnesses the failed extension. [ConnectedMaximum](../src/AoP/ConnectedMaximum.agda) checks the maximum update, and [ConnectedFastDecision](../src/AoP/ConnectedFastDecision.agda) proves the cached decision agrees with the full test. [CachedConnectedFold](../src/AoP/CachedConnectedFold.agda) gives the compact implementation: its active state stores the least and greatest members and evidence that the former is below the latter. A failed test saves the old least member; a new maximum leaves the minimum unchanged; otherwise the common-upper-bound comparison updates the minimum. One `test` call decides extension, with a call to the supplied common-upper-bound operation in the last case. [CachedConnectedTrace](../src/AoP/CachedConnectedTrace.agda) checks that after `[left, low]` the two cached values are `(low, left)` and that the rejected `right` yields `[low, right]`. [CachedBlockExtrema](../src/AoP/CachedBlockExtrema.agda) tracks the active block in the proof: on an extension, both cached extrema are members and bound every member; on a cut, the new singleton supplies both extrema. [CachedFoldSimulation](../src/AoP/CachedFoldSimulation.agda) proves the compact fold meets the same end-to-end specification. `Sync` pairs its active extrema with the full-test block and its saved representatives with the completed blocks. The two cut tests agree because the cached maximum belongs to the block and bounds every member. `certified` gives a least member for each optimal reference block in order, even when ties permit different choices.
