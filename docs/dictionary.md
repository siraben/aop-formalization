# A minimum-cost dictionary encoder (§9.4)

Given a target text, produce instructions that reconstruct it from left to right. A literal appends one letter for cost `c`; a pointer costs `p` and copies from an absolute position in the text decoded so far. The copy can read letters it has just written. In Agda `ptr i k` copies **`k + 1` letters**, so even the shortest pointer advances the decoder. A read outside the current text fails. See [the decoder](../src/AoP/Chapter09/Compression.agda).

## Calculate one row

For target `aaaa`, let `c = 2` and `p = 3`. Store an encoding at each prefix. For the next row, append the last letter literally to the preceding row, or use a pointer ending at this prefix. Among pointers it suffices to consider a longest copy.

| Prefix | Literal extension | Longest pointer extension | Minimum cost |
| --- | ---: | --- | ---: |
| empty | — | — | 0 |
| `a` | 0 + 2 | none: the decoder has no source letter | 2 |
| `aa` | 2 + 2 | from `a`: 2 + 3 | 4 |
| `aaa` | 4 + 2 | from `a`: 2 + 3 | 5 |
| `aaaa` | 5 + 2 | from `a`: 2 + 3 | 5 |

The final program is `sym a; ptr 0 2`. After the literal, the pointer copies from positions 0, 1, and 2 in succession. The last two positions exist because of the preceding copy steps. [ReducedDictionaryTrace](../src/AoP/Chapter09/ReducedDictionaryTrace.agda) checks the programs for the last three rows.

## Why those two candidates suffice

1. [DictionaryLastEdge](../src/AoP/Chapter09/DictionaryLastEdge.agda) splits any successful nonempty program at its final instruction. Its predecessor text is a strict prefix. For a final literal there is only one possible predecessor and last letter.
2. For two pointers with the same end text, [PointerSpanOrder](../src/AoP/Chapter09/PointerSpanOrder.agda) cancels their common final steps. The longer pointer starts at a prefix of the shorter pointer’s source **state** (the text present before executing the pointer, independently of the pointer offset).
3. [DecoderPrefix](../src/AoP/Chapter09/DecoderPrefix.agda) trims the rival’s program to this earlier state without increasing cost. The optimal row for that state costs at most the trimmed program. Both pointers add `p`, so [LongestPointerDominance](../src/AoP/Chapter09/LongestPointerDominance.agda) bounds the longer candidate by the shorter rival.
4. [ReducedBellman](../src/AoP/Chapter09/ReducedBellman.agda) applies these comparisons to the actual candidate chosen by [ReducedDictionary](../src/AoP/Chapter09/ReducedDictionary.agda). [ReducedDictionaryOptimal](../src/AoP/Chapter09/ReducedDictionaryOptimal.agda) extends the optimal-row invariant from the empty text through every prefix. `Solver.minimum` compares the returned program against **every** program decoding to the target.

[DictionaryCachedSize](../src/AoP/Chapter09/DictionaryCachedSize.agda) checks the book’s program-and-size representation separately. Starting at `([], 0)`, `push` appends one instruction and adds its charge to the cached size. The append-cost law proves the cache still equals the size of the whole program; `compare-cost` transfers a comparison of cached numbers to the underlying program costs. The prefix tables above compute costs from the stored programs.

## Scope and alternatives

Letter equality must be decidable. The charges `c` and `p` may be any natural numbers, including zero. Optimal programs can tie. [DictionarySearch](../src/AoP/Chapter09/DictionarySearch.agda) is a bounded exhaustive reference search; [DictionaryOptimal](../src/AoP/Chapter09/DictionaryOptimal.agda) certifies the intermediate table that tests all one-token extensions. The reduced encoder compares at most two program costs per nonempty row, but [finding the longest legal pointer](../src/AoP/Chapter09/LongestPointerScan.agda) still tests bounded tokens and prior rows. No overall running-time bound is claimed.

## Exercise 9.20: thinning the inverse fold

The [inverse fold](../src/AoP/Chapter09/DictionaryConverseFold.agda) reads a letter and either appends a literal, starts a one-letter pointer, or lengthens the last pointer. At `aa` with the charges above, two literals cost 4 and a literal followed by a pointer costs 5. Keeping only the cheaper program loses the best continuation: at `aaa` the pointer grows at no additional cost while appending a literal would cost 6. [DictionaryThinFailure](../src/AoP/Chapter09/DictionaryThinFailure.agda) checks this calculation. [InversePoolTrace](../src/AoP/Chapter09/InversePoolTrace.agda) evaluates the actual fold: the retained costs at `aa` are `[4,5]`; at `aaa` they are `[6,7,7,7,8,8,5]`. The solver selects `sym a; ptr 0 1` from that final pool. The sweep guarantees a representative for each discarded entry and can retain multiple entries with the same key.

The [pruned fold](../src/AoP/Chapter09/DictionaryStateExpand.agda) compares entries only within a key: closed, or an active pointer with a particular starting text, offset and span. A no-more-expensive representative can follow every move available to the rival. [DictionaryStateMinimum](../src/AoP/Chapter09/DictionaryStateMinimum.agda) replays every successful raw encoding as such a sequence of moves. Its `solve` returns a decoding certificate and a cost bound against all valid encodings, under the same fixed-charge assumptions. The [chapter inventory](chapter-nine.md) links each intermediate proof.
