# §6.6 Sorting by selection

| Derivation or exercise | Coverage |
| --- | --- |
| Ordered permutation specification | `Result` in [SelectionSort](../src/AoP/SelectionSort.agda) pairs `Sorted` with occurrence-preserving `Perm` for natural numbers. The general preorder specification remains open. |
| Select a minimum, remove one occurrence, recur on the remainder | [Selection](../src/AoP/Selection.agda) and [SelectionSort](../src/AoP/SelectionSort.agda) prove the executable algorithm meets `Result`. The point-free fusion calculation remains open. |
| Quicksort: split a nonempty input around its last element | `split` in [Quicksort](../src/AoP/Quicksort.agda) returns both sublists and a `Split` trace. The trace records a comparison and destination for each nonpivot item. |
| Introduce a pivot tree, unfold it by splitting, flatten in order | `Tree`, `unfold`, and `flatten` implement these steps. `duplicates` checks `[3,1,2,2]`. [QuickPermutation](../src/AoP/QuickPermutation.agda) proves that splitting and flattening preserve every occurrence. General sortedness remains open. |
| Move pivot bounds through flattening and permutation; derive quicksort by fusion | Open. |
| 6.22: permutation and membership, selection guard | Open. |
| 6.23: termination of both sorts | `shorter` in SelectionSort and `smaller` in Quicksort justify recursive calls by input length. |
| 6.24: ordering by the intersection of preorders | Open. |
| 6.25: sorting a set represented by a list with duplicates | Open. |
| 6.26–6.28: preorder, postorder and merge variants of tree flattening | Open. |
| 6.29: changing the intermediate tree datatype | Open. |
| 6.30: insertion sort and its fusion condition | [InsertionSort](../src/AoP/InsertionSort.agda) proves the deletion guard, inserts into a sorted suffix, and returns the same `Result` as selection sort for natural numbers. |
