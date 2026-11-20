# §6.6 Sorting by selection

| Derivation or exercise | Coverage |
| --- | --- |
| Ordered permutation specification | `Result` in [SelectionSort](../src/AoP/SelectionSort.agda) pairs `Sorted` with occurrence-preserving `Perm` for natural numbers. The general preorder specification remains open. |
| Select a minimum, remove one occurrence, recur on the remainder | [Selection](../src/AoP/Selection.agda) and [SelectionSort](../src/AoP/SelectionSort.agda) prove the executable algorithm meets `Result`. The point-free fusion calculation remains open. |
| Quicksort: split a nonempty input around its last element | `split` in [Quicksort](../src/AoP/Quicksort.agda) returns both sublists and a `Split` trace. The trace records a comparison and destination for each nonpivot item. |
| Introduce a pivot tree, unfold it by splitting, flatten in order | `Tree`, `unfold`, and `flatten` implement these steps. `duplicates` checks `[3,1,2,2]`. [QuickPermutation](../src/AoP/QuickPermutation.agda) proves that splitting and flattening preserve every occurrence. [QuickOrdered](../src/AoP/QuickOrdered.agda) carries pivot bounds through permutation and proves that quicksort meets the same `Result` specification as selection sort. |
| Move pivot bounds through flattening and permutation; derive quicksort by fusion | `upper-perm`, `lower-perm`, and `ordered` prove the forward bound-preservation and sortedness steps for natural numbers. The full relational equalities and fusion calculation remain open. |
| 6.22: permutation and membership, selection guard | [PermutationGuard](../src/AoP/PermutationGuard.agda) proves both directions of the membership law and shows that permuting the remainder commutes with testing its lower bound. `test` expresses the guard point-free using relational division, pair projections, and identity; `express` and `interpret` prove equivalence. |
| 6.23: termination of both sorts | `shorter` in SelectionSort and `smaller` in Quicksort justify recursive calls by input length. |
| 6.24: ordering by the intersection of preorders | [OrderedMeet](../src/AoP/OrderedMeet.agda) proves both relational inclusions for arbitrary comparison relations, using the all-pairs definition of orderedness. |
| 6.25: sorting a set represented by a list with duplicates | Open. |
| 6.26–6.28: preorder, postorder and merge variants of tree flattening | Open. |
| 6.29: changing the intermediate tree datatype | Open. |
| 6.30: insertion sort and its fusion condition | [InsertionSort](../src/AoP/InsertionSort.agda) proves the deletion guard, inserts into a sorted suffix, and returns the same `Result` as selection sort for natural numbers. |
