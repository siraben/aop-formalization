# Scheduling one machine (§10.3)

Each job has a duration, a due date and a nonnegative weight. All jobs are available at time zero. The output is a permutation: every occurrence must be executed once. If a job finishes at time `t`, its weighted tardiness is `weight × max(0, t − due)`. Minimize the largest such penalty. An empty schedule has cost zero.

## Why choose the last job first?

Consider the [three-job example](../src/AoP/Chapter10/TardinessExample.agda):

| Job | Duration | Due | Weight | Penalty if last |
| --- | ---: | ---: | ---: | ---: |
| A | 5 | 10 | 1 | 20 |
| B | 10 | 20 | 3 | 30 |
| C | 15 | 20 | 3 | 30 |

Every order finishes at time 30. The last column gives a lower bound of 20 on the optimum: whichever job is last incurs at least 20. Choose A last, then place B and C. In order B,C,A the completion times are 10,25,30 and the penalties are 0,15,20, attaining the bound. C,B,A also attains it; the other four orders cost 30.

For the general argument, fix any ceiling attained by a competing permutation. Its last job meets the ceiling at the total duration of the jobs. The [selector](../src/AoP/Chapter10/PickLast.agda) chooses a job whose penalty at that same finish time is no greater. Remove that occurrence from the competitor: every intervening job moves earlier, so its penalty cannot increase. [Induction on the remaining jobs](../src/AoP/Chapter10/BackwardOptimal.agda) gives a prefix meeting the ceiling. Append the chosen job to it. Taking the competitor’s own maximum as the ceiling proves [global optimality](../src/AoP/Chapter10/ScheduleCertificate.agda).

## What changes with the objective?

* **Equal weights (10.9).** At a fixed finish time a later due date gives no greater penalty. Repeatedly placing a latest-due job last produces earliest-due-first order. [EqualWeightSchedule](../src/AoP/Chapter10/EqualWeightSchedule.agda) certifies that order using bottom-up merge sort. For positive `n` the sort uses at most `n × ⌈log₂ n⌉` due-date comparisons. This counts comparisons independently of the cost of comparing unbounded naturals. A [three-job calculation](../src/AoP/Chapter10/DeadlineSortExample.agda) takes three comparisons and reduces the maximum penalty from 10 to 2.
* **Signed lateness (10.10).** Use `weight × (t − due)` with integer subtraction. The empty schedule needs a separate bottom value so that negative peaks survive. [LatenessOptimal](../src/AoP/Chapter10/LatenessOptimal.agda) proves optimality by transferring every attainable integer ceiling. For two unit-duration jobs due at 4 and 8, both orders have zero tardiness; the [signed objective](../src/AoP/Chapter10/LatenessChoiceExample.agda) distinguishes peaks −3 and −2.
* **Sum of penalties (10.11).** Controlling each job by the competitor’s maximum does not control the sum. [SumTardiness](../src/AoP/Chapter10/SumTardiness.agda) exhibits a case where the backward rule costs 10 while a competitor costs 9. This counterexample concerns this choice rule.

The [chapter inventory](chapter-ten.md) links the intermediate algebra, insertion and bag-fibre proofs.
