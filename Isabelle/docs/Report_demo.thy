theory Report_demo imports
  "../Norm_proofs"
  "~~/src/HOL/Library/LaTeXsugar"
begin

definition test_gr :: "(nat, nat) grammar" where
  "test_gr =
   [(1, [(0, [])]),
    (2, [(0, [1])]),
    (3, [(0, [2])]),
    (4, [(0, [1, 1, 1])]),
    (5, [(23, [3]), (24, [4])])]"

text {*
Let us first see what happens when we run the norm iteration algorithm without refinement ---
recall that this might lead to wrong results:
*}

lemma "iterate_norms test_gr =
  ([(1, 1, 0, []),
    (2, 2, 0, [1]),
    (4, 4, 0, [1, 1, 1]),
    (3, 3, 0, [2]),
    (5, 5, 24, [4])],
   [])"
by eval

text {*
In the results of the algorithm, we first note that the grammar is normed, because all
variables have a finite norm, which is indicated by the empty list in the second component
of the result pair.

To see whether the norm iteration algorithm returned the right results in this case,
we compare its output with the output from the norm iteration algorithm with
added refinement at the end.
*}

lemma "norms_of_grammar test_gr =
  [(1, 1, 0, []),
   (2, 2, 0, [1]),
   (4, 4, 0, [1, 1, 1]),
   (3, 3, 0, [2]),
   (5, 4, 23, [3])]"
by eval

text {*
Comparing the two results, we note that the last norm entries, namely those
concering variable 5, differ.
That is because the algorithm has first calculated the norm of variable 1, then in the
next iteration the norm of variables 2 and 4, then finally the norm of variables 3 and 5.
However, a reinspection of the norms yields that using the norm of variable 3, we can
find a smaller norm of variable 5, which one refinement step calculates.

Finally, we can also calculate the norm of variable words:
*}

lemma "norm_fun test_gr [1, 3, 5] = 8" by eval

end
