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
recall that this results in a mere overestimation of the final norms:
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

Now we compare the output from the norm iteration algorithm with the output from
the norm iteration algorithm with added refinement at the end.
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
concering variable 5, differ. That means that the refinement found a smaller
norm for variable 5 than the overestimation algorithm.

Finally, we can also calculate the norm of variable words:
*}

lemma "norm_fun test_gr [1, 3, 5] = 8" by eval

end
