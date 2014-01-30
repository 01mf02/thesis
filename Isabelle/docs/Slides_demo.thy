theory Slides_demo imports
  "../Tests"
  "~~/src/HOL/Library/LaTeXsugar"
begin

text {*
@{thm [display] test_gr4_def}
@{lemma "norms_of_grammar test_gr4 =
   [(1, 1, 0, []), (2, 2, 0, [1]), (4, 4, 0, [1, 1, 1]), (3, 3, 0, [2]), (5, 4, 23, [3])]" by eval}
*}

end
