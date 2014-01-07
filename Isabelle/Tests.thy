header {* Tests *}

theory Tests imports Norm_proofs
  "~~/src/HOL/Library/Char_ord"
begin

definition test_gr :: "(char, nat) grammar" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

definition test_gr2 :: "(char, nat) grammar" where
  "test_gr2 =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])]),
    (2, [(CHR ''c'', [1]), (CHR ''d'', [3])]),
    (3, [(CHR ''e'', [])])]"

definition test_gr3 :: "(char, nat) grammar" where
  "test_gr3 =
   [(0, [(CHR ''a'', [0])])]"

definition test_gr4 :: "(char, nat) grammar" where
  "test_gr4 =
   [(1, [(CHR ''a'', [])]),
    (2, [(CHR ''a'', [1])]),
    (3, [(CHR ''a'', [2])]),
    (4, [(CHR ''a'', [1, 1, 1])]),
    (5, [(CHR ''x'', [3]), (CHR ''y'', [4])])]"

value "gram_nsd_fun test_gr"
value "gram_max_vars test_gr = 1"
value "norm_fun test_gr [0] = 1"
value "norm_fun test_gr [1] = 2"
value "word_in_variables test_gr ''a'' [0]"
value "min_word_of_variables test_gr [1] = ''ba''"

value "gram_nsd_fun test_gr2"
value "norm_fun test_gr2 [0] = 1"
value "norm_fun test_gr2 [1] = 2"
value "norm_fun test_gr2 [2] = 2"
value "norm_fun test_gr2 [3] = 1"

value "gram_sd test_gr3"
value "gram_nsd_fun test_gr3 = False"

value "gram_nsd_fun test_gr4"
value "iterate_norms test_gr4"

export_code gram_nsd_fun norms_of_grammar in OCaml file "../Norm.ml"

end
