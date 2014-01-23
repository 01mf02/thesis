header {* Tests *}

theory Tests imports
  Norm_proofs
  "~~/src/HOL/Library/Code_Target_Nat"
begin

export_code gram_nsd_fun norms_of_grammar in OCaml file "../OCaml/Norm.ml"

definition test_gr :: "(nat, nat) grammar" where
  "test_gr =
   [(0, [(0, [])]),
    (1, [(1, [0])])]"

definition test_gr2 :: "(nat, nat) grammar" where
  "test_gr2 =
   [(0, [(0, [])]),
    (1, [(1, [0])]),
    (2, [(2, [1]), (3, [3])]),
    (3, [(4, [])])]"

definition test_gr3 :: "(nat, nat) grammar" where
  "test_gr3 =
   [(0, [(0, [0])])]"

definition test_gr4 :: "(nat, nat) grammar" where
  "test_gr4 =
   [(1, [(0, [])]),
    (2, [(0, [1])]),
    (3, [(0, [2])]),
    (4, [(0, [1, 1, 1])]),
    (5, [(23, [3]), (24, [4])])]"

value "gram_nsd_fun test_gr"
value "norm_fun test_gr [0] = 1"
value "norm_fun test_gr [1] = 2"
value "word_in_variables test_gr [0] [0]"
value "min_word_of_variables test_gr [1] = [1, 0]"

value "gram_nsd_fun test_gr2"
value "norm_fun test_gr2 [0] = 1"
value "norm_fun test_gr2 [1] = 2"
value "norm_fun test_gr2 [2] = 2"
value "norm_fun test_gr2 [3] = 1"

value "gram_sd test_gr3"
value "gram_nsd_fun test_gr3 = False"

value "gram_nsd_fun test_gr4"
value "norms_of_grammar test_gr4"

end
