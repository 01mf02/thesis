theory Tests imports Grammar
  "~~/src/HOL/Library/Char_ord"
begin

definition test_gr :: "(char, nat) v_rules" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

definition test_gr2 :: "(char, nat) v_rules" where
  "test_gr2 =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])]),
    (2, [(CHR ''c'', [1]), (CHR ''d'', [3])]),
    (3, [(CHR ''e'', [])])]"

definition test_gr3 :: "(char, nat) v_rules" where
  "test_gr3 =
   [(0, [(CHR ''a'', [0])])]"

value "gram_nsd test_gr"
value "gram_max_vars test_gr = 1"
value "norm_of_variables test_gr [0] = 1"
value "norm_of_variables test_gr [1] = 2"
value "word_in_variables test_gr ''a'' [0]"
value "minimal_word_of_variables test_gr [1] = ''ba''"
value "mwov2 test_gr [1] = ''ba''"

value "gram_nsd test_gr2"
value "norm_of_variables test_gr2 [0] = 1"
value "norm_of_variables test_gr2 [1] = 2"
value "norm_of_variables test_gr2 [2] = 2"
value "norm_of_variables test_gr2 [3] = 1"

value "gram_sd test_gr3"
value "gram_nsd test_gr3 = False"

end
