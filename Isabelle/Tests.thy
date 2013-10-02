theory Tests imports Grammar
begin

definition test_gr :: "(char, nat) grammar" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

value "gram_valid test_gr"
value "norms_of_grammar test_gr"
value "word_in_variables test_gr ''a'' [0]"

end
