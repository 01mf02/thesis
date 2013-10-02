theory Grammar_defs imports AList_ext
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_ord"
begin

type_synonym ('t, 'v) production_rule = "('t \<times> 'v list)"
type_synonym ('t, 'v) production_rules = "('t, 'v) production_rule list"
type_synonym ('t, 'v) grammar = "('v \<times> ('t, 'v) production_rules) list"

type_synonym ('t, 'v) norm_list = "('v \<times> (nat \<times> ('t, 'v) production_rule)) list"


definition gram_valid :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_valid gr \<equiv> is_typical_alist gr \<and>
     (\<forall>g \<in> set gr. case g of (v, pr) \<Rightarrow> is_typical_alist pr \<and>
       (\<forall>vs \<in> set (map snd pr). \<forall>v' \<in> set vs. v' \<in> fst ` set gr) \<and>
       (\<exists>vs \<in> set (map snd pr). \<forall>v' \<in> set vs. v' < v))"

definition norm_of_variables :: "('t, 'v) norm_list \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_of_variables norms vars \<equiv> listsum (map fst (map (\<lambda>v. of_key norms v) vars))"

definition norm_list_of_rules ::
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> (nat \<times> ('t, 'v) production_rule) list" where
  "norm_list_of_rules norms rules \<equiv>
     let valid_rules = filter (\<lambda>(t, vs). \<forall>v \<in> set vs. v \<in> fst ` set norms) rules in
     map (\<lambda>r. (1 + norm_of_variables norms (snd r), r)) valid_rules"

definition norm_of_production_rules ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norm_of_production_rules gr \<equiv> (fold (\<lambda>(v, rules). \<lambda>norms.
     norms@[(v, Min (set (norm_list_of_rules norms rules)))]) gr [])"

fun eat_word :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = of_key gr vh in
     if th \<in> fst ` set prods then eat_word gr tt ((of_key prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

lemmas eat_word_induct = eat_word.induct[case_names normal nil_word nil_vars]

function minimal_word_of_variables where
  "minimal_word_of_variables gr [] = []"
| "minimal_word_of_variables gr (vh#vt) = (
     if gram_valid gr then
       let norms = norm_of_production_rules gr in
       let (t, vars) = snd (of_key norms vh) in
       t#(minimal_word_of_variables gr (vars@vt))
     else [])"
by pat_completeness auto
termination
  (* apply (relation "\<lambda>x. ...") *)
  (* See functions.pdf. *)
oops

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Min {length w | w. word_in_variables gr w v}"


fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce gr v 0 = v"
| "norm_reduce gr [] (Suc p) = []"
| "norm_reduce gr (vh#vt) (Suc p) = (
     let (n, (_, v)) = of_key (norm_of_production_rules gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"


definition test_gr :: "(char, nat) grammar" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

value "gram_valid test_gr"
value "norm_of_production_rules test_gr"
value "word_in_variables test_gr ''a'' [0]"

end
