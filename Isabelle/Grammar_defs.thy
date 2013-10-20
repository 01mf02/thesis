theory Grammar_defs imports AList_ext
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_ord"
begin


(*****************************************************************************
  Types
 *****************************************************************************)

type_synonym ('t, 'v) production_rule = "('t \<times> 'v list)"
type_synonym ('t, 'v) production_rules = "('t, 'v) production_rule list"
type_synonym ('t, 'v) grammar = "('v \<times> ('t, 'v) production_rules) list"

type_synonym ('t, 'v) norm_list = "('v \<times> (nat \<times> ('t, 'v) production_rule)) list"


(*****************************************************************************
  Grammar
 *****************************************************************************)

definition gram_valid :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_valid gr \<equiv> is_typical_alist gr \<and>
     (\<forall>(v, rules) \<in> set gr. is_typical_alist rules \<and>
       (\<forall>(t, vars) \<in> set rules. set vars \<subseteq> keys gr))"

definition gram_max_vars :: "('t, 'v) grammar \<Rightarrow> nat" where
  "gram_max_vars gr = Max (set (map (\<lambda>(_, rules). Max (set (map (length \<circ> snd) rules))) gr))"


(*****************************************************************************
  Norm calculation
 *****************************************************************************)

definition norm_sum :: "('t, 'v) norm_list \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_sum norms vars \<equiv> listsum (map (fst \<circ> lookup norms) vars)"

definition rule_has_norm :: "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rule \<Rightarrow> bool" where
  "rule_has_norm norms \<equiv> \<lambda>(t, vs). \<forall>v \<in> set vs. v \<in> keys norms"

definition rules_have_norm :: "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> bool" where
  "rules_have_norm norms rules \<equiv> \<exists>r \<in> set rules. rule_has_norm norms r"

definition norms_of_rules ::
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> (nat \<times> ('t, 'v) production_rule) list" where
  "norms_of_rules norms rules \<equiv>
     map (\<lambda>(t, vs). (1 + norm_sum norms vs, (t, vs))) (filter (rule_has_norm norms) rules)"

definition min_norm_of_rules where
  "min_norm_of_rules norms rules \<equiv> Min (set (norms_of_rules norms rules))"

definition norms_of_grammar ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norms_of_grammar gr \<equiv> (fold (\<lambda>(v, rules). \<lambda>ns. ns@[(v, min_norm_of_rules ns rules)]) gr [])"

definition split_normable where
  "split_normable gr norms = partition (\<lambda>(v, rules). rules_have_norm norms rules) gr"

function iterate_norms where
  "iterate_norms gr norms = (case split_normable gr norms of
     ([], _) \<Rightarrow> norms
   | ((v, rules)#normable, unnormable) \<Rightarrow>
       iterate_norms (normable@unnormable) ((v, min_norm_of_rules norms rules)#norms))"
by pat_completeness auto

definition norms_of_grammar_new ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norms_of_grammar_new gr \<equiv> sort (iterate_norms gr [])"

definition norm_of_variables :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_of_variables gr vars \<equiv> norm_sum (norms_of_grammar gr) vars"

function minimal_word_of_variables ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> 't list" where
  "minimal_word_of_variables gr [] = []"
| "minimal_word_of_variables gr (vh#vt) = (
     if gram_valid (* TODO! use gram_normed here! *) gr \<and> set (vh#vt) \<subseteq> keys gr then
       let norms = norms_of_grammar gr in
       let (t, vars) = snd (lookup norms vh) in
       t # minimal_word_of_variables gr vars @ minimal_word_of_variables gr vt
     else [])"
by pat_completeness auto


(*****************************************************************************
  Norm definition
 *****************************************************************************)

fun eat_word :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = lookup gr vh in
     if th \<in> keys prods then eat_word gr tt ((lookup prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

lemmas eat_word_induct = eat_word.induct[case_names normal nil_word nil_vars]

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition gram_normed where
  "gram_normed gr \<equiv> gram_valid gr \<and> (\<forall>(v, _) \<in> set gr. \<exists>w. w \<in> words_of_variables gr [v])"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Least (\<lambda>l. l \<in> (length ` (words_of_variables gr v)))"


(*****************************************************************************
  Equivalence
 *****************************************************************************)

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"


(*****************************************************************************
  Norm reduction
 *****************************************************************************)

fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce gr v 0 = v"
| "norm_reduce gr [] (Suc p) = []"
| "norm_reduce gr (vh#vt) (Suc p) = (
     let (n, (_, v)) = lookup (norms_of_grammar gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"

end
