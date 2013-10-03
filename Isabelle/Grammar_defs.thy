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
       (\<forall>vs \<in> snd ` set rules. \<forall>v' \<in> set vs. v' \<in> fst ` set gr) \<and>
       (\<exists>vs \<in> snd ` set rules. \<forall>v' \<in> set vs. v' < v))"

definition gram_max_vars :: "('t, 'v) grammar \<Rightarrow> nat" where
  "gram_max_vars gr = Max (set (map (\<lambda>(_, rules). Max (set (map (\<lambda>(_, vs). length vs) rules))) gr))"


(*****************************************************************************
  Norm calculation
 *****************************************************************************)

definition norm_sum :: "('t, 'v) norm_list \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_sum norms vars \<equiv> listsum (map fst (map (\<lambda>v. of_key norms v) vars))"

definition rule_has_norm ::
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rule \<Rightarrow> bool" where
  "rule_has_norm norms \<equiv> \<lambda>(t, vs). \<forall>v \<in> set vs. v \<in> fst ` set norms"

definition norms_of_rules ::
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> (nat \<times> ('t, 'v) production_rule) list" where
  "norms_of_rules norms rules \<equiv>
     map (\<lambda>(t, vs). (1 + norm_sum norms vs, (t, vs))) (filter (rule_has_norm norms) rules)"

definition min_norm_of_rules where
  "min_norm_of_rules norms rules = Min (set (norms_of_rules norms rules))"

definition norms_of_grammar ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norms_of_grammar gr \<equiv> (fold (\<lambda>(v, rules). \<lambda>ns. ns@[(v, min_norm_of_rules ns rules)]) gr [])"

definition norm_of_variables :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_of_variables gr vars \<equiv> norm_sum (norms_of_grammar gr) vars"

function minimal_word_of_variables :: "('t :: linorder, nat) grammar \<Rightarrow> nat list \<Rightarrow> 't list" where
  "minimal_word_of_variables gr [] = []"
| "minimal_word_of_variables gr (vh#vt) = (
     if gram_valid gr \<and> set (vh#vt) \<subseteq> fst ` set gr then
       let norms = norms_of_grammar gr in
       let (t, vars) = snd (of_key norms vh) in
       t#(minimal_word_of_variables gr (vars@vt))
     else [])"
by pat_completeness auto


(*****************************************************************************
  Norm definition
 *****************************************************************************)

fun eat_word :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = of_key gr vh in
     if th \<in> fst ` set prods then eat_word gr tt ((of_key prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

lemmas eat_word_induct = eat_word.induct[case_names normal nil_word nil_vars]

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Min {length w | w. word_in_variables gr w v}"


(*****************************************************************************
  Norm reduction
 *****************************************************************************)

fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce gr v 0 = v"
| "norm_reduce gr [] (Suc p) = []"
| "norm_reduce gr (vh#vt) (Suc p) = (
     let (n, (_, v)) = of_key (norms_of_grammar gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"

end
