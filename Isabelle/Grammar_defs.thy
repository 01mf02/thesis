theory Grammar_defs imports
  AList_ext
  Helpers
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_Lexorder"
begin


(*****************************************************************************
  Types
 *****************************************************************************)

type_synonym ('t, 'v) production_rule = "'t \<times> 'v list"
type_synonym ('t, 'v) production_rules = "('t, 'v) production_rule list"
type_synonym ('t, 'v) grammar = "('v \<times> ('t, 'v) production_rules) list"

type_synonym ('t, 'v) norm_rule = "nat \<times> ('t, 'v) production_rule"
type_synonym ('t, 'v) norm_rules = "('t, 'v) norm_rule list"
type_synonym ('t, 'v) norm_list = "('v \<times> ('t, 'v) norm_rule) list"


(*****************************************************************************
  Grammar
 *****************************************************************************)

definition gram_sd :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_sd gr \<equiv> is_alist gr \<and>
     (\<forall>(v, rules) \<in> set gr. is_alist rules \<and> rules \<noteq> [] \<and>
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
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> ('t, 'v) norm_rules" where
  "norms_of_rules norms rules \<equiv>
     map (\<lambda>(t, vs). (1 + norm_sum norms vs, (t, vs))) (filter (rule_has_norm norms) rules)"

definition min_norm_of_rules :: "('t::linorder, 'v::linorder) norm_list \<Rightarrow>
  ('t, 'v) production_rules \<Rightarrow> ('t, 'v) norm_rule" where
  "min_norm_of_rules norms rules \<equiv> Min (set (norms_of_rules norms rules))"

definition split_normable where
  "split_normable gr norms = partition (\<lambda>(v, rules). rules_have_norm norms rules) gr"

definition itno_p where "itno_p = (\<lambda>norms (v, rules). rules_have_norm norms rules)"
definition itno_f where "itno_f = (\<lambda>norms (v, rules). (v, min_norm_of_rules norms rules)#norms)"

definition split_normable2 where
  "split_normable2 norms = partition (itno_p norms)"

definition iterate_norms2 ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> (('t, 'v) norm_list \<times> ('t, 'v) grammar)" where
  "iterate_norms2 gr = partition_fold itno_p itno_f [] gr"

function iterate_norms where
  "iterate_norms rest norms = (case split_normable rest norms of
       ([], unnormable) \<Rightarrow> (unnormable, norms)
     | ((v, rules)#normable_tl, unnormable) \<Rightarrow>
         iterate_norms (normable_tl@unnormable) ((v, min_norm_of_rules norms rules)#norms))"
by pat_completeness auto

definition gram_normed_fun :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> bool" where
  "gram_normed_fun gr \<equiv> fst (iterate_norms gr []) = []"

definition gram_nsd :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> bool" where
  "gram_nsd gr \<equiv> gram_sd gr \<and> gram_normed_fun gr"

definition norms_of_grammar ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norms_of_grammar gr \<equiv> snd (iterate_norms gr [])"

definition norm_of_variables :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_of_variables gr vars \<equiv> norm_sum (norms_of_grammar gr) vars"

function minimal_word_of_variables ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> 't list" where
  "minimal_word_of_variables gr [] = []"
| "minimal_word_of_variables gr (vh#vt) = (
     if gram_nsd gr \<and> vh \<in> keys gr then
       let (t, vars) = snd (lookup (norms_of_grammar gr) vh) in
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

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition gram_normed :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_normed gr \<equiv> \<forall>v. set v \<subseteq> keys gr \<longrightarrow> (\<exists>w. word_in_variables gr w v)"

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
     let (n, _, v) = lookup (norms_of_grammar gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"

end
