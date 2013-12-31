theory Grammar_defs imports
  AList_ext
  Helpers
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_Lexorder"
  "~~/src/HOL/Library/Code_Target_Nat"
begin


(*****************************************************************************
  Types
 *****************************************************************************)

type_synonym ('t, 'v) t_rule  = "'t \<times> 'v list"
type_synonym ('t, 'v) t_rules = "('t, 'v) t_rule list"
type_synonym ('t, 'v) v_rule  = "('v \<times> ('t, 'v) t_rules)"
type_synonym ('t, 'v) grammar = "('t, 'v) v_rule list"

type_synonym ('t, 'v) t_rule_norm   = "nat \<times> ('t, 'v) t_rule"
type_synonym ('t, 'v) t_rules_norms = "('t, 'v) t_rule_norm list"
type_synonym ('t, 'v) v_rule_norm   = "('v \<times> ('t, 'v) t_rule_norm)"
type_synonym ('t, 'v) grammar_norms = "('t, 'v) v_rule_norm list"


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

definition norm_sum :: "('t, 'v) grammar_norms \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_sum norms vars \<equiv> listsum (map (fst \<circ> lookup norms) vars)"

definition t_rule_has_norm :: "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rule \<Rightarrow> bool" where
  "t_rule_has_norm norms \<equiv> \<lambda>(t, vs). set vs \<subseteq> keys norms"

definition t_rules_have_norm :: "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rules \<Rightarrow> bool" where
  "t_rules_have_norm norms rules \<equiv> \<exists>r \<in> set rules. t_rule_has_norm norms r"

definition norms_of_t_rules ::
  "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rules \<Rightarrow> ('t, 'v) t_rules_norms" where
  "norms_of_t_rules norms rules \<equiv>
     map (\<lambda>(t, vs). (Suc (norm_sum norms vs), (t, vs))) (filter (t_rule_has_norm norms) rules)"

definition min_norm_of_t_rules :: "('t::linorder, 'v::linorder) grammar_norms \<Rightarrow>
  ('t, 'v) t_rules \<Rightarrow> ('t, 'v) t_rule_norm" where
  "min_norm_of_t_rules norms rules \<equiv> Min (set (norms_of_t_rules norms rules))"

definition v_rule_has_norm ::
  "('t::linorder, 'v::linorder) grammar_norms \<Rightarrow> ('t, 'v) v_rule \<Rightarrow> bool" where
  "v_rule_has_norm = (\<lambda>norms (v, rules). t_rules_have_norm norms rules)"

definition mnotr_map where
  "mnotr_map norms = map (\<lambda>(v, rules). (v, min_norm_of_t_rules norms rules))"
  (*"mnotr_map norms = value_map (min_norm_of_t_rules norms)"*)

definition update_norms ::
  "('t::linorder, 'v::linorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow> ('t, 'v) grammar_norms" where
  "update_norms norms yes = norms @ (mnotr_map norms yes)"

definition v_rules_of_norms where
  "v_rules_of_norms norms gr = map (\<lambda>(v, n, t, vs). (v, lookup gr v)) norms"

definition refine_norms where
  "refine_norms norms gr = mnotr_map norms (v_rules_of_norms norms gr)"

definition norms_total where
  "norms_total norms = listsum (map (\<lambda>(v, n, t, vs). n) norms)"

function minimise_norms where
  "minimise_norms norms gr =
     (if refine_norms norms gr = norms then norms else minimise_norms (refine_norms norms gr) gr)"
by auto

definition iterate_norms ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> (('t, 'v) grammar_norms \<times> ('t, 'v) grammar)" where
  "iterate_norms gr = partition_iterate v_rule_has_norm update_norms [] gr"

definition itno_invariant where
  "itno_invariant gr norms rest \<equiv> set rest \<subseteq> set gr \<and> keys gr = keys norms \<union> keys rest"

definition itno_invariant_sd where
  "itno_invariant_sd gr norms rest \<equiv> is_alist norms \<and> is_alist rest \<and> keys rest \<inter> keys norms = {}"

definition itno_invariant_sd_in where
  "itno_invariant_sd_in norms rules n t vs \<equiv>
     t_rules_have_norm norms rules \<and> (n, t, vs) = min_norm_of_t_rules norms rules"

definition gram_normed_fun :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> bool" where
  "gram_normed_fun gr \<equiv> snd (iterate_norms gr) = []"

definition gram_nsd_fun :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> bool" where
  "gram_nsd_fun gr \<equiv> gram_sd gr \<and> gram_normed_fun gr"

definition norms_of_grammar ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) grammar_norms" where
  "norms_of_grammar gr \<equiv> fst (iterate_norms gr)"

definition norm_fun :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_fun gr vars \<equiv> norm_sum (norms_of_grammar gr) vars"

function min_word_of_variables ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> 't list" where
  "min_word_of_variables gr vars = (
     if gram_nsd_fun gr \<and> set vars \<subseteq> keys gr then
       concat (map (\<lambda>(n, t, vs). t # (min_word_of_variables gr vs))
                   (map (lookup (norms_of_grammar gr)) vars))
     else [])"
by auto


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

definition gram_normed_def :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_normed_def gr \<equiv> \<forall>v. set v \<subseteq> keys gr \<longrightarrow> (\<exists>w. word_in_variables gr w v)"

definition gram_nsd_def :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_nsd_def gr \<equiv> gram_sd gr \<and> gram_normed_def gr"

definition norm_def :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_def gr v \<equiv> Least (\<lambda>l. l \<in> (length ` (words_of_variables gr v)))"


(*****************************************************************************
  Equivalence
 *****************************************************************************)

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"


(*****************************************************************************
  Norm reduction
 *****************************************************************************)

fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar_norms \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce norms v 0 = v"
| "norm_reduce norms [] (Suc p) = []"
| "norm_reduce norms (vh#vt) (Suc p) = (
     let (n, _, v) = lookup norms vh in
     if Suc p < n then (norm_reduce norms v p) @ vt
     else norm_reduce norms vt (Suc p - n))"

export_code gram_nsd_fun norms_of_grammar in OCaml file "../Norm.ml"

end
