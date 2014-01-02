header {* Norm functions *}

theory Norm_funs imports
  Norm_defs
  Partition_iterate
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_Lexorder"
  "~~/src/HOL/Library/Code_Target_Nat"
begin


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

definition add_norms ::
  "('t::linorder, 'v::linorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow> ('t, 'v) grammar_norms" where
  "add_norms norms yes = norms @ (mnotr_map norms yes)"

definition update_norms where
  "update_norms gr norms yes = minimise_norms (add_norms norms yes) gr"

definition iterate_norms2 ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> (('t, 'v) grammar_norms \<times> ('t, 'v) grammar)" where
  "iterate_norms2 gr = partition_iterate v_rule_has_norm (update_norms gr) [] gr"

definition iterate_norms ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> (('t, 'v) grammar_norms \<times> ('t, 'v) grammar)" where
  "iterate_norms gr = partition_iterate v_rule_has_norm add_norms [] gr"

definition itno_invariant where
  "itno_invariant gr norms rest \<equiv> set rest \<subseteq> set gr \<and> keys gr = keys norms \<union> keys rest"

definition itno_invariant_sd where
  "itno_invariant_sd gr norms rest \<equiv> is_alist norms \<and> is_alist rest \<and> keys rest \<inter> keys norms = {}"

definition itno_invariant_sd_in where
  "itno_invariant_sd_in norms rules n t vs \<equiv>
     t_rules_have_norm norms rules \<and> (n, t, vs) = min_norm_of_t_rules norms rules"

definition itno2_invariant_sd_in where
  "itno2_invariant_sd_in norms v rules \<equiv>
     t_rules_have_norm norms rules \<and> (v, min_norm_of_t_rules norms rules) \<in> set norms"

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
