header {* Norm definitions *}

theory Norm_defs imports
  AList_ext
begin


subsection {* Types *}

type_synonym ('t, 'v) t_rule  = "'t \<times> 'v list"
type_synonym ('t, 'v) t_rules = "('t, 'v) t_rule list"
type_synonym ('t, 'v) v_rule  = "('v \<times> ('t, 'v) t_rules)"
type_synonym ('t, 'v) grammar = "('t, 'v) v_rule list"

type_synonym ('t, 'v) t_rule_norm   = "nat \<times> ('t, 'v) t_rule"
type_synonym ('t, 'v) t_rules_norms = "('t, 'v) t_rule_norm list"
type_synonym ('t, 'v) v_rule_norm   = "('v \<times> ('t, 'v) t_rule_norm)"
type_synonym ('t, 'v) grammar_norms = "('t, 'v) v_rule_norm list"


subsection {* Grammar *}

definition gram_sd :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_sd gr \<equiv> is_alist gr \<and>
     (\<forall>(v, rules) \<in> set gr. is_alist rules \<and> rules \<noteq> [] \<and>
       (\<forall>(t, vars) \<in> set rules. set vars \<subseteq> keys gr))"

definition gram_max_vars :: "('t, 'v) grammar \<Rightarrow> nat" where
  "gram_max_vars gr = Max (set (map (\<lambda>(_, rules). Max (set (map (length \<circ> snd) rules))) gr))"


subsection {* Norm *}

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


subsection {* Equivalence *}

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

end
