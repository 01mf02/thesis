theory Grammar imports
  "Grammar_defs"
  "Helpers"
begin

(*****************************************************************************
  gram_valid
 *****************************************************************************)

lemma gram_alist: "gram_valid gr \<Longrightarrow> is_alist gr"
by (simp add: gram_valid_def is_typical_alist_def)

lemma gram_rule_vars_in_fst:
  assumes "gram_valid gr"
      and "rules \<in> snd ` set gr"
      and "vars \<in> snd ` set rules"
    shows "set vars \<subseteq> fst ` set gr" using assms
  unfolding gram_valid_def
  apply auto
sorry


(*****************************************************************************
  norm_sum
 *****************************************************************************)

lemma ns_singleton: "norm_sum ns [v] = fst (of_key ns v)"
by (simp add: norm_sum_def)


(*****************************************************************************
  rules_have_norm
 *****************************************************************************)

lemma rhn_empty_exists: "gram_normed gr \<Longrightarrow> \<exists>(v, rules) \<in> set gr. rules_have_norm [] rules"
sorry


(*****************************************************************************
  norms_of_rules
 *****************************************************************************)

lemma "snd ` set (norms_of_rules norms rules) \<subseteq> set rules"
by (unfold norms_of_rules_def) auto

lemma nor_nonempty:
  assumes "\<exists>r \<in> set rules. rule_has_norm norms r"
    shows "norms_of_rules norms rules \<noteq> []"
using assms by (simp add: norms_of_rules_def filter_empty_conv)

lemma
  assumes "\<exists>r \<in> set rules. rule_has_norm norms r"
    shows "snd (Min (set (norms_of_rules norms rules))) \<in> set rules"
using assms by - (rule Min_predicate, auto simp add: norms_of_rules_def)


(*****************************************************************************
  min_norm_of_rules
 *****************************************************************************)

lemma mnor_in_nor:
  assumes "rules_have_norm norms rules"
    shows "min_norm_of_rules norms rules \<in> set (norms_of_rules norms rules)" using assms
  apply (auto simp add: min_norm_of_rules_def norms_of_rules_def rules_have_norm_def)
  apply (rule Min.closed)
by (auto simp add: filter_empty_conv min_def)

lemma mnor_in_rules:
  assumes "rules_have_norm norms rules"
    shows "snd (min_norm_of_rules norms rules) \<in> set rules"
sorry


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma "length (norms_of_grammar gr) = length gr"
by (auto simp add: norms_of_grammar_def fold_concat_empty_init)

lemma nog_fst_is_gr_fst: "map fst gr = map fst (norms_of_grammar gr)"
by (auto simp add: norms_of_grammar_def
    key_fold_empty_init[of _ "\<lambda>(v, rules) norms. min_norm_of_rules norms rules"])

lemma nog_alist: "gram_valid gr \<Longrightarrow> is_alist (norms_of_grammar gr)"
by (simp add: alist_fst_map gram_alist nog_fst_is_gr_fst)

(* TODO: this is a most central lemma, but probably quite difficult to prove ... *)
lemma nog_mnor:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "of_key (norms_of_grammar gr) v = min_norm_of_rules (norms_of_grammar gr) rules" using assms
  apply -
  apply (rule of_key_from_existence)
  apply (simp add: nog_alist)
sorry

lemma nog_sufficient:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "norms_sufficient (norms_of_grammar gr) rules"
sorry

lemma nog_in_rules':
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "snd (of_key (norms_of_grammar gr) v) \<in> set rules" using assms
by (auto simp add: nog_mnor mnor_in_rules nog_sufficient)

lemma nog_in_rules:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(t, vars) = snd (of_key (norms_of_grammar gr) v)"
    shows "(t, vars) \<in> set rules" using assms
by (auto simp add: nog_in_rules')


(*****************************************************************************
  norm_of_variables
 *****************************************************************************)

lemma nov_distr: "norm_of_variables gr (x @ y) = norm_of_variables gr x + norm_of_variables gr y"
by (simp add: norm_of_variables_def norm_sum_def)

lemma nov_distr': "norm_of_variables gr (x # y) = norm_of_variables gr [x] + norm_of_variables gr y"
by (rule nov_distr[of _ "[x]", simplified])

lemma nov_singleton:
  assumes "gram_valid gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "norm_of_variables gr [v] = n"
proof -
  have "norm_of_variables gr [v] = fst (of_key (norms_of_grammar gr) v)"  (is "_ = ?rhs")
    by (simp add: norm_of_variables_def norm_sum_def)
  also have "?rhs = fst (n, t, vs)" using assms
    by (simp_all add: of_key_from_existence nog_alist)
  finally show ?thesis by auto
qed

lemma nov_nog:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
    shows "norm_of_variables gr [v] = Suc (norm_of_variables gr vs)"
proof (simp add: norm_of_variables_def norm_sum_def)
  have "(of_key (norms_of_grammar gr) v) = min_norm_of_rules (norms_of_grammar gr) rules" sorry
  then show "fst (of_key (norms_of_grammar gr) v) = Suc(listsum (map (fst \<circ> of_key (norms_of_grammar gr)) vs))" sorry
qed

lemma nov_nog':
  assumes "gram_valid gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]" using assms
by (auto simp add: nov_nog)

lemma nov_greater_zero: "gram_valid gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> 
  0 < norm_of_variables gr [v]"
sorry


(*****************************************************************************
  iterate_norms
 *****************************************************************************)

termination iterate_norms
apply (relation "measure (\<lambda>(gr, norms). length gr)", auto)
apply (auto simp only: split_normable_def partition_length add_less_cancel_right)
by (metis (full_types) impossible_Cons not_less)

lemma "\<forall>(v, n, rule) \<in> set (iterate_norms gr []). v \<in> fst ` set gr"
  apply (induct rule: iterate_norms.induct)
  (* using iterate_norms.induct[of "\<lambda>gr norms. \<forall>(v, n, rule)\<in>set (iterate_norms gr norms). v \<in> fst ` set gr" gr "[]"] *)
  apply auto
sorry

(*****************************************************************************
  norms_of_grammar_new
 *****************************************************************************)

lemma nog_new_fst_is_gr_fst: "gram_normed gr \<Longrightarrow> map fst gr = map fst (norms_of_grammar_new gr)"
sorry


(*****************************************************************************
  minimal_word_of_variables
 *****************************************************************************)

termination minimal_word_of_variables
  apply (relation "measure (\<lambda>(gr, vs). norm_of_variables gr vs)", auto)
  apply (subst nov_distr')
  apply (auto simp add: add_commute add_strict_increasing2 nov_nog')
  apply (subst nov_distr')
by (auto simp add: nov_greater_zero)


lemma mwov_dist:
  assumes "gram_valid gr"
      and "set v1 \<subseteq> keys gr"
      and "set v2 \<subseteq> keys gr"
    shows "minimal_word_of_variables gr (v1 @ v2) =
           minimal_word_of_variables gr v1 @ minimal_word_of_variables gr v2" using assms
proof (induct v1 arbitrary: v2)
  case (Cons a v1)
  then show ?case by (case_tac "snd (of_key (norms_of_grammar gr) a)") auto
qed auto

lemma mwov_len_calcs_nov:
  assumes "gram_valid gr"
      and "set v \<subseteq> fst ` set gr"
    shows "length (minimal_word_of_variables gr v) = norm_of_variables gr v"
sorry

lemma mwov_empty:
  assumes "gram_valid gr"
      and "set v \<subseteq> fst ` set gr"
    shows "(minimal_word_of_variables gr v = []) = (v = [])"
sorry


(*****************************************************************************
  eat_word
 *****************************************************************************)

(* The output word of eat_word is a postfix of the input word. *)
lemma eat_word_postfix: "\<exists>p. w = p @ fst (eat_word gr w v)"
by (induct gr w v rule: eat_word.induct, auto simp add: prefix_helper Let_def split_if_eq1)

lemma eat_word_mwov':
  assumes "gram_valid gr"
      and "(v, prods) \<in> set gr"
      and "(t, vars) \<in> set prods"
      and "(t, vars) = snd (of_key (norms_of_grammar gr) v)"
    shows "eat_word gr (minimal_word_of_variables gr vars) vars = ([], [])" using assms
  apply (induct gr "(minimal_word_of_variables gr vars)" vars rule: eat_word.induct)
  apply (auto intro: mwov_empty)
  (* for last subgoal *)
  using mwov_empty[of gr] nog_in_rules'[of gr v prods] gram_rule_vars_in_fst
sorry

lemma eat_word_mwov:
  assumes G: "gram_valid gr"
      and V: "(v, prods) \<in> set gr"
      and T: "(t, vars) \<in> set prods"
      and "(t, vars) = snd (of_key (norms_of_grammar gr) v)"
    shows "eat_word gr (minimal_word_of_variables gr vars) (of_key (of_key gr v) t) = ([], [])"
proof -
  have 1: "of_key gr v = prods" using gram_alist[OF G] V of_key_from_existence[of gr v prods] by auto
  have "is_alist prods" using G V by (auto simp add: gram_valid_def is_typical_alist_def)
  then have "of_key prods t = vars" using T of_key_from_existence[of prods t vars] by auto
  then have "eat_word gr (minimal_word_of_variables gr vars) (of_key (of_key gr v) t) =
    eat_word gr (minimal_word_of_variables gr vars) vars" using 1 by auto
  then show ?thesis using assms by (auto simp add: eat_word_mwov')
qed


(*****************************************************************************
  word_in_variables
 *****************************************************************************)

(* Postfixfreeness *)
lemma postfix_free:
  assumes "gram_valid gr"
      and "word_in_variables gr w v"
      and "w' = w'h # w't"
    shows "\<not>(word_in_variables gr (w@w') v)" using assms
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)

(* Prefixfreeness *)
lemma prefix_free:
  assumes "gram_valid gr"
      and "w1 = w1h # w1t"
      and "w2 = w2h # w2t"
      and "w = w1 @ w2"
      and "word_in_variables gr w v"
    shows "\<not>(word_in_variables gr w1 v)"
using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)
  then show ?case
  proof (auto simp add: word_in_variables_def Let_def split_if_eq1)
    fix a
    assume a1: "gram_valid gr"
       and a2: "eat_word gr (w1t @ w2h # w2t) (of_key (of_key gr vh) a @ vt) = ([], [])"
       and a3: "eat_word gr w1t (of_key (of_key gr vh) a @ vt) = ([], [])"
    show "False" using a2 postfix_free[simplified word_in_variables_def, OF a1 a3] by simp
  qed
qed (auto simp add: word_in_variables_def)

lemma "eat_word gr w v1 = (p, []) \<Longrightarrow> word_in_variables gr p v2 \<Longrightarrow> word_in_variables gr w (v1 @ v2)"
oops

lemma "word_in_variables gr w (v1 @ v2) \<Longrightarrow> word_in_variables gr (fst (eat_word gr w v1)) v2"
by (induct gr w v1 rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


lemma wiv_no_variables_no_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) (auto simp add: word_in_variables_def)

lemma wiv_no_word_no_variables: "(word_in_variables gr [] v) = (v = [])"
by (case_tac v) (auto simp add: word_in_variables_def)

lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


lemma wiv_mwov_singleton:
  assumes "gram_valid gr"
      and "v \<in> keys gr"
      and "snd (of_key (norms_of_grammar gr) v) = (t, vars)"
    shows "word_in_variables gr (t # minimal_word_of_variables gr vars) [v]" using assms
proof -
  obtain rules where R: "(v, rules) \<in> set gr" using assms by auto
  have G: "is_alist gr" using assms by (simp add: gram_alist)
  have "(t, vars) \<in> set rules" using assms R by (auto intro: nog_in_rules)
  then have "t \<in> keys (of_key gr v)" using G R by (auto intro: of_key_predicate)
  then show ?thesis using assms by (auto simp add: word_in_variables_def eat_word_mwov nog_in_rules)
qed

lemma wiv_mwov:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> keys gr"
    shows "word_in_variables gr (minimal_word_of_variables gr v) v" using V
proof (induct v)
  case Nil then show ?case by (simp add: wiv_no_word_no_variables)
next
  case (Cons a v)
  assume A: "set (a # v) \<subseteq> keys gr"
  assume "(set v \<subseteq> keys gr \<Longrightarrow> word_in_variables gr (minimal_word_of_variables gr v) v)"
  then have H: "word_in_variables gr (minimal_word_of_variables gr v) v" using A by auto

  def R:  rule \<equiv> "snd (of_key (norms_of_grammar gr) a)"
  def T:     t \<equiv> "fst rule"
  def VS: vars \<equiv> "snd rule"

  have S: "word_in_variables gr (t # minimal_word_of_variables gr vars) [a]" using G A R T VS
    by (auto simp add: wiv_mwov_singleton)
  then show ?case using wiv_split[OF S H] G A R T VS
    by (case_tac "snd (of_key (norms_of_grammar gr) a)", auto)
qed

lemma mwov_minimal_wiv:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> keys gr" 
      and W: "word_in_variables gr w v"
    shows "length (minimal_word_of_variables gr v) \<le> length w" using V W unfolding word_in_variables_def
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)
  obtain rules where R: "rules = (of_key gr vh)" by simp
  assume I1: "(\<And>x. x = of_key gr vh \<Longrightarrow>
            th \<in> keys x \<Longrightarrow>
            set (of_key x th @ vt) \<subseteq> keys gr \<Longrightarrow>
            eat_word gr tt (of_key x th @ vt) = ([], []) \<Longrightarrow> length (minimal_word_of_variables gr (of_key x th @ vt)) \<le> length tt)"
  assume I2: "set (vh # vt) \<subseteq> keys gr"
  assume I3: "eat_word gr (th # tt) (vh # vt) = ([], [])"

  have T: "th \<in> keys rules" sorry
  then have 1: "eat_word gr tt (of_key rules th @ vt) = ([], [])" using R I3 by simp

  have "set (of_key rules th @ vt) \<subseteq> keys gr" using I2 gram_rule_vars_in_fst G R sorry
  then have "length (minimal_word_of_variables gr (of_key rules th @ vt)) \<le> length tt" using R T I1 1 by auto
  show ?case sorry
qed auto


(*****************************************************************************
  words_of_variables
 *****************************************************************************)

lemma mwov_in_wov:
  assumes "gram_valid gr"
      and "set v \<subseteq> keys gr"
    shows "minimal_word_of_variables gr v \<in> words_of_variables gr v" using assms
by (simp add: words_of_variables_def wiv_mwov)

lemma mwov_min_wov:
  assumes "gram_valid gr"
      and "set v \<subseteq> keys gr"
    shows "w \<in> words_of_variables gr v \<Longrightarrow> length (minimal_word_of_variables gr v) \<le> length w"
using assms by (auto simp add: words_of_variables_def mwov_minimal_wiv)


(*****************************************************************************
  norm
 *****************************************************************************)

lemma mwov_len_calcs_norm:
  assumes "gram_valid gr"
      and "set v \<subseteq> keys gr"
    shows "norm gr v = length (minimal_word_of_variables gr v)" using assms unfolding norm_def
by (auto intro: Least_equality simp add: mwov_min_wov mwov_in_wov)

theorem nov_calculates_norm:
  assumes "gram_valid gr"
      and "set v \<subseteq> keys gr"
    shows "norm_of_variables gr v = norm gr v" using assms
by (auto simp add: mwov_len_calcs_norm mwov_len_calcs_nov)

end
