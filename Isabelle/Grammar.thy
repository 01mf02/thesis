theory Grammar imports
  "Grammar_defs"
  "Helpers"
begin

(*****************************************************************************
  gram_valid
 *****************************************************************************)

lemma gram_alist: "gram_valid gr \<Longrightarrow> is_alist gr"
by (simp add: gram_valid_def is_typical_alist_def)

lemma gram_rules_alist: "gram_valid gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> is_alist rules"
unfolding gram_valid_def is_typical_alist_def by auto

lemma gram_rule_vars_in_keys:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(t, vars) \<in> set rules"
    shows "set vars \<subseteq> keys gr" using assms
unfolding gram_valid_def by (metis (lifting) split_conv)


(*****************************************************************************
  norm_sum
 *****************************************************************************)

lemma ns_singleton: "norm_sum ns [v] = fst (lookup ns v)"
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
    shows "lookup (norms_of_grammar gr) v = min_norm_of_rules (norms_of_grammar gr) rules" using assms
  apply -
  apply (rule lookup_from_existence)
  apply (simp add: nog_alist)
sorry

lemma nog_sufficient:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "norms_sufficient (norms_of_grammar gr) rules"
sorry

lemma nog_in_rules:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "snd (lookup (norms_of_grammar gr) v) \<in> set rules" using assms
by (auto simp add: nog_mnor mnor_in_rules nog_sufficient)


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
  have "norm_of_variables gr [v] = fst (lookup (norms_of_grammar gr) v)"
    by (simp add: norm_of_variables_def norm_sum_def)
  also have "... = fst (n, t, vs)" using assms by (simp_all add: lookup_from_existence nog_alist)
  finally show ?thesis by simp
qed

lemma nov_nog:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(t, vs) = snd (lookup (norms_of_grammar gr) v)"
    shows "norm_of_variables gr [v] = Suc (norm_of_variables gr vs)"
proof (simp add: norm_of_variables_def norm_sum_def)
  have "(lookup (norms_of_grammar gr) v) = min_norm_of_rules (norms_of_grammar gr) rules" sorry
  then show "fst (lookup (norms_of_grammar gr) v) = Suc(listsum (map (fst \<circ> lookup (norms_of_grammar gr)) vs))" sorry
qed

lemma nov_nog':
  assumes "gram_valid gr"
      and "(t, vs) = snd (lookup (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]" using assms
by (auto simp add: nov_nog)

lemma nov_greater_zero: "gram_valid gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> 0 < norm_of_variables gr [v]"
sorry

lemma nov_empty: "norm_of_variables gr [] = 0"
by (simp add: norm_of_variables_def norm_sum_def)


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
  then show ?case by (case_tac "snd (lookup (norms_of_grammar gr) a)") auto
qed auto

lemma mwov_len_calcs_nog:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, nt, nrt) \<in> set (norms_of_grammar gr)"
    shows "Suc (length (minimal_word_of_variables gr nrt)) = n"
sorry

theorem mwov_len_calcs_nov:
  assumes "gram_valid gr"
      and "set v \<subseteq> fst ` set gr"
    shows "length (minimal_word_of_variables gr v) = norm_of_variables gr v" using assms
  apply (induct v)
  apply (auto simp add: nov_empty)
  apply (case_tac "snd (lookup (norms_of_grammar gr) aa)")
  apply auto
  apply (subst nov_distr')
  apply (simp only: sym[OF Nat.plus_nat.add_Suc])
  apply auto
  (* TODO: use nov_singleton *)
  using nov_singleton mwov_len_calcs_nog
sorry

lemma mwov_empty:
  assumes "gram_valid gr"
      and "set v \<subseteq> fst ` set gr"
      and "minimal_word_of_variables gr v = []"
    shows "v = []" using assms
proof (induct v)
  case (Cons a v)
  then show ?case by (case_tac "snd (lookup (norms_of_grammar gr) a)") auto
qed auto

lemma mwov_length_singleton:
  assumes "gram_valid gr"
      and "(vh, rules) \<in> set gr"
      and "(th, rth) \<in> set rules"
    shows "length (minimal_word_of_variables gr [vh]) \<le>
       1 + length (minimal_word_of_variables gr rth)" using assms
  apply (case_tac "snd (lookup (norms_of_grammar gr) vh)")
  apply auto
sorry

lemma mwov_length:
  assumes G: "gram_valid gr"
      and T: "set vt \<subseteq> keys gr"
      and V: "(vh, rules) \<in> set gr"
      and R: "(th, rth) \<in> set rules"
    shows "length (minimal_word_of_variables gr (vh # vt)) \<le>
       1 + length (minimal_word_of_variables gr (rth @ vt))"
proof -
  have VH: "set [vh] \<subseteq> keys gr" using V by auto

  have L: "length (minimal_word_of_variables gr [vh]) \<le>
       1 + length (minimal_word_of_variables gr rth)" using mwov_length_singleton G V R  .
  have D1: "minimal_word_of_variables gr ([vh] @ vt) =
            minimal_word_of_variables gr [vh] @ minimal_word_of_variables gr vt"
    using mwov_dist G VH T .
  have D2: "minimal_word_of_variables gr (rth @ vt) =
            minimal_word_of_variables gr rth @ minimal_word_of_variables gr vt"
    using mwov_dist G gram_rule_vars_in_keys[OF G V R] T .
  
  show ?thesis using L D1 D2 by auto
qed

lemma mwov_hd_from_nog:
  assumes "gram_valid gr"
      and "(vh, rules) \<in> set gr"
      and "set vt \<subseteq> keys gr"
      and "th # tt = minimal_word_of_variables gr (vh # vt)"
    shows "th = fst (snd (lookup (norms_of_grammar gr) vh))" using assms
by (case_tac "snd (lookup (norms_of_grammar gr) vh)") auto

lemma mwov_prefix:
  assumes G: "gram_valid gr"
      and V: "(vh, rules) \<in> set gr"
      and S: "set vt \<subseteq> keys gr"
      and M: "th # tt = minimal_word_of_variables gr (vh # vt)"
    shows "tt = minimal_word_of_variables gr ((lookup rules th) @ vt)"
proof -
  def rth  \<equiv> "lookup rules th"
  def nvh  \<equiv> "snd (lookup (norms_of_grammar gr) vh)"
  def nth  \<equiv> "fst nvh"
  def nrth \<equiv> "snd nvh"

  have "th = nth" using assms by (auto simp add: nth_def nvh_def mwov_hd_from_nog)
  then have SL: "snd (lookup (norms_of_grammar gr) vh) = (th, nrth)"
    using nvh_def nrth_def nth_def by auto

  have TN: "(th, nrth) \<in> set rules" using nog_in_rules[OF G V] SL by simp
  have LO: "lookup rules th = nrth" using lookup_from_existence gram_rules_alist[OF G V] TN .

  have "is_alist rules" using gram_rules_alist G V .
  then have "(th, rth) \<in> set rules" using TN rth_def by (auto simp add: existence_from_lookup)
  then have RT: "set rth \<subseteq> keys gr" using gram_rule_vars_in_keys G V by simp

  show ?thesis using assms SL LO rth_def mwov_dist[OF G RT S] by auto
qed


(*****************************************************************************
  word_in_variables
 *****************************************************************************)

(* Postfixfreeness *)
lemma wiv_postfix_free:
  assumes "gram_valid gr"
      and "word_in_variables gr w v"
      and "w' = w'h # w't"
    shows "\<not>(word_in_variables gr (w@w') v)" using assms
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def)

(* Prefixfreeness *)
lemma wiv_prefix_free:
  assumes "gram_valid gr"
      and "w1 = w1h # w1t"
      and "w2 = w2h # w2t"
      and "w = w1 @ w2"
      and "word_in_variables gr w v"
    shows "\<not>(word_in_variables gr w1 v)"
using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)
  have "word_in_variables gr w1 (vh#vt) \<Longrightarrow> False"
  proof -
    assume CD: "word_in_variables gr w1 (vh#vt)"
    show ?thesis using normal wiv_postfix_free[OF normal(2) CD normal(4)] by auto
  qed
  then show ?case by auto
qed (auto simp add: word_in_variables_def)

lemma wiv_no_variables_no_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) (auto simp add: word_in_variables_def)

lemma wiv_no_word_no_variables: "(word_in_variables gr [] v) = (v = [])"
by (case_tac v) (auto simp add: word_in_variables_def)

lemma wiv_split:
  assumes "word_in_variables gr w  v"
      and "word_in_variables gr w' v'"
    shows "word_in_variables gr (w@w') (v@v')" using assms
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)

lemma wiv_prefix:
  assumes G: "gram_valid gr"
      and V: "(vh, rules) \<in> set gr"
      and T: "(th, rth) \<in> set rules"
    shows "word_in_variables gr (th#tt) (vh#vt) = word_in_variables gr tt (rth @ vt)"
proof -
  have 1: "lookup gr vh = rules" using lookup_from_existence gram_alist[OF G] V .
  have 2: "lookup rules th = rth" using lookup_from_existence gram_rules_alist[OF G V] T .
  show ?thesis using assms 1 2 unfolding word_in_variables_def by auto
qed

lemma wiv_mwov:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> keys gr"
    shows "word_in_variables gr (minimal_word_of_variables gr v) v" using assms
proof (induct gr "(minimal_word_of_variables gr v)" v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"
  def  nrth \<equiv> "snd (snd (lookup (norms_of_grammar gr) vh))"

  have VT: "set vt \<subseteq> keys gr" using normal(4) by simp
  have VR: "(vh, rules) \<in> set gr" using gram_alist[OF normal(3)] normal rules_def
    by (simp add: existence_from_lookup)
  have RA: "is_alist rules" using gram_rules_alist normal(3) VR .

  have "th = fst (snd (lookup (norms_of_grammar gr) vh))"
    using mwov_hd_from_nog normal(3) VR VT normal(2) .
  then have TN: "(th, nrth) = snd (lookup (norms_of_grammar gr) vh)" using nrth_def by simp
  have TH: "th \<in> keys rules" using nog_in_rules [OF normal(3) VR] sym[OF TN] by simp

  have TT: "tt = minimal_word_of_variables gr (rth @ vt)" unfolding rth_def
    using mwov_prefix normal(3) VR VT normal(2) .
  have TR: "(th, rth) \<in> set rules" using RA TH rth_def by (simp add: existence_from_lookup)
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gram_rule_vars_in_keys[OF normal(3) VR TR]
    by simp

  show ?case using normal VR TR TT TH RV rules_def rth_def by (simp add: sym[OF wiv_prefix])
qed (auto simp add: word_in_variables_def mwov_empty)

lemma wiv_word_head: "word_in_variables gr (th # tt) (vh # vt) \<Longrightarrow> th \<in> keys (lookup gr vh)"
by (case_tac "th \<in> keys (lookup gr vh)") (auto simp add: Let_def word_in_variables_def)

lemma mwov_minimal_wiv:
  assumes "gram_valid gr"
      and "set v \<subseteq> keys gr" 
      and "word_in_variables gr w v"
    shows "length (minimal_word_of_variables gr v) \<le> length w" using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"

  have VR: "(vh, rules) \<in> set gr" using normal rules_def
    by (simp add: existence_from_lookup gram_alist)
  have RA: "is_alist rules" using gram_rules_alist normal(2) VR .

  have TH: "th \<in> keys rules" using rules_def normal wiv_word_head by simp
  have TR: "(th, rth) \<in> set rules" using rth_def RA TH by (simp add: existence_from_lookup)

  have VT: "set vt \<subseteq> keys gr" using normal by simp
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gram_rule_vars_in_keys[OF normal(2) VR TR]
    by auto

  have "length (minimal_word_of_variables gr (vh # vt)) \<le>
    1 + length (minimal_word_of_variables gr (rth @ vt))" using mwov_length normal(2) VT VR TR .
  also have "... \<le> length (th # tt)" using normal rules_def rth_def RV TH
    by (auto simp add: word_in_variables_def)
  finally show ?case .
qed (auto simp add: word_in_variables_def)


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

theorem mwov_len_calcs_norm:
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
