theory Grammar imports
  "Grammar_defs"
  "Helpers"
begin


(*****************************************************************************
  gram_sd
 *****************************************************************************)

lemma gram_alist: "gram_sd gr \<Longrightarrow> is_alist gr"
by (simp add: gram_sd_def)

lemma gram_rules_alist: "gram_sd gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> is_alist rules"
unfolding gram_sd_def by auto

lemma gram_rule_vars_in_keys:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(t, vars) \<in> set rules"
    shows "set vars \<subseteq> keys gr" using assms
unfolding gram_sd_def by (metis (lifting) split_conv)


(*****************************************************************************
  norm_sum
 *****************************************************************************)

lemma ns_singleton: "norm_sum ns [v] = fst (lookup ns v)"
by (simp add: norm_sum_def)

lemma ns_distr: "norm_sum ns (x @ y) = norm_sum ns x + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_distr_cons: "norm_sum ns (x # y) = norm_sum ns [x] + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_empty: "norm_sum ns [] = 0"
by (simp add: norm_sum_def)


(*****************************************************************************
  norms_of_rules
 *****************************************************************************)

lemma nor_in_rules: "snd ` set (norms_of_rules norms rules) \<subseteq> set rules"
unfolding norms_of_rules_def by auto

lemma nor_nonempty:
  assumes "rules_have_norm norms rules"
    shows "norms_of_rules norms rules \<noteq> []"
using assms by (simp add: rules_have_norm_def norms_of_rules_def filter_empty_conv)

lemma nor_norms_greater_zero: "(n, rt, rv) \<in> set (norms_of_rules norms rules) \<Longrightarrow> 0 < n"
unfolding norms_of_rules_def by auto


(*****************************************************************************
  min_norm_of_rules
 *****************************************************************************)

lemma
  assumes "rules_have_norm norms rules"
    shows "min_norm_of_rules norms rules \<in> set (norms_of_rules norms rules)" using assms
unfolding min_norm_of_rules_def by (auto intro: Min_predicate simp add: nor_nonempty)

lemma mnor_in_rules:
  assumes "rules_have_norm norms rules"
    shows "snd (min_norm_of_rules norms rules) \<in> set rules" using assms
  unfolding min_norm_of_rules_def
by - (rule Min_predicate, auto simp add: nor_nonempty nor_in_rules sym[OF Set.image_subset_iff])

lemma mnor_norm_greater_zero:
  assumes "rules_have_norm norms rules"
    shows "0 < fst (min_norm_of_rules norms rules)" using assms unfolding min_norm_of_rules_def
by - (rule Min_predicate, auto simp add: nor_nonempty nor_norms_greater_zero)


(*****************************************************************************
  split_normable
 *****************************************************************************)

lemma sn_fst_have_norms:
  assumes "split_normable rest norms = (nb, unnb)"
      and "(v, rules) \<in> set nb"
    shows "rules_have_norm norms rules" using assms unfolding split_normable_def
by auto

lemma sn_fst_nil:
  assumes "split_normable rest norms = ([], unnb)"
    shows "unnb = rest" using assms
by (auto simp add: split_normable_def) (induct rest, auto)

lemma sn_fst_subset: "set (fst (split_normable rest norms)) \<subseteq> set rest"
unfolding split_normable_def partition_filter1 by (simp only: filter_is_subset)


(*****************************************************************************
  iterate_norms
 *****************************************************************************)

termination iterate_norms
apply (relation "measure (\<lambda>((*gr,*) rest, norms). length rest)", auto)
apply (auto simp only: split_normable_def partition_length add_less_cancel_right)
by (metis (full_types) impossible_Cons not_less)

lemma itno_induct [case_names Base Step]: "
  (\<And>unnb. split_normable rest norms = ([], unnb) \<Longrightarrow> P (iterate_norms (*gr*) rest norms)) \<Longrightarrow>
  (\<And>v rules nbtl unnb. split_normable rest norms = ((v, rules)#nbtl, unnb) \<Longrightarrow>
    P (iterate_norms (*gr*) (nbtl@unnb) ((v, min_norm_of_rules norms rules) # norms))) \<Longrightarrow>
  P (iterate_norms (*gr*) rest norms)"
by (case_tac "split_normable rest norms", case_tac "fst (split_normable rest norms)", auto)

(* TODO: remove after work! *)
thm iterate_norms.induct
thm list.induct

lemma itno_induct' [case_names Nil Cons Base]:
  assumes N: "\<And>rest norms unnb.
                P (rest, norms) \<Longrightarrow> split_normable rest norms = ([], unnb) \<Longrightarrow> P (unnb, norms)"
      and C: "\<And>rest norms v rules nbtl unnb.
                P (rest, norms) \<Longrightarrow> split_normable rest norms = ((v, rules)#nbtl, unnb) \<Longrightarrow>
                P ((nbtl@unnb), ((v, min_norm_of_rules norms rules) # norms))"
      and P: "P (rest, norms)"
  shows "P (iterate_norms rest norms)"
proof (cases "split_normable rest norms")
  case (Pair nb unnb)
  then show ?thesis
    proof (cases nb)
      case Nil then show ?thesis using N P Pair by auto
    next
      case (Cons nbh nbt)
      then show ?thesis using C P Pair
        apply (induct _ rest norms rule: iterate_norms.induct)
        apply (auto simp del: iterate_norms.simps)
      sorry
    qed
qed


lemma itno_conserves_keys: 
  "keys gr \<subseteq> keys (fst (iterate_norms gr [])) \<union> keys (snd (iterate_norms gr []))"
proof (intro subsetI, induct rule: itno_induct')
  case (Nil rest _ unnb)
  then have "rest = unnb" using sn_fst_nil by auto
  then show ?case using Nil by simp
next
  case (Cons rest norms v rules nbtl unnb)
  then show ?case sorry
qed auto


(*****************************************************************************
  gram_nsd
 *****************************************************************************)

lemma gram_nsd_sd: "gram_nsd gr \<Longrightarrow> gram_sd gr"
by (simp add: gram_nsd_def)


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma nog_mnor:
  assumes "gram_nsd gr"
      and "(v, rules) \<in> set gr"
    shows "lookup (norms_of_grammar gr) v = min_norm_of_rules (norms_of_grammar gr) rules"
sorry

lemma nog_has_norms:
  assumes "gram_nsd gr"
      and "(v, rules) \<in> set gr"
    shows "rules_have_norm (norms_of_grammar gr) rules" using assms
sorry

lemma nog_in_rules:
  assumes "gram_nsd gr"
      and "(v, rules) \<in> set gr"
    shows "snd (lookup (norms_of_grammar gr) v) \<in> set rules" using assms
by (auto simp add: nog_mnor nog_has_norms mnor_in_rules)


(*lemma nog_invariant:
  assumes "norms_correct gr rest norms"
  shows "norms_correct gr rest (fst (iterate_norms gr rest norms))"
sorry*)

lemma (*itno_fst_subset_gr:*) "gram_sd gr \<Longrightarrow> set (fst (iterate_norms gr [])) \<subseteq> set gr"
proof (induct rule: itno_induct')
  case (Nil rest norms unnb)
  then show ?case using sn_fst_nil by auto
next
  case (Cons rest norms v rules nbtl unnb)
  have "set (fst (split_normable rest norms)) \<subseteq> set rest" by (rule sn_fst_subset)
  then have "set ((v, rules) # nbtl) \<subseteq> set rest" using Cons by simp
  then show ?case using Cons by (auto simp add: split_normable_def)
qed auto

lemma (*nog_alist:*) "gram_sd gr \<Longrightarrow> is_alist (norms_of_grammar gr)" unfolding norms_of_grammar_def
proof (induct rule: itno_induct')
  case (Cons rest norms v rules nbtl unnb)
  then show ?case sorry
qed (auto)

lemma (*nog_valid:*) "v \<in> keys (norms_of_grammar gr) \<Longrightarrow> v \<in> keys gr"
sorry

lemma nog_complete:
  assumes "gram_nsd gr"
    shows "keys gr \<subseteq> keys (norms_of_grammar gr)"
proof -
  have "fst (iterate_norms gr []) = []" using assms unfolding gram_nsd_def gram_normed_fun_def
    by simp
  then show ?thesis using itno_conserves_keys[of gr] by (simp add: norms_of_grammar_def)
qed

lemma nog_norms_greater_zero: "(v, n, rt, rv) \<in> set (norms_of_grammar gr) \<Longrightarrow> 0 < n"
  unfolding norms_of_grammar_def
proof (induct rule: itno_induct')
  case (Cons rest norms va rules nbtl unnb)
  then show ?case
  proof (cases "v = va")
    case True
    then have "rules_have_norm norms rules"
      using Cons sn_fst_have_norms[of _ _ "(va, rules) # nbtl" unnb _ _] by auto
    then have "0 < fst (min_norm_of_rules norms rules)" using mnor_norm_greater_zero by auto
    then show ?thesis using Cons fst_predicate[of _ "min_norm_of_rules norms rules"] by auto
  qed auto
qed auto

lemma nog_greater_zero_lookup:
  "gram_nsd gr \<Longrightarrow> v \<in> keys gr \<Longrightarrow> 0 < fst (lookup (norms_of_grammar gr) v)"
  apply (rule lookup_forall[of "norms_of_grammar gr"])
using nog_complete nog_norms_greater_zero[of _ _ _ _ gr] by auto


(*****************************************************************************
  norm_of_variables
 *****************************************************************************)

lemma nov_distr: "norm_of_variables gr (x @ y) = norm_of_variables gr x + norm_of_variables gr y"
by (simp add: norm_of_variables_def ns_distr)

lemma nov_distr_cons:
  "norm_of_variables gr (x # y) = norm_of_variables gr [x] + norm_of_variables gr y"
by (rule nov_distr[of _ "[x]", simplified])

lemma nov_singleton: "norm_of_variables gr [v] = fst (lookup (norms_of_grammar gr) v)"
by (simp add: norm_of_variables_def ns_singleton)

lemma nov_nog':
  assumes "gram_nsd gr"
      and "(t, vs) = snd (lookup (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]" using assms
sorry

lemma nov_greater_zero:
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
      and "v \<noteq> []"
    shows "0 < norm_of_variables gr v" using assms unfolding norm_of_variables_def
by (induct v) (auto, subst ns_distr_cons, simp add: ns_singleton nog_greater_zero_lookup)

lemma nov_empty: "norm_of_variables gr [] = 0"
by (simp add: norm_of_variables_def ns_empty)


(*****************************************************************************
  minimal_word_of_variables
 *****************************************************************************)

termination minimal_word_of_variables
  apply (relation "measure (\<lambda>(gr, vs). norm_of_variables gr vs)", auto)
  apply (subst nov_distr_cons)
  apply (auto simp add: add_commute add_strict_increasing2 nov_nog')
  apply (subst nov_distr_cons)
by (auto simp add: nov_greater_zero)

lemmas mwov_induct = minimal_word_of_variables.induct[case_names Nil_vars Cons_vars]

lemma mwov_dist:
  assumes "gram_nsd gr"
      and "set v1 \<subseteq> keys gr"
      and "set v2 \<subseteq> keys gr"
    shows "minimal_word_of_variables gr (v1 @ v2) =
           minimal_word_of_variables gr v1 @ minimal_word_of_variables gr v2" using assms
proof (induct v1 arbitrary: v2)
  case (Cons a v1)
  then show ?case by (case_tac "snd (lookup (norms_of_grammar gr) a)") auto
qed auto

lemma mwov_len_calcs_nog:
  assumes "gram_nsd gr"
      and "v \<in> keys gr"
      and "(n, nt, nrt) = lookup (norms_of_grammar gr) v"
    shows "Suc (length (minimal_word_of_variables gr nrt)) = n" using assms
sorry

theorem mwov_len_calcs_nov:
  assumes G: "gram_nsd gr"
      and V: "set v \<subseteq> fst ` set gr"
    shows "length (minimal_word_of_variables gr v) = norm_of_variables gr v" using assms
proof (induct gr v rule: mwov_induct)
  case (Cons_vars gr vh vt)

  def nogh \<equiv> "lookup (norms_of_grammar gr) vh"
  def nh   \<equiv> "fst nogh"
  def trh  \<equiv> "snd nogh"
  def th   \<equiv> "fst trh"
  def rh   \<equiv> "snd trh"

  have TR: "(th, rh) = trh" using th_def rh_def by simp
  have NO: "(nh, th, rh) = nogh" using nogh_def nh_def th_def rh_def trh_def by simp

  have VH: "vh \<in> keys gr" using Cons_vars by simp
  have VS: "set [vh] \<subseteq> keys gr" using Cons_vars by simp
  have VT: "set vt \<subseteq> keys gr" using Cons_vars by simp

  have IH: "length (minimal_word_of_variables gr vt) = norm_of_variables gr vt"
    using TR Cons_vars trh_def nogh_def by simp

  have MD: "minimal_word_of_variables gr ([vh] @ vt) =
    minimal_word_of_variables gr [vh] @ minimal_word_of_variables gr vt"
    using mwov_dist Cons_vars(3) VS VT .
  have ND: "norm_of_variables gr (vh # vt) = norm_of_variables gr [vh] + norm_of_variables gr vt"
    using nov_distr_cons by auto

  have "Suc (length (minimal_word_of_variables gr rh)) = nh"
    using mwov_len_calcs_nog[OF Cons_vars(3) VH NO[simplified nogh_def]] .

  then have "length (minimal_word_of_variables gr [vh]) = norm_of_variables gr [vh]"
    using Cons_vars(3-4)
    by (case_tac trh) (auto simp add: rh_def nogh_def nh_def trh_def nov_singleton)

  then show ?case using MD ND IH by simp
qed (simp add: nov_empty)

lemma mwov_empty:
  assumes "gram_nsd gr"
      and "set v \<subseteq> fst ` set gr"
      and "minimal_word_of_variables gr v = []"
    shows "v = []" using assms
proof (induct v)
  case (Cons a v)
  then show ?case by (case_tac "snd (lookup (norms_of_grammar gr) a)") auto
qed auto

lemma mwov_length_singleton:
  assumes "gram_nsd gr"
      and "(vh, rules) \<in> set gr"
      and "(th, rth) \<in> set rules"
    shows "length (minimal_word_of_variables gr [vh]) \<le>
       1 + length (minimal_word_of_variables gr rth)" using assms
  apply (case_tac "snd (lookup (norms_of_grammar gr) vh)")
  apply auto
sorry

lemma mwov_length:
  assumes G: "gram_nsd gr"
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
    using mwov_dist G gram_rule_vars_in_keys[OF gram_nsd_sd[OF G] V R] T .

  show ?thesis using L D1 D2 by auto
qed

lemma mwov_hd_from_nog:
  assumes "gram_nsd gr"
      and "(vh, rules) \<in> set gr"
      and "set vt \<subseteq> keys gr"
      and "th # tt = minimal_word_of_variables gr (vh # vt)"
    shows "th = fst (snd (lookup (norms_of_grammar gr) vh))" using assms
by (case_tac "snd (lookup (norms_of_grammar gr) vh)") auto

lemma mwov_prefix:
  assumes G: "gram_nsd gr"
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

  have GS: "gram_sd gr" using G by (rule gram_nsd_sd)
  have TN: "(th, nrth) \<in> set rules" using nog_in_rules[OF G V] SL by simp
  have LO: "lookup rules th = nrth"
    using lookup_from_existence gram_rules_alist[OF GS V] TN .

  have "is_alist rules" using gram_rules_alist GS V .
  then have "(th, rth) \<in> set rules" using TN rth_def by (auto simp add: existence_from_lookup)
  then have RT: "set rth \<subseteq> keys gr" using gram_rule_vars_in_keys GS V by simp

  show ?thesis using assms SL LO rth_def mwov_dist[OF G RT S] by auto
qed


(*****************************************************************************
  word_in_variables
 *****************************************************************************)

lemmas eat_word_induct = eat_word.induct[case_names normal nil_word nil_vars]

(* Postfixfreeness *)
lemma wiv_postfix_free:
  assumes "gram_sd gr"
      and "word_in_variables gr w v"
      and "w' = w'h # w't"
    shows "\<not>(word_in_variables gr (w@w') v)" using assms
by (induct gr w v rule: eat_word_induct, auto simp add: word_in_variables_def Let_def)

(* Prefixfreeness *)
lemma wiv_prefix_free:
  assumes "gram_sd gr"
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
by (induct gr w v rule: eat_word_induct, auto simp add: word_in_variables_def Let_def split_if_eq1)

lemma wiv_prefix:
  assumes G: "gram_sd gr"
      and V: "(vh, rules) \<in> set gr"
      and T: "(th, rth) \<in> set rules"
    shows "word_in_variables gr (th#tt) (vh#vt) = word_in_variables gr tt (rth @ vt)"
proof -
  have 1: "lookup gr vh = rules" using lookup_from_existence gram_alist[OF G] V .
  have 2: "lookup rules th = rth" using lookup_from_existence gram_rules_alist[OF G V] T .
  show ?thesis using assms 1 2 unfolding word_in_variables_def by auto
qed

lemma wiv_mwov:
  assumes G: "gram_nsd gr"
      and V: "set v \<subseteq> keys gr"
    shows "word_in_variables gr (minimal_word_of_variables gr v) v" using assms
proof (induct gr "(minimal_word_of_variables gr v)" v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"
  def  nrth \<equiv> "snd (snd (lookup (norms_of_grammar gr) vh))"

  have GS: "gram_sd gr" using normal by (simp add: gram_nsd_sd)
  have VT: "set vt \<subseteq> keys gr" using normal(4) by simp
  have VR: "(vh, rules) \<in> set gr" using gram_alist[OF GS] normal rules_def
    by (simp add: existence_from_lookup)
  have RA: "is_alist rules" using gram_rules_alist GS VR .

  have "th = fst (snd (lookup (norms_of_grammar gr) vh))"
    using mwov_hd_from_nog normal(3) VR VT normal(2) .
  then have TN: "(th, nrth) = snd (lookup (norms_of_grammar gr) vh)" using nrth_def by simp
  have TH: "th \<in> keys rules" using nog_in_rules [OF normal(3) VR] sym[OF TN] by simp

  have TT: "tt = minimal_word_of_variables gr (rth @ vt)" unfolding rth_def
    using mwov_prefix normal(3) VR VT normal(2) .
  have TR: "(th, rth) \<in> set rules" using RA TH rth_def by (simp add: existence_from_lookup)
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gram_rule_vars_in_keys[OF GS VR TR]
    by simp

  show ?case using normal GS VR TR TT TH RV rules_def rth_def by (simp add: sym[OF wiv_prefix])
qed (auto simp add: word_in_variables_def mwov_empty)

lemma wiv_word_head: "word_in_variables gr (th # tt) (vh # vt) \<Longrightarrow> th \<in> keys (lookup gr vh)"
by (case_tac "th \<in> keys (lookup gr vh)") (auto simp add: Let_def word_in_variables_def)

lemma mwov_minimal_wiv:
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
      and "word_in_variables gr w v"
    shows "length (minimal_word_of_variables gr v) \<le> length w" using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"

  have GS: "gram_sd gr" using normal by (simp add: gram_nsd_sd)
  have VR: "(vh, rules) \<in> set gr" using GS normal rules_def
    by (simp add: existence_from_lookup gram_alist)
  have RA: "is_alist rules" using gram_rules_alist GS VR .

  have TH: "th \<in> keys rules" using normal rules_def wiv_word_head by simp
  have TR: "(th, rth) \<in> set rules" using rth_def RA TH by (simp add: existence_from_lookup)

  have VT: "set vt \<subseteq> keys gr" using normal by simp
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gram_rule_vars_in_keys[OF GS VR TR] by auto

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
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
    shows "minimal_word_of_variables gr v \<in> words_of_variables gr v" using assms
by (simp add: words_of_variables_def wiv_mwov)

lemma mwov_min_wov:
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
    shows "w \<in> words_of_variables gr v \<Longrightarrow> length (minimal_word_of_variables gr v) \<le> length w"
using assms by (auto simp add: words_of_variables_def mwov_minimal_wiv)


(*****************************************************************************
  norm
 *****************************************************************************)

theorem mwov_len_calcs_norm:
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
    shows "norm gr v = length (minimal_word_of_variables gr v)" using assms unfolding norm_def
by (auto intro: Least_equality simp add: mwov_min_wov mwov_in_wov)

theorem nov_calculates_norm:
  assumes "gram_nsd gr"
      and "set v \<subseteq> keys gr"
    shows "norm_of_variables gr v = norm gr v" using assms
by (auto simp add: mwov_len_calcs_norm mwov_len_calcs_nov)

end
