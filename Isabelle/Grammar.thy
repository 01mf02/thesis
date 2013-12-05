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

lemma ns_norms_superset_equal:
  assumes "set vs \<subseteq> keys norms"
      and "is_alist norms"
      and "is_alist norms'"
      and "set norms \<subseteq> set norms'"
    shows "norm_sum norms vs = norm_sum norms' vs"
proof -
  have "map (fst \<circ> lookup norms) vs = map (fst \<circ> lookup norms') vs"
    using alist_superset_lookup_equal[OF assms(1-4)] by auto
  then show ?thesis unfolding norm_sum_def by metis
qed


(*****************************************************************************
  rules_have_norm
 *****************************************************************************)

lemma rhn_concat: "rules_have_norm norms rules \<Longrightarrow> rules_have_norm (norms @ x) rules"
by (induct x) (auto simp add: rules_have_norm_def rule_has_norm_def)


(*****************************************************************************
  norms_of_rules
 *****************************************************************************)

lemma nor_in_rules: "snd ` set (norms_of_rules norms rules) \<subseteq> set rules"
unfolding norms_of_rules_def by auto

lemma nor_nonempty:
  assumes "rules_have_norm norms rules"
    shows "norms_of_rules norms rules \<noteq> []"
using assms by (simp add: rules_have_norm_def norms_of_rules_def filter_empty_conv)

lemma nor_nonempty_cons:
  assumes "rules_have_norm norms rules"
    shows "norms_of_rules (nh # norms) rules \<noteq> []" using assms
by (auto simp add: rules_have_norm_def norms_of_rules_def filter_empty_conv rule_has_norm_def)

lemma nor_norms_greater_zero: "(n, rt, rv) \<in> set (norms_of_rules norms rules) \<Longrightarrow> 0 < n"
unfolding norms_of_rules_def by auto

lemma nor_variables:
  assumes "(n, t, vs) \<in> set (norms_of_rules norms rules)"
    shows "set vs \<subseteq> keys norms"
      and "norm_sum norms vs < n" using assms
unfolding norms_of_rules_def rule_has_norm_def by auto


(*****************************************************************************
  min_norm_of_rules
 *****************************************************************************)

lemma mnor_in_nor:
  assumes "rules_have_norm norms rules"
    shows "min_norm_of_rules norms rules \<in> set (norms_of_rules norms rules)" using assms
unfolding min_norm_of_rules_def by (auto intro: Min_predicate simp add: nor_nonempty)

lemma mnor_in_rules:
  assumes "rules_have_norm norms rules"
    shows "snd (min_norm_of_rules norms rules) \<in> set rules" using assms
  unfolding min_norm_of_rules_def
by - (rule Min_predicate, auto simp add: nor_nonempty nor_in_rules Set.image_subset_iff[symmetric])

lemma mnor_norm_greater_zero:
  assumes "rules_have_norm norms rules"
    shows "0 < fst (min_norm_of_rules norms rules)" using assms unfolding min_norm_of_rules_def
by - (rule Min_predicate, auto simp add: nor_nonempty nor_norms_greater_zero)

lemma mnor_variables:
  assumes "rules_have_norm norms rules"
      and "(n, t, vs) = min_norm_of_rules norms rules"
    shows "set vs \<subseteq> keys norms"
      and "norm_sum norms vs < n"
by (metis assms(1) assms(2) mnor_in_nor nor_variables(1))
   (metis assms(1) assms(2) mnor_in_nor nor_variables(2))


(*****************************************************************************
  iterate_norms
 *****************************************************************************)

definition itno_invariant where
  "itno_invariant gr norms rest \<equiv>
     set rest \<subseteq> set gr (*\<and> keys gr = keys norms \<union> keys rest *)"

lemma itno_induct [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                P (norms, rest) \<Longrightarrow> partition (itno_p norms) rest = (yes, no) \<Longrightarrow>
                P (itno_f norms yes, no)"
  shows "P (iterate_norms gr)"
    and "itno_invariant gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
  unfolding iterate_norms_def
proof (induct rule: pi_induct)
  case Base
    case 1 show ?case using B by auto
    case 2 show ?case unfolding itno_invariant_def by auto
next
  case (Step norms rest yes no)
    case 1 show ?case using S Step by auto
    case 2
      have I1: "set no \<subseteq> set gr" using Step unfolding itno_invariant_def by auto
      show ?case using I1 unfolding itno_invariant_def by auto
qed

definition itno_invariant_sd where
  "itno_invariant_sd gr norms rest \<equiv> is_alist norms \<and> is_alist rest \<and> keys rest \<inter> keys norms = {}"

lemma itno_induct_sd [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                itno_invariant_sd gr norms rest \<Longrightarrow>
                P (norms, rest) \<Longrightarrow> partition (itno_p norms) rest = (yes, no) \<Longrightarrow>
                P (itno_f norms yes, no)"
      and G: "gram_sd gr"
  shows "P (iterate_norms gr)"
    and "itno_invariant_sd gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
proof (induct rule: itno_induct(1))
  case Base
    case 1 show ?case using B by auto
    case 2 show ?case unfolding itno_invariant_sd_def using gram_alist[OF G] by auto
next
  case (Step norms rest yes no)
    case 1 show ?case using S Step by auto
    case 2

    have I: "is_alist norms" "is_alist rest" "keys rest \<inter> keys norms = {}" using Step(3)
      unfolding itno_invariant_sd_def by auto

    have NM: "keys norms \<inter> keys (mnor_map norms yes) = {}" using Step(4) I(3)
      unfolding mnor_map_def by force
    have AY: "is_alist (mnor_map norms yes)" using alist_filter alist_map Step(4) I(2)
      unfolding mnor_map_def by auto
    have I1: "is_alist (itno_f norms yes)" using I(1) AY NM alist_distr[of norms]
      unfolding itno_f_def by auto

    have AC: "is_alist (yes @ no)" using alist_partition_distr[OF I(2) Step(4)[symmetric]] .
    then have I2: "is_alist no" using alist_distr[of yes] by simp
    
    have NN: "keys no \<inter> keys norms = {}" using Step(4) I(3) by force
    have MN: "keys no \<inter> keys (mnor_map norms yes) = {}" unfolding mnor_map_def
      using AC alist_distr[of yes no] by auto
    have I3: "keys no \<inter> keys (itno_f norms yes) = {}" using NN MN unfolding itno_f_def by auto

    show ?case using Step unfolding itno_invariant_sd_def using I1 I2 I3 by auto
qed

definition itno_invariant_sd_nin where
  "itno_invariant_sd_nin norms rules n t vs \<equiv>
     rules_have_norm norms rules \<and> (n, t, vs) = min_norm_of_rules norms rules"

lemma itno_induct_sd_in [case_names Step]:
  assumes "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                itno_invariant_sd gr norms rest \<Longrightarrow>
                ((v, n, t, vs) \<notin> set norms \<Longrightarrow> itno_invariant_sd_nin norms rules n t vs) \<Longrightarrow>
                ((v, n, t, vs) \<in> set norms \<Longrightarrow> P (norms, rest)) \<Longrightarrow>
                partition (itno_p norms) rest = (yes, no) \<Longrightarrow>
                P (itno_f norms yes, no)"
      and "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
  shows "P (iterate_norms gr)" using assms(4) unfolding norms_of_grammar_def
proof (induct rule: itno_induct_sd(1))
  case Base then show ?case by auto
next
  case (Step norms rest yes no) show ?case
  proof (cases "(v, n, t, vs) \<in> set norms")
    case True then show ?thesis using assms(1) Step by auto
  next
    case False

    have I: "set rest \<subseteq> set gr" "is_alist rest"
      using Step(1-2) unfolding itno_invariant_def itno_invariant_sd_def by auto
    have YG: "set yes \<subseteq> set gr" using Step(4) I(1) by auto

    have AG: "is_alist gr" using gram_alist assms(2) by auto
    have AY: "is_alist yes" using alist_partition_distr[OF I(2) Step(4)[symmetric]] alist_distr
      by auto

    have VM: "(v, n, t, vs) \<in> set (mnor_map norms yes)" using False Step(5)
      unfolding itno_f_def by auto
    then have VY: "(v, rules) \<in> set yes" using alist_values_equal[OF AG assms(3)] YG
      unfolding mnor_map_def by auto
    then have R: "rules_have_norm norms rules" using Step(4) unfolding itno_p_def by auto

    have "(n, t, vs) = min_norm_of_rules norms rules"
      using alist_map_values_equal[OF AY VY VM[simplified mnor_map_def]] .
    then have NI: "itno_invariant_sd_nin norms rules n t vs"
      unfolding itno_invariant_sd_nin_def using R by auto

    show ?thesis using assms(1)[OF Step(1-2) NI _ Step(4)] False by auto
  qed
qed (auto simp add: assms)


lemma itno_superset_gr_keys:
  "keys gr \<subseteq> keys (fst (iterate_norms gr)) \<union> keys (snd (iterate_norms gr))"
apply (intro subsetI, induct rule: itno_induct(1))
by (auto simp add: itno_f_def mnor_map_def, force)

lemma itno_subset_gr_keys:
  "keys (fst (iterate_norms gr)) \<union> keys (snd (iterate_norms gr)) \<subseteq> keys gr"
apply (intro subsetI, induct rule: itno_induct(1))
by (auto simp add: itno_f_def mnor_map_def)

lemma itno_gr_keys_equal:
  "keys gr = keys (fst (iterate_norms gr)) \<union> keys (snd (iterate_norms gr))"
using itno_superset_gr_keys itno_subset_gr_keys by blast

lemma itno_invariant_sd_holds:
  assumes "gram_sd gr"
    shows "itno_invariant_sd gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
using itno_induct_sd(2) assms by auto


(*****************************************************************************
  gram_nsd
 *****************************************************************************)

lemma gram_nsd_sd: "gram_nsd gr \<Longrightarrow> gram_sd gr"
by (simp add: gram_nsd_def)


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma nog_alist: "gram_sd gr \<Longrightarrow> is_alist (norms_of_grammar gr)" unfolding norms_of_grammar_def
using itno_invariant_sd_holds unfolding itno_invariant_sd_def by auto

lemma nog_gr_keys_equal: "gram_nsd gr \<Longrightarrow> keys gr = keys (norms_of_grammar gr)"
using itno_gr_keys_equal[of gr] by (simp add: norms_of_grammar_def gram_nsd_def gram_normed_fun_def)

lemma nog_in_rules':
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "(t, vs) \<in> set rules" using assms(3) unfolding norms_of_grammar_def
proof (induct rule: itno_induct_sd_in[of gr v n t vs rules])
  case (Step norms rest yes no)
  show ?case proof (cases "(v, n, t, vs) \<in> set norms")
    case False
    then have I: "rules_have_norm norms rules" "(n, t, vs) = min_norm_of_rules norms rules"
      using Step(3) unfolding itno_invariant_sd_nin_def by auto
    then have "(t, vs) = snd (min_norm_of_rules norms rules)" by (metis snd_conv)
    then show ?thesis using mnor_in_rules[OF I(1)] by auto
  qed (auto simp add: Step)
qed (auto simp add: assms)

lemma nog_in_rules:
  assumes "gram_nsd gr"
      and "(v, rules) \<in> set gr"
    shows "snd (lookup (norms_of_grammar gr) v) \<in> set rules" using assms
proof -
  have A: "is_alist (norms_of_grammar gr)" using nog_alist gram_nsd_sd assms(1) by auto
  have G: "gram_sd gr" using assms gram_nsd_sd by auto

  have "\<exists>nv. (v, nv) \<in> set (norms_of_grammar gr)" using nog_gr_keys_equal assms by force
  then have "\<exists>nv. (v, nv) \<in> set (norms_of_grammar gr) \<and> snd nv \<in> set rules"
    using nog_in_rules'[OF G assms(2)] by force
  then show ?thesis using lookup_predicate[OF A, of v _ "\<lambda>v nv. snd nv \<in> set rules"] by auto
qed

lemma nog_norms_greater_zero:
  assumes "(v, n, nrule) \<in> set (norms_of_grammar gr)"
    shows "0 < n" using assms unfolding norms_of_grammar_def
proof (induct rule: itno_induct(1))
  case (Step norms rest yes no) show ?case
  proof (cases "(v, n, nrule) \<in> set norms")
    case False

    have M: "(v, n, nrule) \<in> set (mnor_map norms yes)" using False Step(4)
      unfolding itno_f_def by auto

    have "\<forall>(v, rules) \<in> set yes. itno_p norms (v, rules)" using Step(3) by auto
    then have "\<forall>(v, rules) \<in> set yes. 0 < fst (min_norm_of_rules norms rules)"
      using mnor_norm_greater_zero unfolding itno_p_def by force
    then have "\<forall>(v, mn) \<in> set (mnor_map norms yes). 0 < fst mn" unfolding mnor_map_def by auto
    then show ?thesis using M by auto

  qed (auto simp add: Step)
qed (auto)

lemma nog_greater_zero_lookup:
  "gram_nsd gr \<Longrightarrow> v \<in> keys gr \<Longrightarrow> 0 < fst (lookup (norms_of_grammar gr) v)"
  apply (rule lookup_forall[of "norms_of_grammar gr"])
using nog_gr_keys_equal nog_norms_greater_zero[of _ _ _ gr] by auto

lemma nog_ns:
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
      and "(v, rules) \<in> set gr"
    shows "set vs \<subseteq> keys (norms_of_grammar gr)"
      and "norm_sum (norms_of_grammar gr) vs < n" using assms(2) unfolding norms_of_grammar_def
proof (induct rule: itno_induct_sd_in[of gr v n t vs rules])
  case (Step norms rest yes no)
  case 1 show ?case
  proof (cases "(v, n, t, vs) \<in> set norms")
    case True then show ?thesis using Step unfolding itno_f_def by auto
  next
    case False
    then have I: "rules_have_norm norms rules" "(n, t, vs) = min_norm_of_rules norms rules"
      using Step(3) unfolding itno_invariant_sd_nin_def by auto
    then show ?thesis unfolding itno_f_def using mnor_variables[OF I] by auto
  qed
  case 2

  have S: "is_alist norms" " is_alist rest" "keys rest \<inter> keys norms = {}" using Step(2)
    unfolding itno_invariant_sd_def by auto
  have AM: "is_alist (mnor_map norms yes)" unfolding mnor_map_def
    using alist_filter alist_map S(2) Step(6) by auto
  have NI: "set norms \<subseteq> set (itno_f norms yes)" unfolding itno_f_def by auto

  have "keys norms \<inter> keys (mnor_map norms yes) = {}" unfolding mnor_map_def
    using S(3) Step(6) by force
  then have AI: "is_alist (itno_f norms yes)" using Step AM alist_distr[of norms]
    unfolding itno_invariant_sd_def itno_f_def by auto

  show ?case
  proof (cases "(v, n, t, vs) \<in> set norms")
    case True then show ?thesis using ns_norms_superset_equal[OF _ S(1) AI NI] Step(4-5) by auto
  next
    case False
    then have "rules_have_norm norms rules" "(n, t, vs) = min_norm_of_rules norms rules"
      using Step(3) unfolding itno_invariant_sd_nin_def by auto
    then show ?thesis using ns_norms_superset_equal[OF _ S(1) AI NI] mnor_variables[of norms]
      by auto
  qed
qed (auto simp add: assms)


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
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]" unfolding norms_of_grammar_def
proof (induct rule: itno_induct_sd_in[of gr v n t vs rules])
  case (Step norms rest yes no)
  show ?case proof (cases "(v, n, t, vs) \<in> set norms")
    case False
    then have N: "rules_have_norm norms rules" "(n, t, vs) = min_norm_of_rules norms rules"
      using Step(3) unfolding itno_invariant_sd_nin_def by auto
    have I: "set rest \<subseteq> set gr" "keys rest \<inter> keys norms = {}" "is_alist rest"
        using Step(1-2) unfolding itno_invariant_def itno_invariant_sd_def by auto
  
    then have S: "norm_of_variables gr vs < n" unfolding norm_of_variables_def
      using nog_ns(2)[OF assms(1-3)]  by auto
  
    have A: "is_alist (norms_of_grammar gr)" using nog_alist assms(1) by auto
    have "norm_of_variables gr [v] = n" unfolding nov_singleton
      using lookup_predicate[OF A, of v _ "\<lambda>k v. fst v = n"] assms by auto
  
    then show ?thesis using S by auto
  qed (auto simp add: Step)
qed (auto simp add: assms)

lemma nov_nog:
  assumes "gram_nsd gr"
      and "(t, vs) = snd (lookup (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]"
proof -
  have "keys gr = keys (norms_of_grammar gr)" using nog_gr_keys_equal assms by auto
  then have V: "v \<in> keys (norms_of_grammar gr)" using assms by auto

  have G: "gram_sd gr" using gram_nsd_sd assms by auto
  then have A: "is_alist (norms_of_grammar gr)" using nog_alist by auto

  def n \<equiv> "fst (lookup (norms_of_grammar gr) v)"
  then show ?thesis using G nov_nog'[of gr v n t] existence_from_lookup[OF A V] assms n_def by auto
qed

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
  apply (auto simp add: add_commute add_strict_increasing2 nov_nog)
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
  case (Cons a v1) then show ?case by (case_tac "snd (lookup (norms_of_grammar gr) a)") auto
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
  have TH: "th \<in> keys rules" using nog_in_rules [OF normal(3) VR] TN[symmetric] by simp

  have TT: "tt = minimal_word_of_variables gr (rth @ vt)" unfolding rth_def
    using mwov_prefix normal(3) VR VT normal(2) .
  have TR: "(th, rth) \<in> set rules" using RA TH rth_def by (simp add: existence_from_lookup)
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gram_rule_vars_in_keys[OF GS VR TR]
    by simp

  show ?case using normal GS VR TR TT TH RV rules_def rth_def by (simp add: wiv_prefix[symmetric])
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
