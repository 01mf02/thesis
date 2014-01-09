header {* Norm proofs *}

theory Norm_proofs imports
  "Norm_funs"
  "Helpers"
begin


subsection {* @{text gram_sd} *}

lemma gsd_alist: "gram_sd gr \<Longrightarrow> is_alist gr"
by (simp add: gram_sd_def)

lemma gsd_rules_alist: "gram_sd gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> is_alist rules"
unfolding gram_sd_def by auto

lemma gsd_rules_rule_exists:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
    shows "\<exists>t vs. (t, vs) \<in> set rules"
proof -
  have "rules \<noteq> []" using assms(1-2) unfolding gram_sd_def by auto
  then show ?thesis by (metis hd_in_set surj_pair)
qed

lemma gsd_rule_vars_in_keys:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(t, vars) \<in> set rules"
    shows "set vars \<subseteq> keys gr" using assms
unfolding gram_sd_def by (metis (lifting) split_conv)


subsection {* @{text norm_sum} *}

lemma ns_singleton: "norm_sum ns [v] = fst (lookup ns v)"
by (simp add: norm_sum_def)

lemma ns_distr: "norm_sum ns (x @ y) = norm_sum ns x + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_distr_cons: "norm_sum ns (x # y) = norm_sum ns [x] + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_singleton_leq:
  "set vars \<subseteq> keys ns \<Longrightarrow> v \<in> set vars \<Longrightarrow> norm_sum ns [v] \<le> norm_sum ns vars"
by (simp add: norm_sum_def)
   (metis (hide_lams, no_types) comp_apply imageI image_set member_le_listsum_nat)

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

lemma ns_leq:
  assumes "map fst norms2 = map fst norms1"
      and "values_leq norms2 norms1"
      and "is_alist norms1"
      and "set vs \<subseteq> keys norms1"
    shows "norm_sum norms2 vs \<le> norm_sum norms1 vs"
using assms(4) proof (induct vs)
  case (Cons a vs)
  then have I: "norm_sum norms2 vs \<le> norm_sum norms1 vs" by auto

  have A1: "a \<in> keys norms1" using Cons(2) by auto
  then have L2: "(a, lookup norms2 a) \<in> set norms2" using assms(3)
    by (metis alist_fst_map assms(1) existence_from_lookup keys_fst_map)

  have "(a, lookup norms1 a) \<in> set norms1" using assms(3) by (metis A1 existence_from_lookup)
  then have "lookup norms2 a \<le> lookup norms1 a" using assms(2)
    unfolding values_leq_def values_related_def using L2 by auto
  then have "fst (lookup norms2 a) \<le> fst (lookup norms1 a)"
    by (metis less_eq_prod_def order.strict_iff_order)
  then show ?case using I unfolding norm_sum_def by auto
qed (auto simp add: norm_sum_def)


(*****************************************************************************
  t_rule_has_norm / t_rules_have_norm
 *****************************************************************************)

lemma trhn_conserves:
  assumes "keys norms = keys norms1 \<union> keys norms2"
      and "t_rule_has_norm norms1 rule"
    shows "t_rule_has_norm norms  rule"
using assms unfolding t_rule_has_norm_def by auto

lemma trhn_vars_normed: "(t_rule_has_norm norms (t, vs)) = (set vs \<subseteq> keys norms)"
unfolding t_rule_has_norm_def by auto

lemma trshn_conserves:
  assumes "keys norms = keys norms1 \<union> keys norms2"
      and "t_rules_have_norm norms1 rules"
    shows "t_rules_have_norm norms  rules"
using assms(2) trhn_conserves[OF assms(1)] unfolding t_rules_have_norm_def by auto


(*****************************************************************************
  norms_of_t_rules
 *****************************************************************************)

lemma notr_in_rules: "snd ` set (norms_of_t_rules norms rules) \<subseteq> set rules"
unfolding norms_of_t_rules_def by auto

lemma notr_nonempty:
  assumes "t_rules_have_norm norms rules"
    shows "norms_of_t_rules norms rules \<noteq> []"
using assms by (simp add: t_rules_have_norm_def norms_of_t_rules_def filter_empty_conv)

lemma notr_nonempty_cons:
  assumes "t_rules_have_norm norms rules"
    shows "norms_of_t_rules (nh # norms) rules \<noteq> []" using assms
by (auto simp add: t_rules_have_norm_def norms_of_t_rules_def filter_empty_conv t_rule_has_norm_def)

lemma notr_norms_greater_zero: "(n, rt, rv) \<in> set (norms_of_t_rules norms rules) \<Longrightarrow> 0 < n"
unfolding norms_of_t_rules_def by auto

lemma notr_variables:
  assumes "(n, t, vs) \<in> set (norms_of_t_rules norms rules)"
    shows "set vs \<subseteq> keys norms"
      and "n = Suc (norm_sum norms vs)" using assms
unfolding norms_of_t_rules_def t_rule_has_norm_def by auto

lemma notr_rule_in:
  assumes "(t, vs) \<in> set rules"
      and "t_rule_has_norm norms (t, vs)"
    shows "(Suc (norm_sum norms vs), t, vs) \<in> set (norms_of_t_rules norms rules)" using assms
unfolding norms_of_t_rules_def by auto


(*****************************************************************************
  min_norm_of_t_rules
 *****************************************************************************)

lemma mnotr_in_nor:
  assumes "t_rules_have_norm norms rules"
    shows "min_norm_of_t_rules norms rules \<in> set (norms_of_t_rules norms rules)" using assms
unfolding min_norm_of_t_rules_def by (auto intro: Min_predicate simp add: notr_nonempty)

lemma mnotr_in_rules:
  assumes "t_rules_have_norm norms rules"
    shows "snd (min_norm_of_t_rules norms rules) \<in> set rules" using assms
  unfolding min_norm_of_t_rules_def
by - (rule Min_predicate,
      auto simp add: notr_nonempty notr_in_rules Set.image_subset_iff[symmetric])

lemma mnotr_norm_greater_zero:
  assumes "t_rules_have_norm norms rules"
    shows "0 < fst (min_norm_of_t_rules norms rules)" using assms unfolding min_norm_of_t_rules_def
by - (rule Min_predicate, auto simp add: notr_nonempty notr_norms_greater_zero)

lemma mnotr_variables:
  assumes "nog_invariant_n_t_vs norms rules n t vs"
    shows "set vs \<subseteq> keys norms"
      and "n = Suc (norm_sum norms vs)" 
by (metis assms nog_invariant_n_t_vs_def mnotr_in_nor notr_variables(1))
   (metis assms nog_invariant_n_t_vs_def mnotr_in_nor notr_variables(2))

lemma mnotr_variables_rules:
  assumes "nog_invariant_n_t_vs norms rules n t vs"
      and "(tr, vsr) \<in> set rules"
      and "t_rule_has_norm norms (tr, vsr)"
    shows "norm_sum norms vs \<le> norm_sum norms vsr"
proof -
  def nr \<equiv> "Suc (norm_sum norms vsr)"

  have I: "t_rules_have_norm norms rules" "(n, t, vs) = min_norm_of_t_rules norms rules"
    using assms(1) unfolding nog_invariant_n_t_vs_def by auto
  have N: "n = Suc (norm_sum norms vs)"
    using notr_variables(2) mnotr_in_nor[OF I(1), simplified I(2)[symmetric]] .

  have M: "(n, t, vs) = Min (set (norms_of_t_rules norms rules))"
    using I(2) unfolding min_norm_of_t_rules_def .

  have "(nr, tr, vsr) \<in> set (norms_of_t_rules norms rules)"
    using notr_rule_in[OF assms(2) assms(3)] unfolding nr_def by auto
  then have "(n, t, vs) \<le> (nr, tr, vsr)" using M by auto
  then have "n \<le> nr" by auto
  then show ?thesis unfolding N nr_def by auto
qed


(*****************************************************************************
  add_norms
 *****************************************************************************)

lemma an_fst_map: "map fst (add_norms norms yes) = map fst norms @ map fst yes"
unfolding add_norms_def mnotr_map_def using map_fst_map[of "min_norm_of_t_rules norms" yes] by auto

lemma an_keys: "keys (add_norms norms yes) = keys norms \<union> keys yes"
using an_fst_map keys_fst_map by (metis set_append)

lemma an_var_in_keys: "(v, rules) \<in> set yes \<Longrightarrow> v \<in> keys (add_norms norms yes)"
unfolding an_keys[of norms yes] by auto

lemma an_nil_invariant: "add_norms norms [] = norms"
unfolding add_norms_def mnotr_map_def by auto

lemma an_conserves_ns:
  assumes "itno_invariant_sd gr norms rest"
      and "partition (v_rule_has_norm norms) rest = (yes, no)"
      and "set vs \<subseteq> keys norms"
    shows "norm_sum norms vs = norm_sum (add_norms norms yes) vs"
proof -
  have S: "is_alist norms" " is_alist rest" "keys rest \<inter> keys norms = {}" using assms(1)
    unfolding itno_invariant_sd_def by auto
  have AM: "is_alist (mnotr_map norms yes)" unfolding mnotr_map_def
    using alist_filter alist_map_alist S(2) assms(2) by auto
  have NI: "set norms \<subseteq> set (add_norms norms yes)" unfolding add_norms_def
    by auto

  have "keys norms \<inter> keys (mnotr_map norms yes) = {}" unfolding mnotr_map_def
    using S(3) assms(2) by force
  then have AI: "is_alist (add_norms norms yes)" using S(1) AM alist_distr[of norms]
    unfolding add_norms_def by auto

  show ?thesis using ns_norms_superset_equal[OF assms(3) S(1) AI NI] .
qed

lemma an_trhn_irrelevant:
  assumes "set vs \<subseteq> keys (add_norms norms yes)"
      and "set vs \<inter> keys yes = {}"
    shows "t_rule_has_norm norms (tr, vs)"
proof -
  have 1: "set vs \<inter> keys (mnotr_map norms yes) = {}" using assms(2) unfolding mnotr_map_def by auto
  have "set vs \<subseteq> keys norms \<union> keys (mnotr_map norms yes)" using assms(1) unfolding add_norms_def by auto
  then have "set vs \<subseteq> keys norms" using 1 by auto
  then show ?thesis unfolding t_rule_has_norm_def by auto
qed


subsection {* @{text v_rules_of_norms} *}

lemma vron_fst_map: "map fst (v_rules_of_norms norms gr) = map fst norms"
unfolding v_rules_of_norms_def by (induct norms) auto

lemma vron_alist:
  assumes "is_alist norms"
    shows "is_alist (v_rules_of_norms norms gr)"
using vron_fst_map[symmetric] alist_fst_map[OF assms] by auto

lemma vron_gr:
  assumes "is_alist gr"
      and "v \<in> keys norms"
      and "(v, rules) \<in> set gr"
    shows "(v, rules) \<in> set (v_rules_of_norms norms gr)"
proof -
  have 1: "(v, lookup gr v) \<in> set (v_rules_of_norms norms gr)" unfolding v_rules_of_norms_def
    using assms(2) by (induct norms) auto
  have 2: "lookup gr v = rules" using lookup_from_existence[OF assms(1,3)] .
  show ?thesis using 1 unfolding 2 .
qed


subsection {* @{text refine_norms} *}

lemma rn_fst_map: "map fst (refine_norms norms gr) = map fst norms"
unfolding refine_norms_def mnotr_map_def vron_fst_map map_fst_map by simp

lemma rn_mnotr:
  assumes "(v, norm) \<in> set (refine_norms norms gr)"
      and "(v, rules) \<in> set gr"
      and "is_alist norms"
      and "is_alist gr"
    shows "norm = min_norm_of_t_rules norms rules"
proof -
  have VN: "v \<in> keys norms" using assms(1) rn_fst_map by (metis image_set key_in_fst keys_fst_map)
  have AV: "is_alist (v_rules_of_norms norms gr)" using vron_alist assms(3) .
  have VR: "(v, rules) \<in> set (v_rules_of_norms norms gr)"
    using vron_gr[OF assms(4) _ assms(2)] VN by auto
  show ?thesis using assms(1)[symmetric] unfolding refine_norms_def mnotr_map_def
    using alist_map_values_equal[OF AV VR, of norm "\<lambda>v rules. min_norm_of_t_rules norms rules"]
      assms(2) by auto
qed

lemma rn_mnotr_equal:
  assumes "refine_norms norms gr = norms"
      and "(v, norm) \<in> set norms"
      and "(v, rules) \<in> set gr"
      and "is_alist norms"
      and "is_alist gr"
    shows "norm = min_norm_of_t_rules norms rules"
using rn_mnotr[OF _ assms(3-5)] unfolding assms(1) using assms(2) by auto

lemma rn_mnotr':
  assumes "is_alist gr"
      and "is_alist norms"
      and "keys norms \<subseteq> keys gr"
      and "(v, norm) \<in> set (refine_norms norms gr)"
    shows "norm = min_norm_of_t_rules norms (lookup gr v)"
proof -
  have "keys (refine_norms norms gr) \<subseteq> keys gr" using assms(3) rn_fst_map by (metis keys_fst_map)
  then have "v \<in> keys gr" using assms(4) by (metis alist_keys_fst_set key_in_fst set_rev_mp)
  then have "(v, lookup gr v) \<in> set gr" using existence_from_lookup[OF assms(1)] by auto
  then show ?thesis using rn_mnotr[OF assms(4) _ assms(2,1)] by auto
qed

lemma notr_smaller:
  assumes "norms2 = refine_norms norms1 gr"
      and "norms2 \<le> norms1"
    shows "norms_of_t_rules norms2 rules \<le> norms_of_t_rules norms1 rules"
unfolding norms_of_t_rules_def using ns_leq
sorry

lemma mnotr_smaller:
  assumes "map fst norms1 = map fst norms2"
      and "norms2 \<le> norms1"
      (*and "t_rules_have_norms norms1"*)
    shows "min_norm_of_t_rules norms2 rules \<le> min_norm_of_t_rules norms1 rules"
unfolding min_norm_of_t_rules_def
sorry

lemma mnotr_leq:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
      and "(v, rnorm) \<in> set (refine_norms norms gr)"
    shows "min_norm_of_t_rules (refine_norms norms gr) (lookup gr v) \<le> rnorm"
proof -
  have I: "\<forall>(v, norm) \<in> set norms. min_norm_of_t_rules norms (lookup gr v) \<le> norm"
    "is_alist norms" "keys norms \<subseteq> keys gr" using assms(2) unfolding rn_invariant_def sorry

  def rules \<equiv> "lookup gr v"

  have MF: "map fst norms = map fst (refine_norms norms gr)" sorry
  have RN: "refine_norms norms gr \<le> norms" sorry
  have Y: "rnorm = min_norm_of_t_rules norms rules" sorry
  have Z: "min_norm_of_t_rules (refine_norms norms gr) rules \<le> rnorm"
    unfolding Y using mnotr_smaller[OF MF RN] .

  show ?thesis using Z unfolding rules_def .
qed

lemma rn_decreases:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
    shows "refine_norms norms gr \<le> norms"
      and "rn_invariant (refine_norms norms gr) gr"
proof -
  (* TODO: Caesar, why doesn't that work? *)
  have I: "\<forall>(v, norm) \<in> set norms. min_norm_of_t_rules norms (lookup gr v) \<le> norm"
    "is_alist norms" "keys norms \<subseteq> keys gr" using assms(2) unfolding rn_invariant_def sorry

  have "refine_norms norms gr = map_ran (\<lambda>v norm. min_norm_of_t_rules norms (lookup gr v)) norms"
    unfolding refine_norms_def mnotr_map_def v_rules_of_norms_def map_ran_def by auto
  then show "refine_norms norms gr \<le> norms" using map_ran_smaller[OF I(1)] by auto

  have I1: "\<forall>(v, norm) \<in> set (refine_norms norms gr).
    min_norm_of_t_rules (refine_norms norms gr) (lookup gr v) \<le> norm"
    using mnotr_leq[OF assms(1-2)] by auto
  have I2: "is_alist (refine_norms norms gr)" using rn_fst_map I(2) by (metis is_alist_def)
  have I3: "keys (refine_norms norms gr) \<subseteq> keys gr" using rn_fst_map I(3) by (metis keys_fst_map)
  show "rn_invariant (refine_norms norms gr) gr" using I1 I2 I3 unfolding rn_invariant_def by auto
qed

lemma rn_nil: "refine_norms [] gr = []"
unfolding refine_norms_def mnotr_map_def v_rules_of_norms_def by auto


subsection {* @{text minimise_norms} *}


termination minimise_norms
proof
  let ?no = "{(n' :: ('t::wellorder, 'v::wellorder) grammar_norms, n). n' < n}"
  let ?mno = "{((n', g' :: ('t, 'v) grammar), n, g). (n', n) \<in> ?no}"
  show "wf ?mno" sorry

  fix norms :: "('t::wellorder, 'v::wellorder) grammar_norms"
  fix gr :: "('t, 'v) grammar"
  assume "is_alist gr \<and> rn_invariant norms gr \<and> refine_norms norms gr \<noteq> norms"
  then have AS: "is_alist gr" "rn_invariant norms gr" "refine_norms norms gr \<noteq> norms" by auto
  
  have "refine_norms norms gr < norms" using rn_decreases(1)[OF AS(1-2)] AS(3) by auto
  then show "((refine_norms norms gr, gr), norms, gr) \<in> ?mno" by auto
qed


lemma mn_map_fst: "map fst norms = map fst (minimise_norms norms gr)"
proof (induct norms gr rule: minimise_norms.induct)
  case (1 norms gr)
  show ?case proof (cases "is_alist gr \<and> rn_invariant norms gr \<and> refine_norms norms gr \<noteq> norms")
    case True show ?thesis using 1[OF True] minimise_norms.simps rn_fst_map by metis
  next
    case False then show ?thesis by (metis minimise_norms.simps)
  qed
qed

lemma mn_rn_new:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
    shows "refine_norms (minimise_norms norms gr) gr = minimise_norms norms gr" using assms
proof (induct norms gr rule: minimise_norms.induct)
  case (1 norms gr)
  show ?case proof (cases "refine_norms norms gr = norms")
    case True then show ?thesis by (metis minimise_norms.simps)
  next
    case False
    have "rn_invariant (refine_norms norms gr) gr" using rn_decreases(2)[OF 1(2-3)] .
    then have X: "refine_norms (minimise_norms (refine_norms norms gr) gr) gr =
      minimise_norms (refine_norms norms gr) gr" using 1 False by auto
    have Y: "minimise_norms (refine_norms norms gr) gr = minimise_norms norms gr"
      using 1(2-3) by (metis minimise_norms.simps)
    show ?thesis using X unfolding Y .
  qed
qed

lemma mn_rn: "refine_norms (minimise_norms norms gr) gr = (minimise_norms norms gr)"
sorry

lemma mn_nil: "minimise_norms [] gr = []"
by (metis minimise_norms.simps rn_nil)


subsection {* @{text update_norms} *}

lemma un_fst_map: "map fst (update_norms gr norms yes) = map fst norms @ map fst yes"
unfolding update_norms_def by (metis an_fst_map mn_map_fst)

lemma un_keys: "keys (update_norms gr norms yes) = keys norms \<union> keys yes"
using keys_fst_map an_keys mn_map_fst update_norms_def by metis

lemma un_minimal:
  assumes "(v, rules) \<in> set gr"
      and "(v, norm) \<in> set (update_norms gr norms yes)"
      and "is_alist (update_norms gr norms yes)"
      and "is_alist gr"
    shows "norm = min_norm_of_t_rules (update_norms gr norms yes) rules"
using rn_mnotr_equal mn_rn assms(2,1,3-4) unfolding update_norms_def .

lemma un_un_invariant: "update_norms gr (update_norms gr norms yes) [] = update_norms gr norms yes"
proof -
  def un \<equiv> "update_norms gr norms yes"
  have "refine_norms un gr = un" unfolding update_norms_def un_def using mn_rn[of _ gr] by auto
  then show ?thesis unfolding update_norms_def un_def
    by (metis an_nil_invariant minimise_norms.simps)
qed

lemma un_nil_invariant: "update_norms gr [] [] = []"
unfolding update_norms_def add_norms_def mnotr_map_def using mn_nil
by (metis append_Nil map.simps(1))


subsection {* @{text iterate_norms} *}

lemma itno_induct [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                partition (v_rule_has_norm norms) rest = (yes, no) \<Longrightarrow>
                P (norms, rest) \<Longrightarrow>
                P (update_norms gr norms yes, no)"
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
      have I1: "set no \<subseteq> set gr" using Step(2-3) unfolding itno_invariant_def by auto
      
      have "keys gr = keys norms \<union> keys rest" using Step(2) unfolding itno_invariant_def by simp
      then have I2: "keys gr = keys (update_norms gr norms yes) \<union> keys no"
        unfolding un_keys[of gr norms yes] using Step(3) by force

      show ?case using I1 I2 unfolding itno_invariant_def by auto
qed

lemma itno_induct_sd [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                itno_invariant_sd gr norms rest \<Longrightarrow>
                partition (v_rule_has_norm norms) rest = (yes, no) \<Longrightarrow>
                P (norms, rest) \<Longrightarrow>
                P (update_norms gr norms yes, no)"
      and G: "gram_sd gr"
  shows "P (iterate_norms gr)"
    and "itno_invariant_sd gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
proof (induct rule: itno_induct(1))
  case Base
    case 1 show ?case using B by auto
    case 2 show ?case unfolding itno_invariant_sd_def using gsd_alist[OF G] by auto
next
  case (Step norms rest yes no)
    case 1 show ?case using S Step by auto
    case 2

    have I: "is_alist norms" "is_alist rest" "keys rest \<inter> keys norms = {}" using Step(4)
      unfolding itno_invariant_sd_def by auto

    have NM: "keys norms \<inter> keys (mnotr_map norms yes) = {}" using Step(2) I(3)
      unfolding mnotr_map_def by force
    have AY: "is_alist (mnotr_map norms yes)" using alist_filter alist_map_alist Step(2) I(2)
      unfolding mnotr_map_def by auto
    have AA: "is_alist (add_norms norms yes)" using I(1) AY NM alist_distr[of norms]
      unfolding add_norms_def by auto
    have I1: "is_alist (update_norms gr norms yes)" unfolding update_norms_def
      using alist_fst_map AA mn_map_fst[of "add_norms norms yes"] .

    have AC: "is_alist (yes @ no)" using alist_partition_distr[OF I(2) Step(2)[symmetric]] .
    then have I2: "is_alist no" using alist_distr[of yes] by simp
    
    have NN: "keys no \<inter> keys norms = {}" using Step(2) I(3) by force
    have MN: "keys no \<inter> keys (mnotr_map norms yes) = {}" unfolding mnotr_map_def
      using AC alist_distr[of yes no] by auto
    have NA: "keys no \<inter> keys (add_norms norms yes) = {}" using NN MN
      unfolding add_norms_def by auto
    have I3: "keys no \<inter> keys (update_norms gr norms yes) = {}" unfolding update_norms_def
      using mn_map_fst[of "add_norms norms yes"] NA keys_fst_map by metis

    show ?case using Step unfolding itno_invariant_sd_def using I1 I2 I3 by auto
qed

lemma itno_invariant_holds: "itno_invariant gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
using itno_induct(2) by auto

lemma itno_gr_keys_equal:
  "keys gr = keys (fst (iterate_norms gr)) \<union> keys (snd (iterate_norms gr))"
using itno_invariant_holds[of gr] unfolding itno_invariant_def by auto

lemma itno_invariant_sd_holds:
  assumes "gram_sd gr"
    shows "itno_invariant_sd gr (fst (iterate_norms gr)) (snd (iterate_norms gr))"
using itno_induct_sd(2) assms by auto


(*****************************************************************************
  gram_nsd_fun
 *****************************************************************************)

lemma gram_nsd_sd: "gram_nsd_fun gr \<Longrightarrow> gram_sd gr"
by (simp add: gram_nsd_fun_def)


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma nog_invariant_holds:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "v \<in> keys (norms_of_grammar gr)"
  shows "nog_invariant (norms_of_grammar gr) v rules"
using assms(3) unfolding norms_of_grammar_def proof (induct rule: itno_induct_sd(1))
  case (Step norms rest yes no)
  def un \<equiv> "update_norms gr norms yes"
  have P: "v \<in> keys un" unfolding un_def using Step(5) by simp
  have II: "set rest \<subseteq> set gr" using Step(1) unfolding itno_invariant_def by simp
  have IS: "is_alist norms" "is_alist rest" "keys rest \<inter> keys norms = {}"
    using Step(2) unfolding itno_invariant_sd_def by auto
  have AG: "is_alist gr" using gsd_alist assms(1) .
  have YG: "set yes \<subseteq> set gr" using Step(3) II(1) by auto
  have AY: "is_alist yes" using alist_partition_distr[OF IS(2) Step(3)[symmetric]] alist_distr
    by auto
  have YR: "keys yes \<subseteq> keys rest" using Step(3) by auto
  have NY: "keys norms \<inter> keys yes = {}" using YR IS(3) by auto
  have AU: "is_alist un" unfolding un_def using alist_distr_fst_map[OF un_fst_map IS(1) AY NY] .

  have T: "t_rules_have_norm norms rules"
  proof (cases "v \<in> keys norms")
    case True then show ?thesis using Step(4) unfolding nog_invariant_def by auto
  next
    case False
    then have "v \<in> keys yes" using un_keys[of gr norms yes] P unfolding un_def by auto
    then have "(v, rules) \<in> set yes" using alist_values_equal[OF AG assms(2)] YG by auto
    then show ?thesis using Step(3) unfolding v_rule_has_norm_def by auto
  qed

  have I1: "t_rules_have_norm un rules" using trshn_conserves un_keys T unfolding un_def .
  have I2: "(v, min_norm_of_t_rules un rules) \<in> set un"
    using un_minimal[OF assms(2) _ _ AG] P AU unfolding un_def by auto

  show ?case using I1 I2 unfolding nog_invariant_def un_def by auto
qed (auto simp add: assms(1))

lemma nog_invariant_n_t_vs_holds:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "nog_invariant_n_t_vs (norms_of_grammar gr) rules n t vs"
proof -
  def norms \<equiv> "(norms_of_grammar gr)"
  have I: "t_rules_have_norm norms rules" "(v, min_norm_of_t_rules norms rules) \<in> set norms"
    using nog_invariant_holds[of gr] assms unfolding norms_def nog_invariant_def by auto

  have II: "is_alist norms" using itno_invariant_sd_holds[OF assms(1)]
    unfolding itno_invariant_sd_def norms_def norms_of_grammar_def by auto
  have I2: "(n, t, vs) = min_norm_of_t_rules norms rules"
    using alist_values_equal II assms(3) I(2) unfolding norms_def .

  show ?thesis using I(1) I2 unfolding nog_invariant_n_t_vs_def norms_def by auto
qed

lemma nog_alist: "gram_sd gr \<Longrightarrow> is_alist (norms_of_grammar gr)" unfolding norms_of_grammar_def
using itno_invariant_sd_holds unfolding itno_invariant_sd_def by auto

lemma nog_gr_keys_equal: "gram_nsd_fun gr \<Longrightarrow> keys gr = keys (norms_of_grammar gr)"
using itno_gr_keys_equal[of gr]
by (simp add: norms_of_grammar_def gram_nsd_fun_def gram_normed_fun_def)

lemma nog_in_rules':
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "(t, vs) \<in> set rules" using assms(3)
proof -
  have I: "t_rules_have_norm (norms_of_grammar gr) rules"
          "(n, t, vs) = min_norm_of_t_rules (norms_of_grammar gr) rules"
    using nog_invariant_n_t_vs_holds[OF assms] unfolding nog_invariant_n_t_vs_def by auto
  then have "(t, vs) = snd (min_norm_of_t_rules (norms_of_grammar gr) rules)" by (metis snd_conv)
  then show ?thesis using mnotr_in_rules[OF I(1)] by auto
qed

lemma nog_in_rules:
  assumes "gram_nsd_fun gr"
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

lemma nog_norms_greater_zero':
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "0 < n"
proof -
  have "\<exists>rules. (v, rules) \<in> set gr" using itno_gr_keys_equal assms(2)
    unfolding norms_of_grammar_def by force
  then have I: "\<exists>rules. nog_invariant_n_t_vs (norms_of_grammar gr) rules n t vs"
    using nog_invariant_n_t_vs_holds[OF assms(1) _ assms(2)] by auto
  then show ?thesis using mnotr_variables(2)[of _ _ n] by auto
qed

lemma nog_greater_zero_lookup:
  assumes "gram_nsd_fun gr"
      and "v \<in> keys gr"
    shows "0 < fst (lookup (norms_of_grammar gr) v)"
proof -
  have GS: "gram_sd gr" using gram_nsd_sd assms(1) .
  show ?thesis apply (rule lookup_forall[of "norms_of_grammar gr"])
    using nog_gr_keys_equal[OF assms(1)] nog_norms_greater_zero'[OF GS] assms(2) by auto
qed

lemma nog_variables:
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
      and "(v, rules) \<in> set gr"
    shows "set vs \<subseteq> keys (norms_of_grammar gr)"
      and "n = Suc (norm_fun gr vs)"
proof -
  have I: "nog_invariant_n_t_vs (norms_of_grammar gr) rules n t vs"
    using nog_invariant_n_t_vs_holds assms(1,3,2) .
  show "set vs \<subseteq> keys (norms_of_grammar gr)" using mnotr_variables(1)[OF I] by simp
  show "n = Suc (norm_fun gr vs)" using mnotr_variables(2)[OF I] unfolding norm_fun_def by simp
qed

lemma nog_v_in_norms':
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "t_rules_have_norm (norms_of_grammar gr) rules"
    shows "v \<in> keys ((\<lambda>(norms, rest).
           (update_norms gr) norms (filter (v_rule_has_norm norms) rest)) (iterate_norms gr))"
  using assms(3) unfolding norms_of_grammar_def
proof (induct rule: itno_induct_sd(1))
  case (Step norms rest yes no)
  show ?case proof (cases "v \<in> keys (update_norms gr norms yes)")
    case True show ?thesis using True un_keys[of gr "(update_norms gr norms yes)"] by auto
  next
    case False
    have GR: "is_alist gr" using gsd_alist[OF assms(1)] .
    have II: "set rest \<subseteq> set gr" "keys gr = keys norms \<union> keys rest"
      using Step(1) unfolding itno_invariant_def by auto
    have IS: "is_alist rest" using Step(2) unfolding itno_invariant_sd_def by simp

    have "v \<notin> keys norms" using False un_keys[of gr] by auto
    then have VR: "v \<in> keys rest" using II(2) assms(2) by auto

    have HN: "v_rule_has_norm (update_norms gr norms yes) (v, rules)"
      unfolding v_rule_has_norm_def using Step(5) by auto
    have VY: "(v, rules) \<notin> set yes" using False unfolding un_keys[of gr norms yes] by auto

    have "(v, rules) \<in> set rest" using alist_subset_values_equal[OF II(1) GR IS VR assms(2)] .
    then have "(v, rules) \<in> set no" using VY Step(3) by auto
    then have VF: "(v, rules) \<in> set (filter (v_rule_has_norm (update_norms gr norms yes)) no)"
      using HN by auto
    show ?thesis using un_keys VF by (metis (lifting) an_keys an_var_in_keys split_conv)
  qed
next
  case Base
  have VF: "(v, rules) \<in> set (filter (v_rule_has_norm []) gr)"
    unfolding v_rule_has_norm_def using Base assms(2) by auto
  show ?case using un_keys VF by (metis (lifting) an_keys an_var_in_keys split_conv)
qed (auto simp add: assms)

lemma nog_un_invariant:
  "(\<lambda>(norms, rest). (update_norms gr) norms (filter (v_rule_has_norm norms) rest)) (iterate_norms gr) =
   norms_of_grammar gr"
unfolding norms_of_grammar_def iterate_norms_def
using pi_invariant_extended
  [of "update_norms gr" "[]" v_rule_has_norm gr, OF un_nil_invariant un_un_invariant]
by (case_tac "partition_iterate v_rule_has_norm (update_norms gr) [] gr") auto

lemma nog_v_in_norms:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "t_rules_have_norm (norms_of_grammar gr) rules"
    shows "v \<in> keys (norms_of_grammar gr)"
using nog_v_in_norms'[OF assms] unfolding nog_un_invariant .


lemma nog_ns:
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "set vs \<subseteq> keys (norms_of_grammar gr)"
      and "n = Suc (norm_fun gr vs)"
proof -
  have "v \<in> keys gr" using itno_gr_keys_equal[of gr] assms(2) unfolding norms_of_grammar_def by auto
  then have R: "\<exists>rules. (v, rules) \<in> set gr" by auto
  show "set vs <= keys (norms_of_grammar gr)" using R nog_variables(1)[OF assms] by metis
  show "n = Suc (norm_fun gr vs)"             using R nog_variables(2)[OF assms] by metis
qed

lemma nog_vs_leq_rules_vs:
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
      and "(v, rules) \<in> set gr"
      and "(tr, vsr) \<in> set rules"
      and "t_rule_has_norm (norms_of_grammar gr) (tr, vsr)"
    shows "norm_fun gr vs \<le> norm_fun gr vsr"
proof -
  have IU: "nog_invariant_n_t_vs (norms_of_grammar gr) rules n t vs"
    using nog_invariant_n_t_vs_holds[OF assms(1,3,2)] .
  show ?thesis using mnotr_variables_rules[OF IU assms(4-5)] unfolding norm_fun_def by simp
qed

lemma nog_keys_superset_gr_normed:
  assumes "gram_sd gr"
      and "keys gr \<subseteq> keys (norms_of_grammar gr)"
    shows "gram_normed_fun gr"
proof -
  have SS: "keys (fst (iterate_norms gr)) \<union> keys (snd (iterate_norms gr)) \<subseteq> keys gr"
    using itno_gr_keys_equal[of gr] by auto

  have "keys (fst (iterate_norms gr)) \<inter> keys (snd (iterate_norms gr)) = {}"
    using itno_invariant_sd_holds[OF assms(1)] unfolding itno_invariant_sd_def by auto
  then have "keys gr \<inter> keys (snd (iterate_norms gr)) = {}"
    by (metis SS subset_antisym sup.bounded_iff norms_of_grammar_def assms(2))
  then have "keys (snd (iterate_norms gr)) \<subseteq> - keys (snd (iterate_norms gr))"
    using SS unfolding Set.disjoint_eq_subset_Compl by force
  then show ?thesis unfolding gram_normed_fun_def using iffD1[OF Set.subset_Compl_self_eq] by auto
qed


(*****************************************************************************
  norm_fun
 *****************************************************************************)

lemma nf_distr: "norm_fun gr (x @ y) = norm_fun gr x + norm_fun gr y"
by (simp add: norm_fun_def ns_distr)

lemma nf_distr_cons:
  "norm_fun gr (x # y) = norm_fun gr [x] + norm_fun gr y"
by (rule nf_distr[of _ "[x]", simplified])

lemma nf_singleton: "norm_fun gr [v] = fst (lookup (norms_of_grammar gr) v)"
by (simp add: norm_fun_def ns_singleton)

lemma nf_nog':
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
      and "(v, rules) \<in> set gr"
    shows "norm_fun gr [v] = Suc (norm_fun gr vs)" unfolding norms_of_grammar_def
proof -
  have S: "n = Suc (norm_fun gr vs)" using nog_ns(2)[OF assms(1-2)] by auto
  have A: "is_alist (norms_of_grammar gr)" using nog_alist assms(1) by auto

  have "norm_fun gr [v] = n" unfolding nf_singleton
    using lookup_predicate[OF A, of v _ "\<lambda>k v. fst v = n"] assms by auto
  then show ?thesis using S by auto
qed

lemma nf_nog:
  assumes "gram_nsd_fun gr"
      and "(t, vs) = snd (lookup (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_fun gr [v] = Suc (norm_fun gr vs)"
proof -
  have "keys gr = keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF assms(1)] .
  then have V: "v \<in> keys (norms_of_grammar gr)" using assms(3) by auto

  have G: "gram_sd gr" using gram_nsd_sd assms by auto
  then have A: "is_alist (norms_of_grammar gr)" using nog_alist by auto

  def n \<equiv> "fst (lookup (norms_of_grammar gr) v)"
  then show ?thesis using nf_nog'[OF G, of v n t] existence_from_lookup[OF A V] assms by auto
qed

lemma nf_singleton_leq:
  assumes "gram_nsd_fun gr"
      and "set vars \<subseteq> keys gr"
      and "v \<in> set vars"
    shows "norm_fun gr [v] \<le> norm_fun gr vars" unfolding norm_fun_def
using ns_singleton_leq[OF _ assms(3)] nog_gr_keys_equal[OF assms(1)] assms(2) by auto

lemma nf_nog2:
  assumes "gram_nsd_fun gr"
      and "set vars \<subseteq> keys gr"
      and "v \<in> set vars"
      and "(n, t, vs) = lookup (norms_of_grammar gr) v"
    shows "norm_fun gr vs < norm_fun gr vars"
proof -
  have V: "set vars \<subseteq> keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF assms(1)] assms(2)
    by auto
  have S: "v \<in> keys (norms_of_grammar gr)" using V assms(3) by auto

  have G: "gram_sd gr" using gram_nsd_sd assms(1) by auto
  then have R: "\<exists>rules. (v, rules) \<in> set gr" using assms(2-3)
    by (metis existence_from_lookup gsd_alist in_mono)
  have I: "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    using existence_from_lookup[OF nog_alist[OF G] S assms(4)[symmetric]] .

  have "norm_fun gr [v] = Suc (norm_fun gr vs)" using nf_nog'[OF G I] R by auto
  then show ?thesis using nf_singleton_leq[OF assms(1-3)] by auto
qed

lemma nf_greater_zero:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
      and "v \<noteq> []"
    shows "0 < norm_fun gr v" using assms unfolding norm_fun_def
by (induct v) (auto, subst ns_distr_cons, simp add: ns_singleton nog_greater_zero_lookup)

lemma nf_empty: "norm_fun gr [] = 0"
by (simp add: norm_fun_def ns_empty)

lemma nf_recursion:
  assumes "gram_nsd_fun gr"
      and "set vars \<subseteq> keys gr"
    shows "norm_fun gr vars =
           (\<Sum>(n, t, vs)\<leftarrow>(map (lookup (norms_of_grammar gr)) vars). Suc (norm_fun gr vs))"
proof -
  have E: "norm_fun gr vars = (\<Sum>(n, t, vs)\<leftarrow>map (lookup (norms_of_grammar gr)) vars. n)"
    unfolding norm_fun_def norm_sum_def
    by (metis (lifting) List.map.compositionality cond_split_eta fst_conv fst_def)

  have G: "gram_sd gr" using gram_nsd_sd[OF assms(1)] .
  have V: "set vars \<subseteq> keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF assms(1)] assms(2)
    by auto
  have N: "\<forall>(v, n, t, vs) \<in> set (norms_of_grammar gr). n = Suc (norm_fun gr vs)"
    using nog_ns(2)[OF G] by auto
  have "\<forall>(n, t, vs) \<in> set (map (lookup (norms_of_grammar gr)) vars).
          n = Suc (norm_fun gr vs)" using lookup_values_predicate[OF V N] by auto
  then have M: "map (\<lambda>(n, t, vs). n)                    (map (lookup (norms_of_grammar gr)) vars) =
                map (\<lambda>(n, t, vs). Suc (norm_fun gr vs)) (map (lookup (norms_of_grammar gr)) vars)"
    using map_eq_conv[symmetric] by auto
  show ?thesis unfolding E using HOL.arg_cong[OF M] .
qed


(*****************************************************************************
  min_word_of_variables
 *****************************************************************************)

termination min_word_of_variables
by (relation "measure (\<lambda>(gr, vs). norm_fun gr vs)") (auto simp add: nf_nog2)

lemma mwov_distr:
  assumes "gram_nsd_fun gr"
      and "set v1 \<subseteq> keys gr"
      and "set v2 \<subseteq> keys gr"
    shows "min_word_of_variables gr (v1 @ v2) =
           min_word_of_variables gr v1 @
           min_word_of_variables gr v2"
      and "length (min_word_of_variables gr (v1 @ v2)) =
           length (min_word_of_variables gr v1) +
           length (min_word_of_variables gr v2)" using assms
by auto

lemma mwov_singleton:
  assumes "gram_nsd_fun gr"
      and "(vh, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "min_word_of_variables gr [vh] = t # (min_word_of_variables gr vs)"
using assms
  lookup_from_existence[OF nog_alist[OF gram_nsd_sd[OF assms(1)]] assms(2)]
  nog_gr_keys_equal[OF assms(1)] by auto

lemma mwov_induct:
  assumes "\<And>gr vars.
             (\<And>n t vs. gram_nsd_fun gr \<Longrightarrow> set vars \<subseteq> keys gr \<Longrightarrow>
               (n, t, vs) \<in> lookup (norms_of_grammar gr) ` set vars \<Longrightarrow> P gr vs) \<Longrightarrow>
             P gr vars"
    shows "P gr vars"
by (induct rule: min_word_of_variables.induct) (metis assms(1) image_set)

lemma mwov_recursion:
  assumes "gram_nsd_fun gr"
      and "set vars \<subseteq> keys gr"
    shows "min_word_of_variables gr vars =
           concat (map (\<lambda>(n, t, vs). t # (min_word_of_variables gr vs))
                  (map (lookup (norms_of_grammar gr)) vars))" using assms
by auto

lemma mwov_len_recursion:
  assumes "gram_nsd_fun gr"
      and "set vars \<subseteq> keys gr"
    shows "length (min_word_of_variables gr vars) =
           (\<Sum>(n, t, vs)\<leftarrow>(map (lookup (norms_of_grammar gr)) vars).
             Suc (length (min_word_of_variables gr vs)))"
proof -
  have "\<And>l f. (\<Sum>x\<leftarrow>l. length (case x of (n, t, vs) \<Rightarrow> t # f vs)) =
          (\<Sum>(n, t, vs)\<leftarrow>l. length (t # f vs))"
    by (metis (no_types) case_prod_distrib prod.exhaust split_conv)
  then have E: "\<And>l f. length (concat (map (\<lambda>(n, t, vs). t # f vs) l)) =
                  (\<Sum>(n, t, vs)\<leftarrow>l. Suc (length (f vs)))" unfolding map_concat_len by auto
  show ?thesis unfolding mwov_recursion[OF assms] E by auto
qed

lemma mwov_len_calcs_nf':
  assumes "gram_nsd_fun gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "length (min_word_of_variables gr vs) = norm_fun gr vs" using assms
proof (induct arbitrary: v n t rule: mwov_induct)
  case (1 gr vars)

  have G: "gram_sd gr" using gram_nsd_sd[OF 1(2)] .
  have V: "v \<in> keys (norms_of_grammar gr)" using 1(3) by auto
  have R: "\<exists>rules. (v, rules) \<in> set gr" using nog_gr_keys_equal[OF 1(2)] G V
    by (metis existence_from_lookup gsd_alist)
      
  have X: "set vars \<subseteq> keys gr" using nog_ns(1)[OF G 1(3)] nog_gr_keys_equal[OF 1(2)] R by auto
  have I: "\<And>v n t vs. v \<in> set vars \<Longrightarrow> (n, t, vs) = lookup (norms_of_grammar gr) v \<Longrightarrow>
             length (min_word_of_variables gr vs) = norm_fun gr vs"
    proof -
      fix v n t vs
      assume V: "v \<in> set vars"
      assume N: "(n, t, vs) = lookup (norms_of_grammar gr) v"

      have A: "is_alist (norms_of_grammar gr)" using nog_alist[OF G] by auto
      have K: "v \<in> keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF 1(2)] V X by auto
      have L: "(n, t, vs) \<in> lookup (norms_of_grammar gr) ` set vars" using V N by auto
      have M: "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
        using existence_from_lookup A K N[symmetric] .
      show "length (min_word_of_variables gr vs) = norm_fun gr vs" using 1(1) 1(2) X L 1(2) M .
    qed
  have M: "\<And>e. e \<in> set (map (lookup (norms_of_grammar gr)) vars) \<longrightarrow>
              (\<lambda>(n, t, vs). Suc (length (min_word_of_variables gr vs))) e =
              (\<lambda>(n, t, vs). Suc (norm_fun gr vs)) e"
    by (case_tac e) (metis (lifting, mono_tags) I image_iff image_set split_conv)
  have L: "(\<Sum>(n, t, vs)\<leftarrow>map (lookup (norms_of_grammar gr)) vars.
             Suc (length (min_word_of_variables gr vs))) =
           (\<Sum>(n, t, vs)\<leftarrow>map (lookup (norms_of_grammar gr)) vars.
             Suc (norm_fun gr vs))" using HOL.arg_cong[OF map_ext[OF M]] .
  show ?case using L nf_recursion[OF 1(2) X] mwov_len_recursion[OF 1(2) X] by simp
qed

theorem mwov_len_calcs_nf:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
    shows "length (min_word_of_variables gr v) = norm_fun gr v" using assms(2)
proof (induct v)
  case (Cons vh vt)
  then have I: "length (min_word_of_variables gr vt) = norm_fun gr vt" by auto

  def l  \<equiv> "lookup (norms_of_grammar gr) vh"
  def n  \<equiv> "fst l"
  def t  \<equiv> "fst (snd l)"
  def vs \<equiv> "snd (snd l)"

  have G: "gram_sd gr" using gram_nsd_sd[OF assms(1)] .
  have A: "is_alist (norms_of_grammar gr)" using nog_alist[OF G] by auto
  have E: "(vh, n, t, vs) \<in> set (norms_of_grammar gr)"
    using Cons(2) nog_gr_keys_equal[OF assms(1)] existence_from_lookup[OF A, of vh l]
    unfolding l_def n_def t_def vs_def by auto

  have LN: "length (min_word_of_variables gr [vh]) = n"
    using mwov_singleton[OF assms(1) E] nog_ns(2)[OF G E] mwov_len_calcs_nf'[OF assms(1) E] Cons(2)
    unfolding l_def n_def by auto
  have LD: "length (min_word_of_variables gr (vh # vt)) =
            length (min_word_of_variables gr [vh]) +
            length (min_word_of_variables gr vt)"
    using mwov_distr(2)[OF assms(1), of "[vh]" vt] Cons(2) by auto
  show ?case using I LN LD nf_distr_cons[of gr vh vt] nf_singleton[of gr vh]
    unfolding l_def n_def by auto
qed (auto simp add: nf_empty)

lemma mwov_empty:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
      and "min_word_of_variables gr v = []"
    shows "v = []" using assms
by (metis gr_implies_not0 list.size(3) mwov_len_calcs_nf nf_greater_zero)

lemma mwov_length:
  assumes "gram_nsd_fun gr"
      and "(v, rules) \<in> set gr"
      and "(tr, vsr) \<in> set rules"
    shows "length (min_word_of_variables gr [v]) \<le> Suc (length (min_word_of_variables gr vsr))"
proof -
  have G: "gram_sd gr" using gram_nsd_sd[OF assms(1)] .
  have A: "is_alist (norms_of_grammar gr)" using nog_alist[OF G] .
  have K: "keys gr = keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF assms(1)] .
  have V: "v \<in> keys (norms_of_grammar gr)" using K assms(2) by auto

  def nvh \<equiv> "lookup (norms_of_grammar gr) v"
  def n  \<equiv> "(\<lambda>(n, t, vs).  n) nvh"
  def t  \<equiv> "(\<lambda>(n, t, vs).  t) nvh"
  def vs \<equiv> "(\<lambda>(n, t, vs). vs) nvh"
  have N: "(v, n, t, vs) \<in> set (norms_of_grammar gr)" apply (case_tac nvh)
    unfolding n_def t_def vs_def nvh_def using existence_from_lookup[OF A V] by auto

  have V1: "set vs  \<subseteq> keys gr" using nog_ns(1)[OF G N] K by auto

  have V2: "set vsr \<subseteq> keys gr" using gsd_rule_vars_in_keys[OF G assms(2-3)] .
  then have "set vsr \<subseteq> keys (norms_of_grammar gr)" using nog_gr_keys_equal[OF assms(1)] by auto
  then have HN: "t_rule_has_norm (norms_of_grammar gr) (tr, vsr)"
    unfolding t_rule_has_norm_def by auto

  have "length (min_word_of_variables gr vs) \<le> length (min_word_of_variables gr vsr)"
    unfolding mwov_len_calcs_nf[OF assms(1) V1] mwov_len_calcs_nf[OF assms(1) V2]
    using nog_vs_leq_rules_vs G N assms(2-3) HN .
  then show ?thesis unfolding mwov_singleton[OF assms(1) N] by auto
qed

lemma mwov_hd_from_nog:
  assumes "gram_nsd_fun gr"
      and "(vh, rules) \<in> set gr"
      and "set vt \<subseteq> keys gr"
      and "th # tt = min_word_of_variables gr (vh # vt)"
    shows "th = fst (snd (lookup (norms_of_grammar gr) vh))" using assms
by (case_tac "lookup (norms_of_grammar gr) vh") simp

lemma mwov_prefix:
  assumes G: "gram_nsd_fun gr"
      and V: "(vh, rules) \<in> set gr"
      and S: "set vt \<subseteq> keys gr"
      and M: "th # tt = min_word_of_variables gr (vh # vt)"
    shows "tt = min_word_of_variables gr ((lookup rules th) @ vt)"
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
    using lookup_from_existence gsd_rules_alist[OF GS V] TN .

  have "is_alist rules" using gsd_rules_alist GS V .
  then have "(th, rth) \<in> set rules" using TN rth_def by (auto simp add: existence_from_lookup)
  then have RT: "set rth \<subseteq> keys gr" using gsd_rule_vars_in_keys GS V by simp

  show ?thesis using assms SL LO[symmetric] rth_def mwov_distr[OF G RT S]
    by (case_tac "lookup (norms_of_grammar gr) vh") simp
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
  have 1: "lookup gr vh = rules" using lookup_from_existence gsd_alist[OF G] V .
  have 2: "lookup rules th = rth" using lookup_from_existence gsd_rules_alist[OF G V] T .
  show ?thesis using assms 1 2 unfolding word_in_variables_def by auto
qed

lemma wiv_mwov:
  assumes G: "gram_nsd_fun gr"
      and V: "set v \<subseteq> keys gr"
    shows "word_in_variables gr (min_word_of_variables gr v) v" using assms
proof (induct gr "min_word_of_variables gr v" v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"
  def  nrth \<equiv> "snd (snd (lookup (norms_of_grammar gr) vh))"

  have GS: "gram_sd gr" using normal by (simp add: gram_nsd_sd)
  have VT: "set vt \<subseteq> keys gr" using normal(4) by simp
  have VR: "(vh, rules) \<in> set gr" using gsd_alist[OF GS] normal rules_def
    by (simp add: existence_from_lookup)
  have RA: "is_alist rules" using gsd_rules_alist GS VR .

  have "th = fst (snd (lookup (norms_of_grammar gr) vh))"
    using mwov_hd_from_nog normal(3) VR VT normal(2) .
  then have TN: "(th, nrth) = snd (lookup (norms_of_grammar gr) vh)" using nrth_def by simp
  have TH: "th \<in> keys rules" using nog_in_rules [OF normal(3) VR] TN[symmetric] by simp

  have TT: "tt = min_word_of_variables gr (rth @ vt)" unfolding rth_def
    using mwov_prefix normal(3) VR VT normal(2) .
  have TR: "(th, rth) \<in> set rules" using RA TH rth_def by (simp add: existence_from_lookup)
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gsd_rule_vars_in_keys[OF GS VR TR]
    by simp

  show ?case using normal GS VR TR TT TH RV unfolding rules_def rth_def
    by (simp add: wiv_prefix[symmetric] del: min_word_of_variables.simps)
qed (simp add: word_in_variables_def mwov_empty del: min_word_of_variables.simps,
     simp add: word_in_variables_def)

lemma wiv_word_head: "word_in_variables gr (th # tt) (vh # vt) \<Longrightarrow> th \<in> keys (lookup gr vh)"
by (case_tac "th \<in> keys (lookup gr vh)") (auto simp add: Let_def word_in_variables_def)

lemma mwov_minimal_wiv:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
      and "word_in_variables gr w v"
    shows "length (min_word_of_variables gr v) \<le> length w" using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"

  have GS: "gram_sd gr" using normal by (simp add: gram_nsd_sd)
  have VR: "(vh, rules) \<in> set gr" using GS normal(3) rules_def
    by (simp add: existence_from_lookup gsd_alist)
  have RA: "is_alist rules" using gsd_rules_alist GS VR .

  have TH: "th \<in> keys rules" using normal rules_def wiv_word_head by simp
  have TR: "(th, rth) \<in> set rules" using rth_def RA TH by (simp add: existence_from_lookup)

  have VT: "set vt \<subseteq> keys gr" using normal by simp
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gsd_rule_vars_in_keys[OF GS VR TR] by auto
  have RT: "set rth \<subseteq> keys gr" using RV by simp

  have L1: "length (min_word_of_variables gr (vh # vt)) =
           length (min_word_of_variables gr [vh]) + length (min_word_of_variables gr vt)"
    using mwov_distr(2)[OF normal(2) _ VT, of "[vh]"] normal(3) by auto
  have L2: "length (min_word_of_variables gr (rth @ vt)) =
           length (min_word_of_variables gr rth) + length (min_word_of_variables gr vt)"
    using mwov_distr(2)[OF normal(2) RT VT] .

  have "length (min_word_of_variables gr (vh # vt)) \<le>
   Suc (length (min_word_of_variables gr (rth @ vt)))"
    using mwov_length[OF normal(2) VR TR] L1 L2 by auto
  also have "... \<le> length (th # tt)" using normal(1,4) RV TH unfolding rules_def rth_def
    by (auto simp add: word_in_variables_def)
  finally show ?case .
qed (auto simp add: word_in_variables_def)

lemma wiv_vars_in_norms:
  assumes "gram_sd gr"
      and "set v \<subseteq> keys gr"
      and "word_in_variables gr w v"
    shows "set v \<subseteq> keys (norms_of_grammar gr)"
 using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)

  def rules \<equiv> "lookup gr vh"
  def   rth \<equiv> "lookup rules th"

  have GS: "gram_sd gr" using normal(2) .
  have VR: "(vh, rules) \<in> set gr" using GS normal(3) rules_def
    by (simp add: existence_from_lookup gsd_alist)
  have RA: "is_alist rules" using gsd_rules_alist GS VR .

  have TH: "th \<in> keys rules" using normal rules_def wiv_word_head by simp
  have TR: "(th, rth) \<in> set rules" using rth_def RA TH by (simp add: existence_from_lookup)

  have VT: "set vt \<subseteq> keys gr" using normal by simp
  have RV: "set (rth @ vt) \<subseteq> keys gr" using normal gsd_rule_vars_in_keys[OF GS VR TR] by auto
  have RT: "set rth \<subseteq> keys gr" using RV by simp

  have "word_in_variables gr tt (rth @ vt)" using normal(4) RV TH unfolding rules_def rth_def
    by (auto simp add: word_in_variables_def)
  then have RVN: "set (rth @ vt) \<subseteq> keys (norms_of_grammar gr)"
    using normal(1)[OF _ TH GS _ ] RV normal(4) unfolding rth_def rules_def by auto
  then have "set rth \<subseteq> keys (norms_of_grammar gr)" by auto
  then have HN: "t_rules_have_norm (norms_of_grammar gr) rules" using TR
    unfolding t_rules_have_norm_def t_rule_has_norm_def by auto

  have "vh \<in> keys (norms_of_grammar gr)" using nog_v_in_norms GS VR HN .
  then show ?case using RVN by auto
qed (auto simp add: word_in_variables_def)


(*****************************************************************************
  words_of_variables
 *****************************************************************************)

lemma mwov_in_wov:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
    shows "min_word_of_variables gr v \<in> words_of_variables gr v" using assms
by (simp add: words_of_variables_def wiv_mwov del: min_word_of_variables.simps)

lemma mwov_min_wov:
  assumes "gram_nsd_fun gr"
      and "set v \<subseteq> keys gr"
    shows "w \<in> words_of_variables gr v \<Longrightarrow> length (min_word_of_variables gr v) \<le> length w"
unfolding words_of_variables_def using mwov_minimal_wiv[OF assms] by simp


(*****************************************************************************
  gram_normed_def
 *****************************************************************************)

lemma gnf_calcs_gnd:
  assumes "gram_sd gr"
    shows "gram_normed_def gr = gram_normed_fun gr"
proof (intro iffI)
  assume P: "gram_normed_def gr"
  
  have S: "\<And>v. set v \<subseteq> keys gr \<Longrightarrow> set v \<subseteq> keys (norms_of_grammar gr)"
    proof -
      fix v
      assume V: "set v \<subseteq> keys gr"
      then have "\<exists>w. word_in_variables gr w v" using P[simplified gram_normed_def_def] by auto
      then show "set v \<subseteq> keys (norms_of_grammar gr)" using wiv_vars_in_norms[OF assms(1) V] by auto
    qed
  have "keys gr \<subseteq> keys (norms_of_grammar gr)" using list_subset_trans S .
  then show "gram_normed_fun gr" using nog_keys_superset_gr_normed[OF assms(1)] by simp
next
  assume "gram_normed_fun gr"
  then have "gram_nsd_fun gr" using assms(1) unfolding gram_nsd_fun_def by simp
  then show "gram_normed_def gr" unfolding gram_normed_def_def using wiv_mwov by auto
qed


(*****************************************************************************
  gram_nsd_def
 *****************************************************************************)

lemma gnsdf_calcs_gnsdd: "gram_nsd_def gr = gram_nsd_fun gr"
unfolding gram_nsd_def_def gram_nsd_fun_def by (metis gnf_calcs_gnd)


(*****************************************************************************
  norm
 *****************************************************************************)

theorem mwov_len_calcs_nd:
  assumes "gram_nsd_def gr"
      and "set v \<subseteq> keys gr"
    shows "norm_def gr v = length (min_word_of_variables gr v)" unfolding norm_def_def
apply (intro Least_equality)
using mwov_in_wov[OF _ assms(2)] mwov_min_wov[OF _ assms(2)]
  assms(1)[simplified gnsdf_calcs_gnsdd] by auto

theorem nf_calcs_nd:
  assumes "gram_nsd_def gr"
      and "set v \<subseteq> keys gr"
    shows "norm_fun gr v = norm_def gr v"
using mwov_len_calcs_nd[OF assms] mwov_len_calcs_nf[OF _ assms(2)]
  assms(1)[simplified gnsdf_calcs_gnsdd] by simp

end
