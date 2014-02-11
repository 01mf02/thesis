header {* Norm proofs *}

theory Norm_proofs imports
  "Norm_funs"
  "Helpers"
begin


subsection {* Norm orders *}

definition v_rule_norm_hd_ord ::
  "(('v :: wellorder \<times> nat \<times> 't :: wellorder) \<times> ('v \<times> nat \<times> 't)) set" where
  "v_rule_norm_hd_ord \<equiv> {(n1, n2). n1 < n2}"

definition t_rule_norm_hd_ord ::
  "((nat \<times> 't :: wellorder) \<times> (nat \<times> 't)) set" where
  "t_rule_norm_hd_ord \<equiv> {(n1, n2). n1 < n2}"

lemma vrnhl_wf: "wf v_rule_norm_hd_ord"
unfolding v_rule_norm_hd_ord_def by (metis wf)

lemma vrnl_wf: "wfP v_rule_norm_less"
proof -
  let ?rel = "{(n1, n2). v_rule_norm_less n1 n2}"
  have id: "?rel = inv_image v_rule_norm_hd_ord v_rule_norm_strip_vs"
    unfolding inv_image_def v_rule_norm_less_def v_rule_norm_hd_ord_def by auto
  have "wf ?rel" unfolding id by (rule wf_inv_image[OF vrnhl_wf])
  then show ?thesis by (metis wfP_def)
qed

lemma vrno_wf: "wf v_rule_norm_ord"
unfolding v_rule_norm_ord_def using vrnl_wf by (metis wfP_def)

lemma gno_wf: "wf grammar_norms_ord"
unfolding grammar_norms_ord_def using vrno_wf by (rule wf_lex)

lemma vrnsv_trnsv_conv: "v_rule_norm_strip_vs (v, n) = (v, t_rule_norm_strip_vs n)"
unfolding v_rule_norm_strip_vs_def t_rule_norm_strip_vs_def
by (metis (lifting) split_conv surj_pair)

lemma vrnl_trnl: "t_rule_norm_less n1 n2 = v_rule_norm_less (v, n1) (v, n2)"
unfolding t_rule_norm_less_def v_rule_norm_less_def vrnsv_trnsv_conv by auto

lemma vrnle_trnle: "t_rule_norm_less_eq n1 n2 = v_rule_norm_less_eq (v, n1) (v, n2)"
unfolding t_rule_norm_less_eq_def v_rule_norm_less_eq_def vrnsv_trnsv_conv
by (metis (hide_lams, no_types) leI less_eq_prod_simp less_le_not_le prod.inject)

lemma vrno_vrnle: "(v_rule_norm_less_eq n1 n2) = ((n1, n2) \<in> v_rule_norm_ord\<^sup>=)"
using v_rule_norm_less_def unfolding v_rule_norm_less_eq_def v_rule_norm_ord_def
by (metis (no_types) Un_iff mem_Collect_eq pair_in_Id_conv split_conv)

lemma trnle_norm_le: "n1 \<le> n2 \<Longrightarrow> t_rule_norm_less_eq (n1, t, vs) (n2, t, vs)"
unfolding t_rule_norm_less_eq_def t_rule_norm_strip_vs_def by auto


subsection {* @{text gram_sd} *}

lemma gsd_alist: "gram_sd gr \<Longrightarrow> is_alist gr"
by (simp add: gram_sd_def)

lemma gsd_rules_alist: "gram_sd gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> is_alist rules"
unfolding gram_sd_def by auto

lemma gsd_rule_vars_in_keys:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(t, vars) \<in> set rules"
    shows "set vars \<subseteq> keys gr" using assms
unfolding gram_sd_def by (metis (lifting) split_conv)


subsection {* @{text norm_sum} *}

lemma ns_singleton: "norm_sum ns [v] = fst (lookup ns v)"
unfolding norm_sum_def by (case_tac "lookup ns v") auto

lemma ns_conv: "norm_sum ns vars = listsum (map (fst \<circ> lookup ns) vars)"
unfolding norm_sum_def apply (induct vars) by auto (metis fst_def)

lemma ns_distr: "norm_sum ns (x @ y) = norm_sum ns x + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_distr_cons: "norm_sum ns (x # y) = norm_sum ns [x] + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_singleton_leq: "v \<in> set vars \<Longrightarrow> norm_sum ns [v] \<le> norm_sum ns vars"
using member_le_listsum_nat[of "fst (lookup ns v)" "map (fst \<circ> lookup ns) vars"]
unfolding ns_singleton unfolding norm_sum_def ns_conv[symmetric] by auto

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
  then show ?thesis unfolding norm_sum_def by (metis norm_sum_def ns_conv)
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
  then show ?case using I  unfolding ns_distr_cons[of _ "a" "vs"] ns_singleton by auto
qed (auto simp add: norm_sum_def)

lemma ns_leq_new:
  assumes "map fst norms2 = map fst norms1"
      and "list_all2 v_rule_norm_less_eq norms2 norms1"
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
    unfolding values_leq_def values_related_def using L2 (*by auto*) sorry
  then have "fst (lookup norms2 a) \<le> fst (lookup norms1 a)"
    by (metis less_eq_prod_def order.strict_iff_order)
  then show ?case using I unfolding ns_distr_cons[of _ "a" "vs"] ns_singleton by auto
qed (auto simp add: norm_sum_def)


subsection {* @{text t_rule_has_norm} / @{text t_rules_have_norm} *}

lemma trhn_keys_superset:
  assumes "keys norms\<^sub>1 \<subseteq> keys norms\<^sub>2"
      and "t_rule_has_norm norms\<^sub>1 rule"
    shows "t_rule_has_norm norms\<^sub>2 rule"
using assms unfolding t_rule_has_norm_def by auto

lemma trhn_vars_normed: "(t_rule_has_norm norms (t, vs)) = (set vs \<subseteq> keys norms)"
unfolding t_rule_has_norm_def by auto

lemma trshn_keys_superset:
  assumes "keys norms\<^sub>1 \<subseteq> keys norms\<^sub>2"
      and "t_rules_have_norm norms\<^sub>1 rules"
    shows "t_rules_have_norm norms\<^sub>2 rules"
using assms unfolding t_rules_have_norm_def by (metis trhn_keys_superset)


subsection {* @{text norms_of_t_rules} *}

lemma notr_conv:
  "norms_of_t_rules norms rules = map (norm_of_t_rule norms) (filter (t_rule_has_norm norms) rules)"
unfolding norms_of_t_rules_def by (induct rules) auto

lemma notr_in_rules: "snd ` set (norms_of_t_rules norms rules) \<subseteq> set rules"
unfolding norms_of_t_rules_def norm_of_t_rule_def by auto

lemma notr_nonempty:
  assumes "t_rules_have_norm norms rules"
    shows "norms_of_t_rules norms rules \<noteq> []"
using assms unfolding t_rules_have_norm_def norms_of_t_rules_def by auto

lemma notr_norms_greater_zero: "(n, rt, rv) \<in> set (norms_of_t_rules norms rules) \<Longrightarrow> 0 < n"
unfolding norms_of_t_rules_def norm_of_t_rule_def by auto

lemma notr_variables:
  assumes "(n, t, vs) \<in> set (norms_of_t_rules norms rules)"
    shows "set vs \<subseteq> keys norms"
      and "n = Suc (norm_sum norms vs)" using assms
unfolding norms_of_t_rules_def norm_of_t_rule_def t_rule_has_norm_def by auto

lemma notr_rule_in:
  assumes "(t, vs) \<in> set rules"
      and "t_rule_has_norm norms (t, vs)"
    shows "(Suc (norm_sum norms vs), t, vs) \<in> set (norms_of_t_rules norms rules)" using assms
unfolding norms_of_t_rules_def norm_of_t_rule_def by auto (metis (lifting) Int_Collect split_conv)

lemma notr_leq:
  assumes "\<And>vs. set vs \<subseteq> keys norms\<^sub>2 \<Longrightarrow> norm_sum norms\<^sub>1 vs \<le> norm_sum norms\<^sub>2 vs"
      and "(t :: 't :: order, vs :: 'v :: order list) \<in> set (filter (t_rule_has_norm norms\<^sub>2) rules)"
    shows "norm_of_t_rule norms\<^sub>1 (t, vs) \<le> norm_of_t_rule norms\<^sub>2 (t, vs)"
proof -
  have "set vs \<subseteq> keys norms\<^sub>2" using assms(2) trhn_vars_normed[of norms\<^sub>2 t vs] by auto
  then have "norm_sum norms\<^sub>1 vs \<le> norm_sum norms\<^sub>2 vs" using assms(1) by auto
  then show ?thesis unfolding norm_of_t_rule_def by simp
qed

lemma notr_leq_new:
  assumes "\<And>vs. set vs \<subseteq> keys norms\<^sub>2 \<Longrightarrow> norm_sum norms\<^sub>1 vs \<le> norm_sum norms\<^sub>2 vs"
      and "(t :: 't :: order, vs :: 'v :: order list) \<in> set (filter (t_rule_has_norm norms\<^sub>2) rules)"
    shows "t_rule_norm_less_eq (norm_of_t_rule norms\<^sub>1 (t, vs)) (norm_of_t_rule norms\<^sub>2 (t, vs))"
proof -
  have "set vs \<subseteq> keys norms\<^sub>2" using assms(2) trhn_vars_normed[of norms\<^sub>2 t vs] by auto
  then have "norm_sum norms\<^sub>1 vs \<le> norm_sum norms\<^sub>2 vs" using assms(1) by auto
  then show ?thesis unfolding norm_of_t_rule_def
    using trnle_norm_le[of "Suc (norm_sum norms\<^sub>1 vs)" "Suc (norm_sum norms\<^sub>2 vs)"] by simp
qed

lemma notr_smaller:
  assumes "map fst norms\<^sub>1 = map fst norms\<^sub>2"
      and "values_leq norms\<^sub>1 norms\<^sub>2"
      and "is_alist (norms\<^sub>2 :: ('t :: order, 'v :: order) grammar_norms)"
    shows "list_all2 less_eq (norms_of_t_rules norms\<^sub>1 rules) (norms_of_t_rules norms\<^sub>2 rules)"
proof -
  have "keys norms\<^sub>1 = keys norms\<^sub>2" using assms(1) by (metis keys_fst_map)
  then have "t_rule_has_norm norms\<^sub>1 = t_rule_has_norm norms\<^sub>2" unfolding t_rule_has_norm_def by auto
  then have FF: "filter (t_rule_has_norm norms\<^sub>1) rules = filter (t_rule_has_norm norms\<^sub>2) rules"
    by auto

  have LE: "\<forall>x \<in> set (filter (t_rule_has_norm norms\<^sub>2) rules).
    norm_of_t_rule norms\<^sub>1 x \<le> norm_of_t_rule norms\<^sub>2 x"
    using notr_leq[of norms\<^sub>2 norms\<^sub>1] ns_leq[OF assms(1-3)] by (metis prod.exhaust)
  
  show ?thesis unfolding notr_conv FF using list_all2_map[of _ less_eq, OF LE] .
qed

lemma notr_smaller_new:
  assumes "map fst norms\<^sub>1 = map fst norms\<^sub>2"
      and "list_all2 v_rule_norm_less_eq norms\<^sub>1 norms\<^sub>2"
      and "is_alist (norms\<^sub>2 :: ('t :: wellorder, 'v :: wellorder) grammar_norms)"
    shows "list_all2 t_rule_norm_less_eq
           (norms_of_t_rules norms\<^sub>1 rules) (norms_of_t_rules norms\<^sub>2 rules)"
proof -
  have "keys norms\<^sub>1 = keys norms\<^sub>2" using assms(1) by (metis keys_fst_map)
  then have "t_rule_has_norm norms\<^sub>1 = t_rule_has_norm norms\<^sub>2" unfolding t_rule_has_norm_def by auto
  then have FF: "filter (t_rule_has_norm norms\<^sub>1) rules = filter (t_rule_has_norm norms\<^sub>2) rules"
    by auto

  have LE: "\<forall>x \<in> set (filter (t_rule_has_norm norms\<^sub>2) rules).
    t_rule_norm_less_eq (norm_of_t_rule norms\<^sub>1 x) (norm_of_t_rule norms\<^sub>2 x)"
    using notr_leq_new[of norms\<^sub>2 norms\<^sub>1] ns_leq_new[OF assms(1-3)] by (metis prod.exhaust)
  
  show ?thesis unfolding notr_conv FF using list_all2_map[of _ t_rule_norm_less_eq, OF LE] .
qed


subsection {* @{text min_norm_of_t_rules} *}

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


subsection {* @{text add_norms} *}

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


subsection {* @{text iterate_norms} *}

lemma itno_induct [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                partition (v_rule_has_norm norms) rest = (yes, no) \<Longrightarrow>
                P (norms, rest) \<Longrightarrow>
                P (add_norms norms yes, no)"
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
      then have I2: "keys gr = keys (add_norms norms yes) \<union> keys no"
        unfolding an_keys[of norms yes] using Step(3) by force

      show ?case using I1 I2 unfolding itno_invariant_def by auto
qed

lemma itno_induct_sd [case_names Base Step]:
  assumes B: "P ([], gr)"
      and S: "\<And>norms rest yes no.
                itno_invariant gr norms rest \<Longrightarrow>
                itno_invariant_sd gr norms rest \<Longrightarrow>
                partition (v_rule_has_norm norms) rest = (yes, no) \<Longrightarrow>
                P (norms, rest) \<Longrightarrow>
                P (add_norms norms yes, no)"
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
    have I1: "is_alist (add_norms norms yes)" using I(1) AY NM alist_distr[of norms]
      unfolding add_norms_def by auto

    have AC: "is_alist (yes @ no)" using alist_partition_distr[OF I(2) Step(2)[symmetric]] .
    then have I2: "is_alist no" using alist_distr[of yes] by simp
    
    have NN: "keys no \<inter> keys norms = {}" using Step(2) I(3) by force
    have MN: "keys no \<inter> keys (mnotr_map norms yes) = {}" unfolding mnotr_map_def
      using AC alist_distr[of yes no] by auto
    have I3: "keys no \<inter> keys (add_norms norms yes) = {}" using NN MN
      unfolding add_norms_def by auto

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

lemma itno_v_in_norms':
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "t_rules_have_norm (fst (iterate_norms gr)) rules"
    shows "v \<in> keys ((\<lambda>(norms, rest).
           add_norms norms (filter (v_rule_has_norm norms) rest)) (iterate_norms gr))"
using assms(3)
proof (induct rule: itno_induct_sd(1))
  case (Step norms rest yes no)
  show ?case proof (cases "v \<in> keys (add_norms norms yes)")
    case True show ?thesis using True an_keys[of "add_norms norms yes"] by auto
  next
    case False
    have GR: "is_alist gr" using gsd_alist[OF assms(1)] .
    have II: "set rest \<subseteq> set gr" "keys gr = keys norms \<union> keys rest"
      using Step(1) unfolding itno_invariant_def by auto
    have IS: "is_alist rest" using Step(2) unfolding itno_invariant_sd_def by simp

    have "v \<notin> keys norms" using False an_keys[of norms] by auto
    then have VR: "v \<in> keys rest" using II(2) assms(2) by auto

    have HN: "v_rule_has_norm (add_norms norms yes) (v, rules)"
      unfolding v_rule_has_norm_def using Step(5) by auto
    have VY: "(v, rules) \<notin> set yes" using False unfolding an_keys[of norms yes] by auto

    have "(v, rules) \<in> set rest" using alist_subset_values_equal[OF II(1) GR IS VR assms(2)] .
    then have "(v, rules) \<in> set no" using VY Step(3) by auto
    then have VF: "(v, rules) \<in> set (filter (v_rule_has_norm (add_norms norms yes)) no)"
      using HN by auto
    show ?thesis using VF an_var_in_keys by (metis (lifting) split_conv)
  qed
next
  case Base
  have VF: "(v, rules) \<in> set (filter (v_rule_has_norm []) gr)"
    unfolding v_rule_has_norm_def using Base assms(2) by auto
  show ?case using VF an_var_in_keys by (metis (no_types) split_conv)
qed (auto simp add: assms)

lemma itno_an_invariant:
  "(\<lambda>(norms, rest). add_norms norms (filter (v_rule_has_norm norms) rest)) (iterate_norms gr) =
   fst (iterate_norms gr)"
unfolding iterate_norms_def
using pi_invariant
  [of "add_norms" v_rule_has_norm "[]" gr, OF an_nil_invariant]
by (case_tac "partition_iterate v_rule_has_norm add_norms [] gr") auto

lemma itno_v_in_norms:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "t_rules_have_norm (fst (iterate_norms gr)) rules"
    shows "v \<in> keys (fst (iterate_norms gr))"
using itno_v_in_norms'[OF assms] unfolding itno_an_invariant[of gr] .


subsection {* @{text gram_nsd_fun} *}

lemma gram_nsd_sd: "gram_nsd_fun gr \<Longrightarrow> gram_sd gr"
by (simp add: gram_nsd_fun_def)


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

lemma mnotr_rn_leq:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
      and "(v, norm) \<in> set (refine_norms norms gr)"
    shows "t_rule_norm_less_eq (min_norm_of_t_rules (refine_norms norms gr) (lookup gr v)) norm"
proof -
  have I: "\<forall>(v, norm) \<in> set norms.
    t_rule_norm_less_eq (min_norm_of_t_rules norms (lookup gr v)) norm"
    "is_alist norms" "keys norms \<subseteq> keys gr" using assms(2) unfolding rn_invariant_def by auto

  def rules \<equiv> "lookup gr v"

  have MF: "map fst (refine_norms norms gr) = map fst norms" by (metis rn_fst_map)

  have "refine_norms norms gr = map_ran (\<lambda>v norm. min_norm_of_t_rules norms (lookup gr v)) norms"
    unfolding refine_norms_def mnotr_map_def v_rules_of_norms_def map_ran_def by auto
  then have LA: "list_all2 v_rule_norm_less_eq (refine_norms norms gr) norms" using I(1) vrnle_trnle sorry
  (*then have VL: "values_leq (refine_norms norms gr) norms" (*using map_ran_values_leq[OF I(1) _ I(2)]*)
    (*by auto*) sorry*)
  
  have "norm = min_norm_of_t_rules norms rules" using rn_mnotr'[OF assms(1) I(2-3) assms(3)]
    unfolding rules_def .
  then show ?thesis using list_all2_Min notr_smaller_new[OF MF LA I(2)] (*[OF MF VL I(2)]*)
    unfolding min_norm_of_t_rules_def rules_def (*by auto*) sorry
qed

lemma rn_decreases:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
      and "refine_norms norms gr \<noteq> norms"
    shows "(refine_norms norms gr, norms) \<in> grammar_norms_ord"
      and "rn_invariant (refine_norms norms gr) gr"
proof -
  have I: "\<forall>(v, norm) \<in> set norms.
    t_rule_norm_less_eq (min_norm_of_t_rules norms (lookup gr v)) norm"
    "is_alist norms" "keys norms \<subseteq> keys gr" using assms(2) unfolding rn_invariant_def by auto

  have "\<forall>(v, norm)\<in>set norms.
    v_rule_norm_less_eq (v, min_norm_of_t_rules norms (lookup gr v)) (v, norm)"
    using vrnle_trnle I(1) by (metis (lifting, no_types) prod.exhaust split_conv)
  then have VO: "\<forall>(v, norm)\<in>set norms.
    ((v, min_norm_of_t_rules norms (lookup gr v)), (v, norm)) \<in> v_rule_norm_ord\<^sup>="
    using vrno_vrnle by (metis (lifting, no_types) prod.exhaust split_conv)

  have "refine_norms norms gr = map_ran (\<lambda>v norm. min_norm_of_t_rules norms (lookup gr v)) norms"
    unfolding refine_norms_def mnotr_map_def v_rules_of_norms_def map_ran_def by auto
  then show "(refine_norms norms gr, norms) \<in> grammar_norms_ord" using map_ran_lex[OF VO] assms(3)
    unfolding grammar_norms_ord_def by auto

  have I1: "\<forall>(v, norm) \<in> set (refine_norms norms gr).
    t_rule_norm_less_eq (min_norm_of_t_rules (refine_norms norms gr) (lookup gr v)) norm"
    using mnotr_rn_leq[OF assms(1-2)] by auto
  have I2: "is_alist (refine_norms norms gr)" using rn_fst_map I(2) by (metis is_alist_def)
  have I3: "keys (refine_norms norms gr) \<subseteq> keys gr" using rn_fst_map I(3) by (metis keys_fst_map)
  show "rn_invariant (refine_norms norms gr) gr" using I1 I2 I3 unfolding rn_invariant_def by auto
qed

lemma rn_nil: "refine_norms [] gr = []"
unfolding refine_norms_def mnotr_map_def v_rules_of_norms_def by auto


subsection {* @{text minimise_norms} *}

termination minimise_norms
proof
  let ?mno = "{((n', g' :: ('t::wellorder, 'v::wellorder) grammar), n, g). (n', n) \<in> grammar_norms_ord}"
  have id: "?mno = inv_image grammar_norms_ord fst" unfolding inv_image_def by auto
  show "wf ?mno" unfolding id by (rule wf_inv_image[OF gno_wf])

  fix norms :: "('t::wellorder, 'v::wellorder) grammar_norms"
  fix gr :: "('t, 'v) grammar"
  assume "is_alist gr \<and> rn_invariant norms gr \<and> refine_norms norms gr \<noteq> norms"
  then have AS: "is_alist gr" "rn_invariant norms gr" "refine_norms norms gr \<noteq> norms" by auto

  have "(refine_norms norms gr, norms) \<in> grammar_norms_ord" using rn_decreases(1)[OF AS] .
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

lemma mn_rn:
  assumes "is_alist gr"
      and "rn_invariant norms gr"
    shows "refine_norms (minimise_norms norms gr) gr = minimise_norms norms gr" using assms
proof (induct norms gr rule: minimise_norms.induct)
  case (1 norms gr)
  show ?case proof (cases "refine_norms norms gr = norms")
    case True then show ?thesis by (metis minimise_norms.simps)
  next
    case False
    have "rn_invariant (refine_norms norms gr) gr" using rn_decreases(2) 1(2-3) False .
    then have X: "refine_norms (minimise_norms (refine_norms norms gr) gr) gr =
      minimise_norms (refine_norms norms gr) gr" using 1 False by auto
    have Y: "minimise_norms (refine_norms norms gr) gr = minimise_norms norms gr"
      using 1(2-3) by (metis minimise_norms.simps)
    show ?thesis using X unfolding Y .
  qed
qed

lemma mn_nil: "minimise_norms [] gr = []"
by (metis minimise_norms.simps rn_nil)


subsection {* @{text norms_of_grammar} *}

lemma nog_map_fst:
  shows "map fst (norms_of_grammar gr) = map fst (fst (iterate_norms gr))"
unfolding norms_of_grammar_def unfolding mn_map_fst[symmetric] by simp

lemma nog_alist: "gram_sd gr \<Longrightarrow> is_alist (norms_of_grammar gr)"
using itno_invariant_sd_holds mn_map_fst unfolding norms_of_grammar_def itno_invariant_sd_def
by (metis alist_fst_map)

lemma nog_gr_keys_equal:
  assumes "gram_nsd_fun gr"
    shows "keys gr = keys (norms_of_grammar gr)"
proof -
  have "keys gr = keys (fst (iterate_norms gr))" using itno_gr_keys_equal[of gr] assms
    by (simp add: norms_of_grammar_def gram_nsd_fun_def gram_normed_fun_def)
  then show ?thesis using nog_map_fst by (metis keys_fst_map)
qed

lemma itno_invariant_sd_member_holds:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "v \<in> keys (fst (iterate_norms gr))"
  shows "itno_invariant_sd_member (fst (iterate_norms gr)) v rules"
using assms(3) proof (induct rule: itno_induct_sd(1))
  case (Step norms rest yes no)
  def an \<equiv> "add_norms norms yes"
  have P: "v \<in> keys an" unfolding an_def using Step(5) Step by simp
  have II: "set rest \<subseteq> set gr" "keys gr = keys norms \<union> keys rest"
    using Step(1) unfolding itno_invariant_def by auto
  have IS: "is_alist norms" "is_alist rest" "keys rest \<inter> keys norms = {}"
    using Step(2) unfolding itno_invariant_sd_def by auto
  have AG: "is_alist gr" using gsd_alist assms(1) .
  have YG: "set yes \<subseteq> set gr" using Step(3) II(1) by auto
  have AY: "is_alist yes" using alist_partition_distr[OF IS(2) Step(3)[symmetric]] alist_distr
    by auto
  have YR: "keys yes \<subseteq> keys rest" using Step(3) by auto
  have NY: "keys norms \<inter> keys yes = {}" using YR IS(3) by auto
  have AU: "is_alist an" unfolding an_def using alist_distr_fst_map[OF an_fst_map IS(1) AY NY] .

  have T: "t_rules_have_norm norms rules"
  proof (cases "v \<in> keys norms")
    case True then show ?thesis using Step(4) unfolding itno_invariant_sd_member_def by auto
  next
    case False
    then have "v \<in> keys yes" using an_keys[of norms yes] P unfolding an_def by auto
    then have "(v, rules) \<in> set yes" using alist_values_equal[OF AG assms(2)] YG by auto
    then show ?thesis using Step(3) unfolding v_rule_has_norm_def by auto
  qed

  have "t_rules_have_norm an rules" unfolding an_def
    using trshn_keys_superset[OF _ T] an_keys[of norms] by auto
  then show ?case unfolding itno_invariant_sd_member_def an_def by auto
qed (auto simp add: assms(1))

lemma itno_rn_invariant:
  assumes "gram_sd gr"
    shows "rn_invariant (fst (iterate_norms gr)) gr"
proof -
  let ?in = "fst (iterate_norms gr)"

  have I1: "\<forall>(v, norm)\<in>set ?in. t_rule_norm_less_eq (min_norm_of_t_rules ?in (lookup gr v)) norm" sorry
  have I2: "is_alist ?in" using itno_invariant_sd_holds[OF assms(1)]
    unfolding itno_invariant_sd_def by auto
  have I3: "keys ?in \<subseteq> keys gr" using itno_gr_keys_equal by auto

  show ?thesis using I1 I2 I3 unfolding rn_invariant_def by simp
qed

lemma nog_invariant_holds:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, norm) \<in> set (norms_of_grammar gr)"
    shows "nog_invariant (norms_of_grammar gr) v rules"
proof -
  have AG: "is_alist gr" using gsd_alist[OF assms(1)] .
  have AN: "is_alist (norms_of_grammar gr)" using nog_alist[OF assms(1)] .
  have RI: "rn_invariant (fst (iterate_norms gr)) gr" using itno_rn_invariant[OF assms(1)] .
  have RE: "refine_norms (norms_of_grammar gr) gr = norms_of_grammar gr" using mn_rn[OF AG RI]
    unfolding norms_of_grammar_def .

  have "v \<in> keys (fst (iterate_norms gr))" using nog_map_fst assms(3)
    by (metis image_set key_in_fst keys_fst_map)
  then have "itno_invariant_sd_member (fst (iterate_norms gr)) v rules"
    using itno_invariant_sd_member_holds[OF assms(1-2)] by simp
  then have "t_rules_have_norm (fst (iterate_norms gr)) rules"
    unfolding itno_invariant_sd_member_def by auto
  then have I1: "t_rules_have_norm (norms_of_grammar gr) rules"
    using trshn_keys_superset nog_map_fst by (metis eq_iff keys_fst_map)

  have I2: "(v, min_norm_of_t_rules (norms_of_grammar gr) rules) \<in> set (norms_of_grammar gr)"
    using rn_mnotr_equal[OF RE _ assms(2) AN AG] assms(3) by auto
  show ?thesis using I1 I2 unfolding nog_invariant_def by simp
qed

lemma nog_invariant_n_t_vs_holds:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "nog_invariant_n_t_vs (norms_of_grammar gr) rules n t vs"
proof -
  def norms \<equiv> "(norms_of_grammar gr)"
  have I: "t_rules_have_norm norms rules" "(v, min_norm_of_t_rules norms rules) \<in> set norms"
    using nog_invariant_holds[of gr] assms unfolding norms_def nog_invariant_def by auto

  have II: "is_alist norms" using nog_alist[OF assms(1)] unfolding norms_def by auto
  have I2: "(n, t, vs) = min_norm_of_t_rules norms rules"
    using alist_values_equal II assms(3) I(2) unfolding norms_def .

  show ?thesis using I(1) I2 unfolding nog_invariant_n_t_vs_def norms_def by auto
qed

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
  have "v \<in> keys (fst (iterate_norms gr))" using nog_map_fst assms(2)
    by (metis image_set key_in_fst keys_fst_map)
  then have "\<exists>rules. (v, rules) \<in> set gr" using itno_gr_keys_equal by force
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

lemma nog_v_in_norms:
  assumes "gram_sd gr"
      and "(v, rules) \<in> set gr"
      and "t_rules_have_norm (norms_of_grammar gr) rules"
    shows "v \<in> keys (norms_of_grammar gr)"
proof -
  have "t_rules_have_norm (fst (iterate_norms gr)) rules"
    using trshn_keys_superset[OF _ assms(3)] nog_map_fst by (metis keys_fst_map subset_refl)
  then show ?thesis using itno_v_in_norms[OF assms(1-2)] using nog_map_fst by (metis keys_fst_map)
qed

lemma nog_ns:
  assumes "gram_sd gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "set vs \<subseteq> keys (norms_of_grammar gr)"
      and "n = Suc (norm_fun gr vs)"
proof -
  have "v \<in> keys (fst (iterate_norms gr))" using nog_map_fst assms(2)
    by (metis image_set key_in_fst keys_fst_map)
  then have "v \<in> keys gr" using itno_gr_keys_equal[of gr] by auto
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
  have GI: "keys gr \<subseteq> keys (fst (iterate_norms gr))" using nog_map_fst assms(2)
    by (metis keys_fst_map)

  have "keys (fst (iterate_norms gr)) \<inter> keys (snd (iterate_norms gr)) = {}"
    using itno_invariant_sd_holds[OF assms(1)] unfolding itno_invariant_sd_def by auto
  then have "keys gr \<inter> keys (snd (iterate_norms gr)) = {}"
    by (metis SS subset_antisym sup.bounded_iff GI)
  then have "keys (snd (iterate_norms gr)) \<subseteq> - keys (snd (iterate_norms gr))"
    using SS unfolding Set.disjoint_eq_subset_Compl by force
  then show ?thesis unfolding gram_normed_fun_def using iffD1[OF Set.subset_Compl_self_eq] by auto
qed


subsection {* @{text norm_fun} *}

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
      and "v \<in> set vars"
    shows "norm_fun gr [v] \<le> norm_fun gr vars" unfolding norm_fun_def
using ns_singleton_leq[OF assms(2)] nog_gr_keys_equal[OF assms(1)] by auto

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
  then show ?thesis using nf_singleton_leq[OF assms(1,3)] by auto
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


subsection {* @{text min_word_of_variables} *}

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


subsection {* @{text word_in_variables} *}

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


subsection {* @{text words_of_variables} *}

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


subsection {* @{text gram_normed_def} *}

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


subsection {* @{text gram_nsd_def} *}

lemma gnsdf_calcs_gnsdd: "gram_nsd_def gr = gram_nsd_fun gr"
unfolding gram_nsd_def_def gram_nsd_fun_def by (metis gnf_calcs_gnd)


subsection {* @{text norm_def} *}

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
