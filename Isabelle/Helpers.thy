header {* Helpers *}

theory Helpers imports
  "~~/src/HOL/Library/List_lexord"
begin

lemma Min_predicate: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P x \<Longrightarrow> P (Min A)"
by auto

lemma fst_predicate: "P (fst p) \<Longrightarrow> (f, s) = p \<Longrightarrow> P f"
by auto

lemma Min_insert_leq: "finite A \<Longrightarrow> (x :: 'a :: linorder) \<le> y \<Longrightarrow> Min (insert x A) \<le> y"
by (cases "A = {}") (auto simp add: min_max.le_infI1)

lemma list_all2_Min:
  assumes "list_all2 less_eq xs ys"
    shows "Min (set (xs :: 'a :: linorder list)) \<le> Min (set ys)"
using assms apply (induct rule: list_all2_induct)
  using Min_insert_leq by auto (metis (no_types) List.finite_set List.set.simps(2)
    Min.coboundedI Min_in eq_iff insertCI list_all2_Nil min_def min_le_iff_disj set_empty)

lemma list_all2_map:
  assumes "\<forall>x \<in> set l. P (f x) (g x)"
    shows "list_all2 P (map f l) (map g l)"
using assms by (induct l) auto


(*****************************************************************************
  filter and partition lemmata
 *****************************************************************************)

lemma sum_length_filter_compl':
  "length (filter P l) + length (filter (Not \<circ> P) l) = length l"
by (induct l) simp_all

lemma partition_length: "(yes, no) = partition P l \<Longrightarrow> length l = length yes + length no"
by (auto simp add: sum_length_filter_compl')

lemma filter_length_smaller:
  assumes "yesh # yest = filter (P a) l"
    shows "length (filter (Not \<circ> P a) l) < length l"
proof -
  have S: "set (yesh # yest) \<subseteq> set l" using assms by auto

  have "P a yesh" using assms Cons_eq_filter_iff[of yesh] by auto
  then show ?thesis using S length_filter_less[of yesh] by auto
qed

lemma filter_one_empty_other_full: "(filter P l = []) \<Longrightarrow> (l = filter (Not \<circ> P) l)"
by (metis (mono_tags) Set.filter_def comp_apply filter_True in_set_member member_filter member_rec(2) set_filter)

lemma map_concat_len:
  "length (concat (map f l)) = (\<Sum>x\<leftarrow>l. length (f x))"
by (induct l) auto

lemma list_subset_trans:
  assumes "\<And>v. set v \<subseteq> A \<Longrightarrow> set v \<subseteq> B"
    shows "A \<subseteq> B" using assms
by (metis List.set_insert in_set_insert insert_Nil insert_subset not_Cons_self2 subsetI)

lemma list_smaller:
  assumes "length xs = length ys"
      and "\<forall>(x, y) \<in> set (zip xs ys). (x :: 'a :: order) \<le> y"
    shows "xs \<le> ys"
using assms by (induct rule: list_induct2) auto

end
