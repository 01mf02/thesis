header {* Extension of Association Lists *}

theory AList_ext imports "~~/src/HOL/Library/AList_Mapping"
begin

definition is_alist :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "is_alist l \<equiv> distinct (map fst l)"

definition lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "lookup l k \<equiv> the (Mapping.lookup (Mapping l) k)"

definition keys :: "('a \<times> 'b) list \<Rightarrow> 'a set" where
  "keys l \<equiv> Mapping.keys (Mapping l)"


lemma alist_keys_fst_set[simp]: "keys l = fst ` set l"
by (induct l) (auto simp add: keys_def)

lemma alist_fst_map: "is_alist l1 \<Longrightarrow> map fst l1 = map fst l2 \<Longrightarrow> is_alist l2"
by (simp add: is_alist_def)

lemma alist_empty[simp]: "is_alist []"
by (simp add: is_alist_def)

lemma keys_fst_map: "set (map fst l) = keys l"
by (induct l) (auto simp add: keys_def)

lemma key_in_fst[simp]: "(k, v) \<in> A \<Longrightarrow> k \<in> fst ` A"
by (rule Set.image_eqI) simp_all

lemma lookup_from_existence: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> lookup l k = v"
by (simp add: lookup_def is_alist_def)

lemma existence_from_lookup: "is_alist l \<Longrightarrow> k \<in> keys l \<Longrightarrow> lookup l k = v \<Longrightarrow> (k, v) \<in> set l"
by (auto simp add: keys_def lookup_def is_alist_def)

lemma lookup_predicate: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> P k v \<Longrightarrow> P k (lookup l k)"
by (induct l) (auto simp add: lookup_def is_alist_def)

lemma lookup_forall: "\<forall>(k, v) \<in> set l. P k v \<Longrightarrow> k \<in> keys l \<Longrightarrow> P k (lookup l k)"
by (induct l) (auto simp add: lookup_def)

(* TODO: improve proof speed! *)
lemma alist_partition_distr: "is_alist l \<Longrightarrow> (yes, no) = partition P l \<Longrightarrow> is_alist (yes @ no)"
unfolding is_alist_def apply (induct l arbitrary: yes no) by auto

lemma alist_distr: "is_alist (l1 @ l2) = (is_alist l1 \<and> is_alist l2 \<and> keys l1 \<inter> keys l2 = {})"
by (induct l1, auto simp add: is_alist_def)

lemma alist_distr_fst_map:
  assumes "map fst l = map fst l1 @ map fst l2"
      and "is_alist l1"
      and "is_alist l2"
      and "keys l1 \<inter> keys l2 = {}"
    shows "is_alist l"
using assms by (induct l1, auto simp add: is_alist_def)

lemma alist_values_equal: "is_alist l \<Longrightarrow> (k, v1) \<in> set l \<Longrightarrow> (k, v2) \<in> set l \<Longrightarrow> v1 = v2"
by (induct l) (auto simp add: is_alist_def)

lemma alist_filter: "is_alist l \<Longrightarrow> is_alist (filter P l)"
by (induct l) (auto simp add: is_alist_def)

lemma alist_map_alist: "is_alist l \<Longrightarrow> is_alist (map (\<lambda>(a, b). (a, f b)) l)"
by (induct l) (auto simp add: is_alist_def)

lemma alist_map_values_equal:
  "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> (k, v') \<in> set (map (\<lambda>(k, v). (k, f k v)) l) \<Longrightarrow> v' = f k v"
by (induct l) (auto simp add: is_alist_def, force)

lemma map_fst_map: "map fst (map (\<lambda>(k, v). (k, f v)) l) = map fst l"
by (induct l) auto

lemma map_keys_equal: "keys (map (\<lambda>(k, v). (k, f v)) l) = keys l"
by (induct l) auto

lemma alist_superset_lookup_equal:
  assumes "set l \<subseteq> keys A"
      and "is_alist A"
      and "is_alist B"
      and "set A \<subseteq> set B"
      and "k \<in> set l"
    shows "lookup A k = lookup B k"
proof -
  have "(k, lookup A k) \<in> set A" using existence_from_lookup assms(1,2,5) by force
  then have 1: "(k, lookup A k) \<in> set B" using assms(4) by auto

  have "(k, lookup B k) \<in> set B" using existence_from_lookup assms by force
  then show ?thesis using 1 alist_values_equal assms(3) by force
qed

lemma alist_subset_values_equal:
  assumes "set l2 \<subseteq> set l1"
      and "is_alist l1"
      and "is_alist l2"
      and "k \<in> keys l2"
      and "(k, v) \<in> set l1"
    shows "(k, v) \<in> set l2"
proof -
  have 1: "(k, lookup l2 k) \<in> set l2" using assms(3-4) by (metis existence_from_lookup)
  then have "(k, lookup l2 k) \<in> set l1" using assms(1) by auto
  then have "lookup l2 k = v" using assms(2,5) by (metis lookup_from_existence)
  then show ?thesis using 1 by auto
qed

lemma lookup_in_snd: "k \<in> keys l \<Longrightarrow> (lookup l) k \<in> snd ` set l"
by (induct l) (auto simp add: lookup_def)

lemma lookup_map_in_snd: "set ks \<subseteq> keys l \<Longrightarrow> set (map (lookup l) ks) \<subseteq> snd ` set l"
by (metis (hide_lams, no_types) image_set image_subsetI in_mono lookup_in_snd)

lemma lookup_values_predicate:
  assumes "set ks \<subseteq> keys l"
      and "\<forall>(k, v) \<in> set l. P v"
    shows "\<forall>v \<in> set (map (lookup l) ks). P v"
proof -
  have "\<forall>v \<in> snd ` set l. P v" using assms(2) by auto
  then show ?thesis using lookup_map_in_snd[OF assms(1)] by (metis in_mono)
qed

end
