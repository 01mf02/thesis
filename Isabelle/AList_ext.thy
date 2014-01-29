header {* Extension of Association Lists *}

theory AList_ext imports
  "~~/src/HOL/Library/AList_Mapping"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_Lexorder"
begin

text {*
Association lists in Isabelle are implemented in the theory @{text AList} and extended by
the theory @{text AList_Mapping}, which links association lists with mappings.
However, we found the two theories to lack several useful lemmata, which we tried to remedy
in our extension of association lists.
Furthermore, we defined some short-hand notation for frequently used expressions.
*}

definition is_alist :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "is_alist l \<equiv> distinct (map fst l)"

definition lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "lookup l k \<equiv> the (Mapping.lookup (Mapping l) k)"

definition keys :: "('a \<times> 'b) list \<Rightarrow> 'a set" where
  "keys l \<equiv> Mapping.keys (Mapping l)"

(*<*)
definition values_related where
  "values_related r l1 l2 \<equiv> \<forall>(k1, v1) \<in> set l1. \<forall>(k2, v2) \<in> set l2. k1 = k2 \<longrightarrow> r v1 v2"

definition values_leq where
  "values_leq \<equiv> values_related less_eq"


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

lemma map_ran_smaller:
  assumes "\<forall>(k, v) \<in> set xs. f k v \<le> v"
      and "ys = map_ran f xs"
    shows "ys \<le> (xs :: ('a :: order \<times> 'b :: order) list)"
proof -
  have "length ys = length xs" using assms(2) unfolding map_ran_def by auto
  then show ?thesis using assms apply (induct rule: list_induct2) by auto
qed

lemma values_leq_cons:
  assumes "values_leq xs ys"
      and "x \<le> y"
      and "k \<notin> keys xs \<union> keys ys"
    shows "values_leq ((k, x) # xs) ((k,y) # ys)"
using assms unfolding values_leq_def values_related_def by auto

lemma map_ran_values_leq:
  assumes "\<forall>(k, v) \<in> set xs. f k v \<le> v"
      and "ys = map_ran f xs"
      and "is_alist xs"
    shows "values_leq ys xs"
proof -
  have "length ys = length xs" using assms(2) unfolding map_ran_def by auto
  then show ?thesis using assms proof (induct rule: list_induct2)
    case (Cons x xs y ys)
    then have "is_alist ys" using alist_distr[of "[y]" ys, simplified] by auto
    then have I: "values_leq xs ys" using Cons by auto

    def  k \<equiv> "fst y"
    def vx \<equiv> "snd x"
    def vy \<equiv> "snd y"

    have FF: "fst y = fst x" using Cons(4) by (metis (mono_tags) fst_conv list.inject map.simps(2)
      map_ran_def split_conv surjective_pairing)
    have XP: "x = (k, vx)" unfolding k_def vx_def FF by auto
    have YP: "y = (k, vy)" unfolding k_def vy_def by auto

    have XY: "vx = f k vy" using Cons(4) unfolding XP YP by auto
    have LE: "vx \<le> vy" unfolding XY using Cons(3) unfolding k_def vy_def by auto
    have AL: "is_alist (x # xs)" using distinct_map_ran[of "y # ys"] Cons(4-5)
      unfolding is_alist_def by auto

    have NX: "k \<notin> keys xs" using k_def FF AL   alist_distr[of "[x]" xs] by auto
    have NY: "k \<notin> keys ys" using k_def Cons(5) alist_distr[of "[y]" ys] by auto
    have NU: "k \<notin> keys xs \<union> keys ys" using NX NY by auto
    show ?case unfolding XP YP using values_leq_cons[OF I LE NU] .
  qed (auto simp add: values_leq_def values_related_def)
qed

end
