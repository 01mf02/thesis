theory AList_ext imports "~~/src/HOL/Library/AList_Mapping"
begin

definition is_alist :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "is_alist l \<equiv> distinct (map fst l)"

definition lookup :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "lookup l k \<equiv> the (Mapping.lookup (Mapping l) k)"

definition keys :: "('a \<times> 'b) list \<Rightarrow> 'a set" where
  "keys l \<equiv> Mapping.keys (Mapping l)"


lemma alist_fst_map: "is_alist l \<Longrightarrow> map fst l = map fst (f l) \<Longrightarrow> is_alist (f l)"
by (simp add: is_alist_def)

lemma alist_empty[simp]: "is_alist []"
by (simp add: is_alist_def)

lemma key_in_fst[simp]: "(k, v) \<in> A \<Longrightarrow> k \<in> fst ` A"
by (rule Set.image_eqI) simp_all

lemma lookup_from_existence: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> lookup l k = v"
by (simp add: lookup_def is_alist_def)

lemma existence_from_lookup: "is_alist l \<Longrightarrow> k \<in> keys l \<Longrightarrow> lookup l k = v \<Longrightarrow> (k, v) \<in> set l"
by (auto simp add: keys_def lookup_def is_alist_def)

lemma lookup_predicate: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> P k v \<Longrightarrow> P k (lookup l k)"
by (induct l) (auto simp add: lookup_def is_alist_def)

lemma lookup_forall: "\<forall>(k, v) \<in> set l. P k v \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> P k (lookup l k)"
by (induct l) (auto simp add: lookup_def)

lemma alist_keys_fst_set[simp]: "keys l = fst ` set l"
by (induct l) (auto simp add: keys_def)

(* TODO: improve proof speed! *)
lemma alist_partition_distr: "is_alist l \<Longrightarrow> (yes, no) = partition P l \<Longrightarrow> is_alist (yes @ no)"
unfolding is_alist_def apply (induct l arbitrary: yes no) by auto

lemma alist_distr: "is_alist (l1 @ l2) = (is_alist l1 \<and> is_alist l2 \<and> keys l1 \<inter> keys l2 = {})"
by (induct l1, auto simp add: is_alist_def)

lemma alist_values_equal: "is_alist l \<Longrightarrow> (k, v1) \<in> set l \<Longrightarrow> (k, v2) \<in> set l \<Longrightarrow> v1 = v2"
by (induct l) (auto simp add: is_alist_def)

lemma alist_filter: "is_alist l \<Longrightarrow> is_alist (filter P l)"
by (induct l) (auto simp add: is_alist_def)

lemma alist_map: "is_alist l \<Longrightarrow> is_alist (map (\<lambda>(a, b). (a, f b)) l)"
by (induct l) (auto simp add: is_alist_def)

lemma alist_map_values_equal:
  "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> (k, v') \<in> set (map (\<lambda>(k, v). (k, f k v)) l) \<Longrightarrow> v' = f k v"
by (induct l) (auto simp add: is_alist_def, force)


end
