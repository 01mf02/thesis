theory AList_ext imports "~~/src/HOL/Library/AList"
begin

definition is_alist :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "is_alist l \<equiv> distinct (map fst l)"

definition is_typical_alist where
  "is_typical_alist l \<equiv> is_alist l \<and> l \<noteq> [] \<and> sorted (map fst l)"

definition of_key :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "of_key l k \<equiv> snd (hd (AList.restrict {k} l))"


lemma alist_fst_map: "is_alist l \<Longrightarrow> map fst l = map fst (f l) \<Longrightarrow> is_alist (f l)"
by (simp add: is_alist_def)

lemma alist_subset_is_alist: "is_alist (x # l) \<Longrightarrow> is_alist l"
by (induct l) (auto simp add: is_alist_def)

lemma key_in_fst[simp]: "(k, v) \<in> A \<Longrightarrow> k \<in> fst ` A"
by (rule Set.image_eqI) simp_all

lemma key_filter_empty: "(k \<notin> fst ` set l) = ([(ka, v)\<leftarrow>l . ka = k] = [])"
by (induct l) auto

lemma restrict_single: "is_alist l \<Longrightarrow> ((k, v) \<in> set l) = (AList.restrict {k} l = [(k, v)])"
by (induct l) (auto simp add: restrict_eq is_alist_def key_filter_empty)

lemma of_key_from_existence: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> of_key l k = v"
by (simp add: of_key_def restrict_single)

lemma existence_from_of_key: "is_alist l \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> of_key l k = v \<Longrightarrow> (k, v) \<in> set l"
  unfolding restrict_single
by (induct l) (auto simp add: of_key_def restrict_eq key_filter_empty is_alist_def)

lemma of_key_predicate: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> P k v \<Longrightarrow> P k (of_key l k)"
by (induct l) (auto simp add: of_key_def is_alist_def)

lemma of_key_forall: "\<forall>(k, v) \<in> set l. P k v \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> P k (of_key l k)"
by (induct l) (auto simp add: of_key_def)

end
