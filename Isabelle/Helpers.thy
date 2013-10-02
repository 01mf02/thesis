theory Helpers imports Main
begin

lemma prefix_helper: "\<exists>p. x = p @ y \<Longrightarrow> \<exists>p. x' # x = p @ y"
by auto

lemma fold_concat:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l l') = length l + length l'"
by (induct l arbitrary: l') simp_all

lemma fold_concat_empty_init:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l []) = length l"
by (simp add: fold_concat)

lemma key_fold:
  "\<forall>x p. f x p = p@[(fst x, g' x p)] \<Longrightarrow> map fst (fold f l l') = map fst l' @ map fst l"
by (induct l arbitrary: l') auto

lemma key_fold_empty_init:
  "\<forall>x p. f x p = p@[(fst x, g x p)] \<Longrightarrow> map fst (fold f l []) = map fst l"
  apply (rule subst [of "map fst [] @ map fst l"])
  apply simp
  apply (rule key_fold)
by auto

lemma Min_predicate: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P x \<Longrightarrow> P (Min A)"
by auto


end
