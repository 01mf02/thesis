theory Helpers imports Main
begin

lemma Min_predicate: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P x \<Longrightarrow> P (Min A)"
by auto

lemma fst_predicate: "P (fst p) \<Longrightarrow> (f, s) = p \<Longrightarrow> P f"
by auto


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


(*****************************************************************************
  partition_fold
 *****************************************************************************)

function partition_fold ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> ('a \<times> 'b list)" where
  "partition_fold P f a l = (case partition (P a) l of
       ([] , no) \<Rightarrow> (a, no)
     | (yes, no) \<Rightarrow> partition_fold P f (foldl f a yes) no)"
by auto

termination partition_fold
apply (relation "measure (\<lambda>(p, f, a, l). length l)")
by (auto simp add: filter_length_smaller)

lemma pf_induct:
  assumes N: "P (a, l)"
      and C: "\<And>a l yes no. P (a, l) \<Longrightarrow> partition (p a) l = (yes, no) \<Longrightarrow> yes \<noteq> [] \<Longrightarrow>
              P (foldl f a yes, no)"
  shows "P (partition_fold p f a l)" using N
proof (induct l arbitrary: a rule: length_induct)
  case (1 l a) then show ?case
  proof (cases "filter (p a) l")
    case Nil show ?thesis using 1(2) filter_one_empty_other_full[of "p a" l] Nil by auto
  next
    case (Cons yesh yest)
    def no \<equiv> "filter (Not \<circ> p a) l"
    have L: "length no < length l" using filter_length_smaller[of yesh yest p a l, OF Cons[symmetric]] no_def by auto
    have X: "(\<forall>x. P (x, no) \<longrightarrow> P (partition_fold p f x no))" using spec[OF 1(1), of no] L by auto
    have Y: "P (foldl f a (yesh # yest), no)" using C[OF 1(2), of "yesh#yest" no] no_def Cons by auto

    have C: "partition_fold p f a l = partition_fold p f (foldl f a (yesh # yest)) no" using Cons no_def[symmetric] by auto
    have "P (partition_fold p f (foldl f a (yesh#yest)) no)" using Y spec[OF X, of "foldl f a (yesh # yest)"] by auto
    then show ?thesis using C by auto
  qed
qed

end
