header {* partition_iterate *}

theory Partition_iterate imports Helpers
begin

function partition_iterate where
  "partition_iterate P f a l = (case partition (P a) l of
       ([] , no) \<Rightarrow> (a, no)
     | (yes, no) \<Rightarrow> partition_iterate P f (f a yes) no)"
by auto

termination partition_iterate
apply (relation "measure (\<lambda>(p, f, a, l). length l)")
by (auto simp add: filter_length_smaller)

lemma pi_induct [case_names Base Step]:
  assumes B: "P (a, l)"
      and S: "\<And>a l yes no. P (a, l) \<Longrightarrow> partition (p a) l = (yes, no) \<Longrightarrow> P (f a yes, no)"
  shows "P (partition_iterate p f a l)" using B
proof (induct l arbitrary: a rule: length_induct)
  case (1 l a) then show ?case
  proof (cases "filter (p a) l")
    case Nil show ?thesis using 1(2) filter_one_empty_other_full[of "p a"] Nil by auto
  next
    case (Cons yesh yest)
    def no \<equiv> "filter (Not \<circ> p a) l"
    have "(\<forall>x. P (x, no) \<longrightarrow> P (partition_iterate p f x no))"
      using spec[OF 1(1), of no] filter_length_smaller[of _ _ p, OF Cons[symmetric]] no_def by auto
    then have "P (partition_iterate p f (f a (yesh#yest)) no)"
      using S[OF 1(2), of "yesh#yest"] Cons no_def by auto
    then show ?thesis using Cons no_def[symmetric] by simp
  qed
qed

lemma pi_invariant:
  assumes "\<And>a. f a [] = a"
    shows "partition_iterate P f a l =
           (\<lambda>(acc, no). (f acc (filter (P acc) no), no)) (partition_iterate P f a l)"
proof -
  def  pi \<equiv> "partition_iterate P f a l"
  def acc \<equiv> "fst pi"
  def  no \<equiv> "snd pi"

  have "filter (P acc) no = []" sorry
  then have "f acc (filter (P acc) no) = acc" using assms by auto
  then show ?thesis unfolding acc_def no_def pi_def by (case_tac "partition_iterate P f a l") auto
qed

end
