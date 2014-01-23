header {* Partition iteration algorithm *}

(*<*)
theory Partition_iterate imports Helpers
begin
(*>*)

text {*
The partition iteration algorithm @{text partition_iterate} takes four parameters:
\begin{itemize}
\item a predicate $P$,
\item an accumulator update function $f$,
\item an accumulator $a$,
\item and finally a list $l$.
\end{itemize}
In each iteration of the algorithm, it splits the input list $l$
into two lists $yes$ and $no$, which contain the list elements satisfying
$P\, a$ respectively those which do not. Then, we calculate a new
accumulator $a'$ using the accumulator update function $f$, i.e.
$a'=f\, a\, yes$, and call the algorithm again with the updated accumulator
$a'$ and those list elements which did not satisfy the predicate
$P\, a$, namely $no$. We continue this process as long as there
are list elements which satisfy the predicate; when this is no longer
the case, we return the last accumulator and those list elements which
never satisfied the predicate.

This algorithm can be used in many scenarios, most notably when there
exist dependencies between list elements which we need to resolve.
Example applications include:
\begin{itemize}
\item SAT of Horn formulas
\item Scheduling
\item Topological sorting
\end{itemize}
Note that the complexity of this algorithm is quadratic in the size $n$
of the input list, because in each iteration, we determine all the
elements of the input list which satisfy the predicate, and we may have
a maximal number of $n$ iterations.
*}

function partition_iterate ::
  "('a \<Rightarrow> 'b \<Rightarrow> bool) \<Rightarrow> ('a \<Rightarrow> 'b list \<Rightarrow> 'a) \<Rightarrow> 'a \<Rightarrow> 'b list \<Rightarrow> 'a \<times> 'b list" where
  "partition_iterate P f a l = (case partition (P a) l of
       ([] , no) \<Rightarrow> (a, no)
     | (yes, no) \<Rightarrow> partition_iterate P f (f a yes) no)"
by auto

termination partition_iterate
by (relation "measure (\<lambda>(p, f, a, l). length l)") (auto simp add: filter_length_smaller)

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

(*fun bla where
  "bla (n :: nat) = (if n = 0 then (n, 42 :: nat) else bla (n - 1))"

lemma assumes "bla n = (a, 42)" shows "a = 0"
  apply (rule bla.elims[OF assms])
  apply clarify
  apply (induct n)
  apply simp
  apply simp
done*)

lemma pi_termination_condition:
  assumes "partition_iterate P f a l = (ac, no)"
  shows "filter (P ac) no = []"
  apply (rule partition_iterate.elims[OF assms])
  apply clarify
  apply (induct l arbitrary: ac no rule: length_induct)
  apply simp
  (* TODO *)
sorry

lemma pi_termination_condition_busy:
  assumes "filter (P a) l = yesh # yest"
      and "partition_iterate P f a l = (ac, no)"
    shows "\<exists>a l. ac = f a l"
sorry

lemma pi_invariant_extended:
  assumes "f a [] = a"
      and "\<And>a l. f (f a l) [] = f a l"
    shows "partition_iterate P f a l =
           (\<lambda>(ac, no). (f ac (filter (P ac) no), no)) (partition_iterate P f a l)"
proof -
  def pi \<equiv> "partition_iterate P f a l"
  def ac \<equiv> "fst pi"
  def no \<equiv> "snd pi"
  have PI: "partition_iterate P f a l = (ac, no)" using pi_def ac_def no_def by auto

  have FE: "filter (P ac) no = []" using pi_termination_condition PI .
  then have "f ac (filter (P ac) no) = ac"
  proof (cases "filter (P a) l")
    case Nil then show ?thesis using assms(1) unfolding ac_def no_def pi_def by auto
  next
    case (Cons yesh yest)
    have "\<exists>a l. ac = f a l" using pi_termination_condition_busy[of P a l yesh yest, OF Cons PI] .
    then show ?thesis unfolding FE using assms(2) by auto
  qed
  then show ?thesis unfolding ac_def no_def pi_def by (case_tac "partition_iterate P f a l") auto
qed

lemma pi_invariant:
  assumes "\<And>a. f a [] = a"
    shows "partition_iterate P f a l =
           (\<lambda>(acc, no). (f acc (filter (P acc) no), no)) (partition_iterate P f a l)"
proof -
  def pi \<equiv> "partition_iterate P f a l"
  def ac \<equiv> "fst pi"
  def no \<equiv> "snd pi"
  have PI: "partition_iterate P f a l = (ac, no)" using pi_def ac_def no_def by auto

  have "filter (P ac) no = []" using pi_termination_condition PI .
  then have "f ac (filter (P ac) no) = ac" using assms by auto
  then show ?thesis unfolding ac_def no_def pi_def by (case_tac "partition_iterate P f a l") auto
qed

(*<*)end(*>*)
