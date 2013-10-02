theory Grammar imports
  "Grammar_defs"
  "Helpers"
begin


(*****************************************************************************
  norm_sum
 *****************************************************************************)

lemma ns_singleton: "norm_sum ns [v] = fst (of_key ns v)"
by (simp add: norm_sum_def)


(*****************************************************************************
  norms_of_rules
 *****************************************************************************)

lemma "snd ` set (norms_of_rules norms rules) \<subseteq> set rules"
by (unfold norms_of_rules_def) auto

lemma nor_nonempty:
  "\<exists>(t, vs) \<in> set rules. \<forall>v \<in> set vs. v \<in> fst ` set norms \<Longrightarrow> norms_of_rules norms rules \<noteq> []"
by (simp add: norms_of_rules_def filter_empty_conv)

lemma "\<exists>a b. (a, b) \<in> set rules \<and> (\<forall>v\<in>set b. v \<in> fst ` set norms) \<Longrightarrow>
  snd (Min (set (norms_of_rules norms rules))) \<in> set rules"
by (rule Min_predicate) (auto simp add: norms_of_rules_def)


(*****************************************************************************
  min_norm_of_rules
 *****************************************************************************)

lemma
  assumes "\<exists>vs \<in> snd ` set rules. \<forall>v \<in> set vs. v \<in> fst ` set norms"
    shows "min_norm_of_rules norms rules \<in> set (norms_of_rules norms rules)" using assms
  apply (auto simp add: min_norm_of_rules_def norms_of_rules_def)
  apply (rule Min.closed)
by (auto simp add: filter_empty_conv min_def)


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma "length (norms_of_grammar gr) = length gr"
by (auto simp add: norms_of_grammar_def fold_concat_empty_init)

lemma nog_fst_is_gr_fst: "map fst (norms_of_grammar gr) = map fst gr"
by (auto simp add: norms_of_grammar_def
    key_fold_empty_init[of _ "\<lambda>(v, rules) norms. min_norm_of_rules norms rules"])

(* Do we need this? *)
(* lemma nog_fst_is_gr_fst:
  assumes "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "v \<in> fst ` set gr"
proof -
  have "fst ` set gr = set (map fst (norms_of_grammar gr))" by (simp add: nog_fst_is_gr_fst)
  then show ?thesis using assms by (auto simp add: key_in_fst)
qed *)


(*****************************************************************************
  norm_of_variables
 *****************************************************************************)

lemma nov_distr: "norm_of_variables gr (x @ y) = norm_of_variables gr x + norm_of_variables gr y"
by (simp add: norm_of_variables_def norm_sum_def)

lemma nov_distr': "norm_of_variables gr (x # y) = norm_of_variables gr [x] + norm_of_variables gr y"
by (rule nov_distr[of _ "[x]", simplified])

lemma nov_nog:
  assumes "gram_valid gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]"
  unfolding norm_of_variables_def norm_sum_def
  apply simp
sorry


(*****************************************************************************
  minimal_word_of_variables
 *****************************************************************************)

termination minimal_word_of_variables
  apply (relation "measure (\<lambda>(gr, vs). norm_of_variables gr vs)", auto)
  apply (subst nov_distr')
  apply (simp add: nov_distr nov_nog)
done


(*****************************************************************************
  eat_word
 *****************************************************************************)

(* The output word of eat_word is a postfix of the input word. *)
lemma eat_word_postfix: "\<exists>p. w = p @ fst (eat_word gr w v)"
by (induct gr w v rule: eat_word.induct, auto simp add: prefix_helper Let_def split_if_eq1)


(*****************************************************************************
  word_in_variables
 *****************************************************************************)

(* Postfixfreeness *)
lemma postfix_free:
  "gram_valid gr \<Longrightarrow> word_in_variables gr w v \<Longrightarrow> w' = w'h # w't \<Longrightarrow> \<not>(word_in_variables gr (w@w') v)"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)

(* Prefixfreeness *)
lemma prefix_free:
  assumes "gram_valid gr"
      and "word_in_variables gr w v"
    shows "\<not>(\<exists>w1 w2. w1 = w1h # w1t \<and> w2 = w2h # w2t \<and> w = w1 @ w2 \<and> word_in_variables gr w1 v)"
using assms
proof (induct gr w v rule: eat_word_induct)
  case (normal gr th tt vh vt)
  then show ?case
  proof (auto simp add: word_in_variables_def Let_def split_if_eq1)
    fix a  (* TODO: why do we fix "a" here? where is "a"? *)
    assume a1: "gram_valid gr"
       and a2: "eat_word gr (w1t @ w2h # w2t) (of_key (of_key gr vh) a @ vt) = ([], [])"
       and a3: "eat_word gr w1t (of_key (of_key gr vh) a @ vt) = ([], [])"
    show "False" using a2 postfix_free[simplified word_in_variables_def, OF a1 a3] by simp
  qed
qed (auto simp add: word_in_variables_def)

lemma "eat_word gr w v1 = (p, []) \<Longrightarrow> word_in_variables gr p v2 \<Longrightarrow> word_in_variables gr w (v1 @ v2)"
oops

lemma "word_in_variables gr w (v1 @ v2) \<Longrightarrow> word_in_variables gr (fst (eat_word gr w v1)) v2"
by (induct gr w v1 rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)

lemma "word_in_variables gr w v \<Longrightarrow> length w \<ge> length (minimal_word_of_variables gr v)"
oops

lemma no_variables_no_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) (auto simp add: word_in_variables_def)

lemma no_word_no_variables: "(word_in_variables gr [] v) = (v = [])"
by (case_tac v) (auto simp add: word_in_variables_def)

lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


(*****************************************************************************
  norm
 *****************************************************************************)

lemma no_variables_zero_norm: "norm gr [] = 0"
by (simp add: norm_def no_variables_no_word Min_eqI)

lemma "gram_valid gr \<Longrightarrow> set a \<union> set b \<subseteq> fst ` set gr \<Longrightarrow> norm gr (a@b) = norm gr a + norm gr b"
oops

lemma nov_calculates_norm:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> fst ` set gr"
    shows "norm_of_variables gr v = norm gr v"
proof (induct v)
  case Nil then show ?case
  by (auto simp add: no_variables_zero_norm norm_of_variables_def norm_sum_def)
next
  case (Cons a v)
    have CA: "a # v = [a] @ v" by simp
    show ?case unfolding CA
      apply (subst nov_distr)
      apply (simp only: norm_of_variables_def ns_singleton)
      sorry
qed

end
