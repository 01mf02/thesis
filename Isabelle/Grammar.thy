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
  assumes "\<exists>r \<in> set rules. rule_has_norm norms r"
    shows "norms_of_rules norms rules \<noteq> []"
using assms by (simp add: norms_of_rules_def filter_empty_conv)

lemma
  assumes "\<exists>r \<in> set rules. rule_has_norm norms r"
    shows "snd (Min (set (norms_of_rules norms rules))) \<in> set rules"
using assms by - (rule Min_predicate, auto simp add: norms_of_rules_def)


(*****************************************************************************
  min_norm_of_rules
 *****************************************************************************)

lemma
  assumes "\<exists>r \<in> set rules. rule_has_norm norms r"
    shows "min_norm_of_rules norms rules \<in> set (norms_of_rules norms rules)" using assms
  apply (auto simp add: min_norm_of_rules_def norms_of_rules_def)
  apply (rule Min.closed)
by (auto simp add: filter_empty_conv min_def)


(*****************************************************************************
  norms_of_grammar
 *****************************************************************************)

lemma "length (norms_of_grammar gr) = length gr"
by (auto simp add: norms_of_grammar_def fold_concat_empty_init)

lemma nog_fst_is_gr_fst: "map fst gr = map fst (norms_of_grammar gr)"
by (auto simp add: norms_of_grammar_def
    key_fold_empty_init[of _ "\<lambda>(v, rules) norms. min_norm_of_rules norms rules"])

lemma nog_alist: "gram_valid gr \<Longrightarrow> is_alist (norms_of_grammar gr)"
by (simp add: alist_fst_map gram_valid_def is_typical_alist_def nog_fst_is_gr_fst)

lemma
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
    shows "of_key (norms_of_grammar gr) v = min_norm_of_rules (norms_of_grammar gr) rules" using assms
  apply -
  apply (rule of_key_from_existence)
  apply (simp add: nog_alist)
oops


(*****************************************************************************
  norm_of_variables
 *****************************************************************************)

lemma nov_distr: "norm_of_variables gr (x @ y) = norm_of_variables gr x + norm_of_variables gr y"
by (simp add: norm_of_variables_def norm_sum_def)

lemma nov_distr': "norm_of_variables gr (x # y) = norm_of_variables gr [x] + norm_of_variables gr y"
by (rule nov_distr[of _ "[x]", simplified])

lemma nov_singleton:
  assumes "gram_valid gr"
      and "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "norm_of_variables gr [v] = n"
proof -
  have "norm_of_variables gr [v] = fst (of_key (norms_of_grammar gr) v)"  (is "_ = ?rhs")
    by (simp add: norm_of_variables_def norm_sum_def)
  also have "?rhs = fst (n, t, vs)" using assms
    by (simp_all add: of_key_from_existence nog_alist)
  finally show ?thesis by auto
qed

lemma nov_nog:
  assumes "gram_valid gr"
      and "(v, rules) \<in> set gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
    shows "norm_of_variables gr [v] = Suc (norm_of_variables gr vs)"
proof (simp add: norm_of_variables_def norm_sum_def)
  have "(of_key (norms_of_grammar gr) v) = min_norm_of_rules (norms_of_grammar gr) rules" sorry
  then show "fst (of_key (norms_of_grammar gr) v) = Suc(listsum (map (fst \<circ> of_key (norms_of_grammar gr)) vs))" sorry
qed

lemma nov_nog':
  assumes "gram_valid gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]" using assms
by (auto simp add: nov_nog)

lemma nov_greater_zero: "gram_valid gr \<Longrightarrow> (v, rules) \<in> set gr \<Longrightarrow> 
  0 < norm_of_variables gr [v]"
sorry


(*****************************************************************************
  minimal_word_of_variables
 *****************************************************************************)

termination minimal_word_of_variables
  apply (relation "measure (\<lambda>(gr, vs). norm_of_variables gr vs)", auto)
  apply (subst nov_distr')
  apply (auto simp add: add_commute add_strict_increasing2 nov_nog')
  apply (subst nov_distr')
by (auto simp add: nov_greater_zero)

(* TODO! *)
lemma helpy: "(case x of (y, z) \<Rightarrow> (f y z @ g)) = (case x of (y, z) \<Rightarrow> f y z) @ g"
sorry

lemma mwov_dist: "gram_valid gr \<Longrightarrow> set v1 \<subseteq> fst ` set gr \<Longrightarrow> set v2 \<subseteq> fst ` set gr \<Longrightarrow>
  minimal_word_of_variables gr (v1 @ v2) = minimal_word_of_variables gr v1 @ minimal_word_of_variables gr v2"
  apply (induct v1 arbitrary: v2)
  apply auto
  (* TODO: we can certainly solve this. why does helpy not work here? *)
oops

lemma mwov_len_calcs_nov:
  assumes "gram_valid gr"
      and "set v \<subseteq> fst ` set gr"
    shows "length (minimal_word_of_variables gr v) = norm_of_variables gr v"
sorry


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


lemma no_variables_no_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) (auto simp add: word_in_variables_def)

lemma no_word_no_variables: "(word_in_variables gr [] v) = (v = [])"
by (case_tac v) (auto simp add: word_in_variables_def)

lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


lemma wiv_mwov: "word_in_variables gr (minimal_word_of_variables gr v) v"
oops

lemma mwov_minimal_wiv:
  assumes "word_in_variables gr w v"
    shows "length (minimal_word_of_variables gr v) \<le> length w"
  apply (case_tac "w = minimal_word_of_variables gr v")
  apply auto
sorry


(*****************************************************************************
  words_of_variables
 *****************************************************************************)

lemma mwov_in_wov: "length (minimal_word_of_variables gr v) \<in> length ` words_of_variables gr v"
sorry

lemma mwov_min_wov:
  "\<And>x. x \<in> words_of_variables gr v \<Longrightarrow> length (minimal_word_of_variables gr v) \<le> length x"
by (auto simp add: words_of_variables_def mwov_minimal_wiv)


(*****************************************************************************
  norm
 *****************************************************************************)

(* lemma no_variables_zero_norm: "norm gr [] = 0"
by (simp add: norm_def no_variables_no_word words_of_variables_def Min_eqI) *)

(* lemma norm_distr:
  assumes "gram_valid gr"
      and "set (a@b) \<subseteq> fst ` set gr"
    shows "norm gr (a@b) = norm gr a + norm gr b"
oops *)

(* lemma nog_calculates_norm:
  assumes "gram_valid gr"
      and "v \<in> fst ` set gr"
    shows "fst (of_key (norms_of_grammar gr) a) = norm gr ([a])"
oops *)

lemma mwov_len_calcs_norm: "norm gr v = length (minimal_word_of_variables gr v)"
  unfolding norm_def
  (* TODO: big problem here: We need the conclusion of Min_eqI, but its premise that the set of
     words be _finite_ can not be fulfilled! *)
  apply (rule Min_eqI)
  apply (auto simp add: mwov_in_wov mwov_min_wov)
sorry

lemma nov_calculates_norm:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> fst ` set gr"
    shows "norm_of_variables gr v = norm gr v" using assms
by (auto simp add: mwov_len_calcs_norm mwov_len_calcs_nov)

(* lemma nov_calculates_norm:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> fst ` set gr"
    shows "norm_of_variables gr v = norm gr v" using assms
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
qed *)

end
