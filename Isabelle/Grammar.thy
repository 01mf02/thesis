theory Grammar imports
  "Grammar_defs"
  "Helpers"
begin

(* The output word of eat_word is a postfix of the input word. *)
lemma eat_word_postfix: "\<exists>p. w = p @ fst (eat_word gr w v)"
by (induct gr w v rule: eat_word.induct, auto simp add: prefix_helper Let_def split_if_eq1)

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

lemma no_variables_zero_norm: "norm gr [] = 0"
by (simp add: norm_def no_variables_no_word Min_eqI)


lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


lemma "gram_valid gr \<Longrightarrow> set a \<union> set b \<subseteq> fst ` set gr \<Longrightarrow> norm gr (a@b) = norm gr a + norm gr b"
oops



lemma "length (norms_of_grammar gr) = length gr"
by (auto simp add: norms_of_grammar_def fold_concat_empty_init)

lemma norm_fst_is_gr_fst: "map fst (norms_of_grammar gr) = map fst gr"
by (auto simp add: norms_of_grammar_def
    key_fold_empty_init[of _ "\<lambda>(v, rules) norms. Min (set (norms_of_rules norms rules))"])

lemma "snd ` set (norms_of_rules norms rules) \<subseteq> set rules"
by (unfold norms_of_rules_def) auto

lemma nor_nonempty:
  "\<exists>(t, vs) \<in> set rules. \<forall>v \<in> set vs. v \<in> fst ` set norms \<Longrightarrow> norms_of_rules norms rules \<noteq> []"
by (simp add: norms_of_rules_def filter_empty_conv)

lemma nog_fst_is_gr_fst:
  assumes "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "v \<in> fst ` set gr"
proof -
  have "fst ` set gr = set (map fst (norms_of_grammar gr))" by (simp add: norm_fst_is_gr_fst)
  then show ?thesis using assms by (auto simp add: key_in_fst)
qed



lemma helper: "\<exists>a b. (a, b) \<in> set rules \<and> (\<forall>v\<in>set b. v \<in> fst ` set norms) \<Longrightarrow>
  snd (Min (set (norms_of_rules norms rules))) \<in> set rules"
by (rule Min_predicate) (auto simp add: norms_of_rules_def)


(* lemma
  assumes G: "gram_valid gr"
      and N: "(v, n, t, vs) \<in> set (norms_of_grammar gr)"
    shows "(t, vs) \<in> set (of_key gr v)"
proof -
  have XX: "\<forall>(k, v)\<in>set gr. is_alist v" using G by (auto simp add: gram_valid_def is_typical_alist_def)
  have XY: "v \<in> fst ` set gr" using G N by (simp add: nog_fst_is_gr_fst)
  have AL: "is_alist (of_key gr v)" using XX XY by (rule of_key_forall)

  have T1: "\<And>x. gram_valid gr \<Longrightarrow> x \<in> set gr \<Longrightarrow> case x of (v, rules) \<Rightarrow> of_key gr v = rules"
    by (auto simp add: of_key_from_existence gram_valid_def is_typical_alist_def)
  have T2: "\<And>P. \<forall>x\<in>set []. P x" by auto

  have ABC: "\<And>a norms. \<forall>(v, n, t, vs)\<in>set norms. t \<in> fst ` set (of_key gr v) \<Longrightarrow>
             \<exists>(n, t, vs) \<in> (set (norms_of_rules norms (of_key gr a))). True" sorry

  have XYZ: "\<And>a s ab ac ba. \<forall>(v, n, t, vs)\<in>set s. t \<in> fst ` set (of_key gr v) \<Longrightarrow>
             (ab, ac, ba) = Min (set (norms_of_rules s (of_key gr a))) \<Longrightarrow>
             ac \<in> fst ` set (of_key gr a)" using G ABC by (auto simp add: Min.closed nor_nonempty norms_of_rules_def) (* TODO! *)

  have T3: "\<And>x s. gram_valid gr \<Longrightarrow>
          case x of (v, rules) \<Rightarrow> of_key gr v = rules \<Longrightarrow>
          \<forall>(v, n, t, vs)\<in>set s. t \<in> fst ` set (of_key gr v) \<Longrightarrow>
          \<forall>(v, n, t, vs)\<in>set ((\<lambda>(v, rules) norms. norms @ [(v, Min (set (norms_of_rules norms rules)))]) x s).
             t \<in> fst ` set (of_key gr v)" using G XYZ by auto

  have SGX: "gram_valid gr \<Longrightarrow>
    \<forall>(v, n, t, vs)\<in>set (norms_of_grammar gr).
      t \<in> fst ` set (of_key gr v)" unfolding norms_of_grammar_def using T1 T2 T3
    by (rule fold_invariant[of _ "\<lambda>(v, rules). of_key gr v = rules"
      "\<lambda>s. \<forall>(v, n, t, vs) \<in> set s. t \<in> fst ` set (of_key gr v)" _])

  have SG: "\<forall>(v, n, t, vs) \<in> set (norms_of_grammar gr). t \<in> fst ` set (of_key gr v)"
    using G SGX by (auto simp add: norms_of_grammar_def)

  have EX1: "t \<in> fst ` set (of_key gr v)" using N SG by auto
  have EX2: "of_key (of_key gr v) t = vs" sorry
  show ?thesis using AL EX1 EX2 by (rule existence_from_of_key)
qed *)

(* lemma ns_distr: "norm_sum ns (x @ y) = norm_sum ns x + norm_sum ns y"
by (simp add: norm_sum_def)

lemma ns_distr': "norm_sum ns (x # y) = norm_sum ns [x] + norm_sum ns y"
by (rule ns_distr[of _ "[x]", simplified]) *)

lemma ns_singleton: "norm_sum ns [v] = fst (of_key ns v)"
by (simp add: norm_sum_def)

lemma nov_distr: "norm_of_variables gr (x @ y) = norm_of_variables gr x + norm_of_variables gr y"
by (simp add: norm_of_variables_def norm_sum_def)

lemma nov_distr': "norm_of_variables gr (x # y) = norm_of_variables gr [x] + norm_of_variables gr y"
by (rule nov_distr[of _ "[x]", simplified])

lemma nog_nov:
  assumes "gram_valid gr"
      and "(t, vs) = snd (of_key (norms_of_grammar gr) v)"
      and "(v, rules) \<in> set gr"
    shows "norm_of_variables gr vs < norm_of_variables gr [v]"
  unfolding norm_of_variables_def norm_sum_def
  apply simp
sorry

termination minimal_word_of_variables
  apply (relation "measure (\<lambda>(gr, vs). norm_of_variables gr vs)", auto)
  apply (subst nov_distr')
  apply (simp add: nov_distr nog_nov)
done


lemma nov_norm_equal:
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
