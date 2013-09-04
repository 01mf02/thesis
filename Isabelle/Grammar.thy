theory Grammar imports
  "~~/src/HOL/Library/AList"
  "~~/src/HOL/Library/Char_ord"
  "~~/src/HOL/Library/List_lexord"
  "~~/src/HOL/Library/Product_ord"
begin

type_synonym ('t, 'v) production_rule = "('t \<times> 'v list)"
type_synonym ('t, 'v) production_rules = "('t, 'v) production_rule list"
type_synonym ('t, 'v) grammar = "('v \<times> ('t, 'v) production_rules) list"

type_synonym ('t, 'v) norm_list = "('v \<times> (nat \<times> ('t, 'v) production_rule)) list"


definition is_alist :: "('a \<times> 'b) list \<Rightarrow> bool" where
  "is_alist l \<equiv> distinct (map fst l)"

definition is_typical_alist where
  "is_typical_alist l \<equiv> is_alist l \<and> l \<noteq> [] \<and> sorted (map fst l)"

definition of_key :: "('a \<times> 'b) list \<Rightarrow> 'a \<Rightarrow> 'b" where
  "of_key l k \<equiv> snd (hd (AList.restrict {k} l))"


lemma alist_subset_is_alist: "is_alist (x # l) \<Longrightarrow> is_alist l"
by (induct l) (auto simp add: is_alist_def)

lemma fst_existence: "(k, v) \<in> A \<Longrightarrow> k \<in> fst ` A"
by (rule Set.image_eqI) simp_all

lemma filter_nonex_key: "(k \<notin> fst ` set l) = ([(ka, v)\<leftarrow>l . ka = k] = [])"
by (induct l) auto

lemma restrict_single: "is_alist l \<Longrightarrow> ((k, v) \<in> set l) = (AList.restrict {k} l = [(k, v)])"
by (induct l) (auto simp add: restrict_eq is_alist_def filter_nonex_key)

lemma of_key_from_existence: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> of_key l k = v"
by (simp add: of_key_def restrict_single)

lemma existence_from_of_key: "is_alist l \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> of_key l k = v \<Longrightarrow> (k, v) \<in> set l"
  unfolding restrict_single
by (induct l) (auto simp add: of_key_def fst_existence alist_subset_is_alist restrict_eq
  filter_nonex_key is_alist_def)


definition gram_valid :: "('t::linorder, 'v::linorder) grammar \<Rightarrow> bool" where
  "gram_valid gr \<equiv> is_typical_alist gr \<and>
     (\<forall>g \<in> set gr. case g of (v, pr) \<Rightarrow> is_typical_alist pr \<and>
       (\<forall>vs \<in> set (map snd pr). \<forall>v' \<in> set vs. v' \<in> fst ` set gr) \<and>
       (\<exists>vs \<in> set (map snd pr). \<forall>v' \<in> set vs. v' < v))"

definition norm_of_variables :: "('t, 'v) norm_list \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_of_variables norms vars \<equiv> listsum (map fst (map (\<lambda>v. of_key norms v) vars))"

definition norm_list_of_rules ::
  "('t, 'v) norm_list \<Rightarrow> ('t, 'v) production_rules \<Rightarrow> (nat \<times> ('t, 'v) production_rule) list" where
  "norm_list_of_rules norms rules \<equiv>
     let valid_rules = filter (\<lambda>(t, vs). \<forall>v \<in> set vs. v \<in> fst ` set norms) rules in
     map (\<lambda>r. (1 + norm_of_variables norms (snd r), r)) valid_rules"

definition norm_of_production_rules ::
  "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> ('t, 'v) norm_list" where
  "norm_of_production_rules gr \<equiv> (fold (\<lambda>(v, rules). \<lambda>norms.
     let min_norm = Min (set (norm_list_of_rules norms rules)) in
     norms@[(v, min_norm)]) gr [])"

fun eat_word :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = of_key gr vh in
     if th \<in> fst ` set prods then eat_word gr tt ((of_key prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Min {length w | w. word_in_variables gr w v}"

(* The output word of eat_word is a postfix of the input word. *)
lemma "eat_word gr w v = (w', v') \<Longrightarrow> \<exists>p. w = p @ w'"
  apply (induct w arbitrary: v)
  apply auto
oops

(* Prefixfreeness *)
lemma "word_in_variables gr w v \<Longrightarrow> \<not>(\<exists>w'. w' = w'h # w't \<and> word_in_variables gr (w@w') v)"
  apply (auto simp add: word_in_variables_def)
  apply (cases w)
  apply auto
  apply (cases v)
  apply auto
  apply (case_tac "a \<in> fst ` set (of_key gr aa)")
  apply auto
oops

lemma "word_in_variables gr w (v1 @ v2) \<Longrightarrow> word_in_variables gr (fst (eat_word gr w v1)) v2"
oops


lemma no_variables_no_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) (auto simp add: word_in_variables_def)

lemma no_word_no_variables: "(word_in_variables gr [] v) = (v = [])"
by (case_tac v) (auto simp add: word_in_variables_def)

lemma no_variables_zero_norm: "norm gr [] = 0"
by (auto simp add: norm_def no_variables_no_word Min_eqI)

lemma "word_in_variables gr w (vh # vt) \<Longrightarrow>
       \<exists>w1 w2. w = w1 @ w2 \<and> word_in_variables gr w1 [vh]"
  apply (cases w)
  apply (auto simp add: no_word_no_variables)
  apply (case_tac "a \<in> fst ` set prods")
  apply (auto simp add: fst_existence)
  apply (intro exI)
oops

lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
  apply (cases w)
  apply (cases v)
  apply (auto simp add: no_variables_no_word)
  apply (cases v)
  apply (auto simp add: no_variables_no_word)
  (* apply (case_tac "a \<in> fst ` set (of_key gr aa)")
  apply auto *)
oops

lemma "norm gr (a@b) = norm gr a + norm gr b"
  apply (cases a)
  apply (auto simp add: norm_def no_variables_no_word)
oops

lemma fold_concat:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l l') = length l + length l'"
by (induct l arbitrary: l') simp_all

lemma fold_concat_empty_init:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l []) = length l"
by (simp add: fold_concat)

lemma "norm_of_production_rules gr = l \<Longrightarrow> length l = length gr"
by (auto simp add: norm_of_production_rules_def fold_concat_empty_init)


lemma key_fold:
  "\<forall>x p. f x p = p@[(fst x, g' x p)] \<Longrightarrow> map fst (fold f l l') = map fst l' @ map fst l"
by (induct l arbitrary: l') auto

lemma key_fold_empty_init:
  "\<forall>x p. f x p = p@[(fst x, g x p)] \<Longrightarrow> map fst (fold f l []) = map fst l"
  apply (rule subst [of "map fst [] @ map fst l"])
  apply simp
  apply (rule key_fold)
by auto

lemma norm_fst_is_gr_fst: "norm_of_production_rules gr = l \<Longrightarrow> map fst l = map fst gr"
by (auto simp add: norm_of_production_rules_def
    key_fold_empty_init[of _ "\<lambda>(v, rules) norms. Min (set (norm_list_of_rules norms rules))"])

lemma "norm_list_of_rules norms rules = l \<Longrightarrow> snd ` set l \<subseteq> set rules"
by (unfold norm_list_of_rules_def) auto

lemma nopr_fst_is_gr_fst:
  "gram_valid gr \<Longrightarrow> norm_of_production_rules gr = l \<Longrightarrow> \<forall>(v, _) \<in> set l. v \<in> fst ` set gr"
  apply (rule subst [of "set (map fst gr)"])
  apply simp
  apply (rule subst [of "(map fst l)"])
by (auto intro: norm_fst_is_gr_fst simp add: fst_existence)

(* lemma of_key_forall: "\<forall>(k, v)\<in>set l. P k v \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> P k (of_key l k)"
by (induct l) (auto simp add: of_key_def) *)

lemma "gram_valid gr \<Longrightarrow> norm_of_production_rules gr = l \<Longrightarrow>
  \<forall>(v, (_, (t, vs))) \<in> set l. (t, vs) \<in> set (of_key gr v)"
  (* unfolding norm_of_production_rules_def *)
  apply (auto simp add: gram_valid_def is_typical_alist_def)
  (* apply (rule subst [of "prods" "of_key gr a"])
  apply (rule sym)
  apply (rule of_key_semantics)
  apply auto *)
oops

lemma nov_distr: "norm_of_variables ns (x @ y) = norm_of_variables ns x + norm_of_variables ns y"
by (unfold norm_of_variables_def) auto

lemma "gram_valid gr \<Longrightarrow> set v \<subseteq> fst ` set gr \<Longrightarrow>
  norm_of_variables (norm_of_production_rules gr) v = norm gr v"
proof (induct v)
  case Nil then show ?case by (auto simp add: no_variables_zero_norm norm_of_variables_def)
next
  case (Cons a v)
    assume A: "gram_valid gr \<Longrightarrow> set v \<subseteq> fst ` set gr
      \<Longrightarrow> norm_of_variables (norm_of_production_rules gr) v = norm gr v"
    assume B: "gram_valid gr"
    assume C: "set (a # v) \<subseteq> fst ` set gr"
    have D: "a # v = [a] @ v" by simp
    show ?case unfolding D
      apply (simp only: nov_distr)
      sorry
qed

fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce gr v 0 = v"
| "norm_reduce gr [] (Suc p) = []"
| "norm_reduce gr (vh#vt) (Suc p) = (
     let (n, (_, v)) = of_key (norm_of_production_rules gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"


definition test_gr :: "(char, nat) grammar" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

value "gram_valid test_gr"
value "norm_of_production_rules test_gr"
value "word_in_variables test_gr ''a'' [0]"

end
