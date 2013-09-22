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

lemmas eat_word_induct = eat_word.induct[case_names normal nil_word nil_vars]

function minimal_word_of_variables where
  "minimal_word_of_variables gr [] = []"
| "minimal_word_of_variables gr (vh#vt) = (
     if gram_valid gr then
       let norms = norm_of_production_rules gr in
       let (t, vars) = snd (of_key norms vh) in
       t#(minimal_word_of_variables gr (vars@vt))
     else [])"
by pat_completeness auto
termination
  (* apply (relation "\<lambda>x. ...") *)
  (* See functions.pdf. *)
oops

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Min {length w | w. word_in_variables gr w v}"


lemma prefix_helper: "\<exists>p. x = p @ y \<Longrightarrow> \<exists>p. x' # x = p @ y"
by auto

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

(* lemma "eat_word gr w v = (postf, []) \<Longrightarrow> \<exists>pref. w = pref @ postf \<and> word_in_variables gr pref v"
oops *)

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
by (auto simp add: norm_def no_variables_no_word Min_eqI)


lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
by (induct gr w v rule: eat_word.induct, auto simp add: word_in_variables_def Let_def split_if_eq1)


lemma "gram_valid gr \<Longrightarrow> set a \<union> set b \<subseteq> fst ` set gr \<Longrightarrow> norm gr (a@b) = norm gr a + norm gr b"
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
  "(v, n, t, vs) \<in> set (norm_of_production_rules gr) \<Longrightarrow> v \<in> fst ` set gr"
  apply (rule subst [of "set (map fst gr)"])
  apply simp
  apply (rule subst [of "(map fst (norm_of_production_rules gr))"])
by (auto intro: norm_fst_is_gr_fst simp add: fst_existence)

lemma of_key_predicate: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> P k v \<Longrightarrow> P k (of_key l k)"
by (induct l) (auto simp add: of_key_def is_alist_def fst_existence)

lemma of_key_forall: "\<forall>(k, v) \<in> set l. P k v \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> P k (of_key l k)"
by (induct l) (auto simp add: of_key_def is_alist_def fst_existence)

lemma Min_predicate: "finite A \<Longrightarrow> A \<noteq> {} \<Longrightarrow> \<forall>x \<in> A. P x \<Longrightarrow> P (Min A)"
by auto

lemma helper: "\<exists>a b. (a, b) \<in> set rules \<and> (\<forall>v\<in>set b. v \<in> fst ` set norms) \<Longrightarrow>
  snd (Min (set (norm_list_of_rules norms rules))) \<in> set rules"
by (rule Min_predicate) (auto simp add: norm_list_of_rules_def)

lemma helper3:
  "(\<And>x p. f x p = p @ [g x p]) \<Longrightarrow> (\<And>x p. P (g x p)) \<Longrightarrow> (\<forall>x \<in> set (fold f l []). P x)"
by (rule fold_invariant) auto

(* TODO: Can't we conclude that in an easier way from helper3? *)
lemma helper3':
  assumes F: "(\<And>x p. f x p = p @ [g x p])"
      and G: "(\<And>x p. P (g x p))"
      and L: "x \<in> set (fold f l [])"
    shows "P x"
proof -
  have "\<forall>x \<in> set (fold f l []). P x" using F G by (rule helper3)
  then show "P x" using L by (auto simp add: ballE)
qed

lemma "gram_valid gr \<Longrightarrow> (v, n, t, vs) \<in> set (norm_of_production_rules gr) \<Longrightarrow>
  (t, vs) \<in> set (of_key gr v)"
  apply (rule existence_from_of_key)
  apply (rule of_key_forall [of gr])
  apply (simp add: gram_valid_def is_typical_alist_def)
  apply (auto simp add: nopr_fst_is_gr_fst)
  apply (auto simp add: norm_of_production_rules_def)
  (* TODO: I think most machinery is in place, now we have to figure out the assembly.
     Use "helper"! *)
oops

lemma nov_distr: "norm_of_variables ns (x @ y) = norm_of_variables ns x + norm_of_variables ns y"
by (unfold norm_of_variables_def) auto

lemma nov_singleton: "norm_of_variables ns [v] = fst (of_key ns v)"
by (auto simp add: norm_of_variables_def)

lemma nov_norm_equal:
  assumes G: "gram_valid gr"
      and V: "set v \<subseteq> fst ` set gr"
    shows "norm_of_variables (norm_of_production_rules gr) v = norm gr v"
proof (induct v)
  case Nil then show ?case by (auto simp add: no_variables_zero_norm norm_of_variables_def)
next
  case (Cons a v)
    have CA: "a # v = [a] @ v" by simp
    show ?case unfolding CA
      apply (simp only: nov_distr nov_singleton)
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
