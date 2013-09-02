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
  unfolding is_alist_def
by (induct l) auto


lemma fst_existence: "(k, v) \<in> A \<Longrightarrow> k \<in> fst ` A"
by (rule Set.image_eqI) simp_all

lemma filter_nonex_key: "(k \<notin> fst ` set l) = ([(ka, v)\<leftarrow>l . ka = k] = [])"
by (induct l) auto

(* TODO: this is a trivial consequence from fst_existence; how to get rid of it in proof below? *)
lemma helper_restr2: "k \<notin> fst ` set l \<Longrightarrow> (k, v) \<notin> set l"
by (induct l) auto

(* TODO: this also looks like a candidate for removal ... *)
lemma inclusion_helper: "set [x] \<subseteq> l \<Longrightarrow> x \<in> l"
by auto

lemma restrict_single: "is_alist l \<Longrightarrow> ((k, v) \<in> set l) = (AList.restrict {k} l = [(k, v)])"
  unfolding restrict_eq is_alist_def
  apply (rule iffI)

  apply (induct l)
  apply auto
  apply (simp add: filter_nonex_key)
  apply (rule notE)
  apply (rule helper_restr2)
  apply assumption+
  apply (rule notE)
  apply (rule helper_restr2)
  apply assumption+

  apply (rule inclusion_helper)
  apply (rule subst [of "[(ka, v)\<leftarrow>l . ka = k]" "[(k, v)]"])
  apply assumption
  apply (rule filter_is_subset)
done

lemma of_key_from_existence: "is_alist l \<Longrightarrow> (k, v) \<in> set l \<Longrightarrow> of_key l k = v"
  unfolding of_key_def
by (simp add: restrict_single)

lemma existence_from_of_key: "is_alist l \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> of_key l k = v \<Longrightarrow> (k, v) \<in> set l"
  unfolding of_key_def
  apply (simp add: restrict_single)
  apply (induct l)
  apply simp
  apply (case_tac "fst a \<in> fst ` set l")
  apply (simp only: is_alist_def)
  apply auto
  apply (simp only: restrict_eq)
  apply (simp add: filter_nonex_key)
  apply (drule alist_subset_is_alist)
  apply (drule fst_existence)
by assumption


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

fun word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr []    [] = True"
| "word_in_variables gr [] (_#_) = False"
| "word_in_variables gr (_#_) [] = False"
| "word_in_variables gr (th#tt) (vh#vt) = (
     let prods = of_key gr vh in
     if th \<in> fst ` set prods then word_in_variables gr tt ((of_key prods th) @ vt)
     else False)"



definition test_gr :: "(char, nat) grammar" where
  "test_gr =
   [(0, [(CHR ''a'', [])]),
    (1, [(CHR ''b'', [0])])]"

value "gram_valid test_gr"
value "norm_of_production_rules test_gr"
value "word_in_variables test_gr ''a'' [0]"


definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

definition norm :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm gr v \<equiv> Min {length w | w. word_in_variables gr w v}"

lemma no_variables_empty_word: "(word_in_variables gr w []) = (w = [])"
by (case_tac w) simp_all

lemma no_variables_zero_norm: "norm gr [] = 0"
  unfolding norm_def
  apply (rule Min_eqI)
  apply auto
  apply (rule finite_imageI)
by (simp add: no_variables_empty_word)

lemma wiv_split: "word_in_variables gr w v \<Longrightarrow> word_in_variables gr w' v' \<Longrightarrow>
  word_in_variables gr (w@w') (v@v')"
oops

lemma "norm gr (a@b) = norm gr a + norm gr b"
  apply (cases a)
  apply simp
  apply (unfold norm_def)
  apply (simp add: no_variables_empty_word)
  apply auto
oops

lemma fold_helper:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l l') = length l + length l'"
by (induct l arbitrary: l') simp_all

lemma fold_helper2:
  "(\<forall>l e. length (f e l) = Suc (length l)) \<Longrightarrow> length (fold f l []) = length l"
by (simp add: fold_helper)

lemma "norm_of_production_rules gr = l \<Longrightarrow> length l = length gr"
  unfolding norm_of_production_rules_def
  apply (drule sym)
  apply (simp)
  apply (rule fold_helper2)
  apply auto
done


lemma key_fold:
  "\<forall>x p. f x p = p@[(fst x, g' x p)] \<Longrightarrow> map fst (fold f l l') = map fst l' @ map fst l"
by (induct l arbitrary: l') auto

lemma key_fold_empty_init:
  "\<forall>x p. f x p = p@[(fst x, g x p)] \<Longrightarrow> map fst (fold f l []) = map fst l"
  apply (rule subst [of "map fst [] @ map fst l"])
  apply simp
  apply (rule key_fold)
  apply auto
done

(* TODO: fix this most ugly proof! *)
lemma norm_fst_is_gr_fst: "norm_of_production_rules gr = l \<Longrightarrow> map fst l = map fst gr"
  unfolding norm_of_production_rules_def
  apply auto
  apply (rule key_fold_empty_init [of "\<lambda>(v, rules) norms. norms @
    [(v, Min (set (norm_list_of_rules norms rules)))]" "\<lambda>(v, rules) norms. 
    Min (set (norm_list_of_rules norms rules))"])
  apply auto
done

lemma "norm_list_of_rules norms rules = l \<Longrightarrow> snd ` set l \<subseteq> set rules"
by (unfold norm_list_of_rules_def) auto


lemma nopr_fst_is_gr_fst:
  "gram_valid gr \<Longrightarrow> norm_of_production_rules gr = l \<Longrightarrow> \<forall>(v, _) \<in> set l. v \<in> fst ` set gr"
  apply (rule subst [of "set (map fst gr)"])
  apply simp
  apply (rule subst [of "(map fst l)"])
  apply (rule norm_fst_is_gr_fst)
  apply assumption
  apply (rule subst [of "fst ` set l"])
  apply auto
  apply (rule fst_existence)
by assumption

(* lemma of_key_forall: "\<forall>(k, v)\<in>set l. P k v \<Longrightarrow> k \<in> fst ` set l \<Longrightarrow> P k (of_key l k)"
  unfolding of_key_def
by (induct l) auto *)

lemma "gram_valid gr \<Longrightarrow> norm_of_production_rules gr = l \<Longrightarrow>
  \<forall>(v, (_, (t, vs))) \<in> set l. (t, vs) \<in> set (of_key gr v)"
  (* unfolding norm_of_production_rules_def *)
  apply (drule sym)
  apply auto
  unfolding gram_valid_def is_typical_alist_def
  apply auto
  (* apply (rule subst [of "prods" "of_key gr a"])
  apply (rule sym)
  apply (rule of_key_semantics)
  apply auto *)
oops

lemma nov_distr: "norm_of_variables ns (x @ y) = norm_of_variables ns x + norm_of_variables ns y"
by (unfold norm_of_variables_def) auto

lemma "gram_valid gr \<Longrightarrow> set v \<subseteq> fst ` set gr \<Longrightarrow>
  norm_of_variables (norm_of_production_rules gr) v = norm gr v"
  apply (induct v)
  apply (rule subst [of "0::nat"], rule sym)
  apply (rule no_variables_zero_norm)
  apply (simp only: norm_of_variables_def)
  apply auto
  (* apply (simp only: nov_distr) *) (* TODO! *)
oops

fun norm_reduce :: "('t :: linorder, 'v :: linorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce gr v 0 = v"
| "norm_reduce gr [] (Suc p) = []"
| "norm_reduce gr (vh#vt) (Suc p) = (
     let (n, (_, v)) = of_key (norm_of_production_rules gr) vh in
     if Suc p < n then (norm_reduce gr v p) @ vt
     else norm_reduce gr vt (Suc p - n))"


end
