header {* Norm functions *}

theory Norm_funs imports
  Norm_defs
  Partition_iterate
begin


subsection {* Types *}

text {*
Similarly to the types used in the formalisation of norms, we have
defined several norm types on top.

The most basic type here is @{text t_rule_norm}, which associates a natural
number (the norm) with a terminal rule. For example, given the terminal
rule $a$, the norm of it would be $(1,a)$.

Based on this, @{text t_rules_norms} stores the norms of several terminal
rules. For example, given the rules $a+bX+cY$, the associated norms
could be $\left[(1,a),(42,bX)\right]$. Note that not every terminal
rule of a variable must have a finite norm, so in case we cannot find
a finite norm for a terminal rule, we ignore it.

For @{text v_rule_norm}, we might expect that it should be the product type
of @{text 'v} and @{text t_rules_norms}, analogously to the definition of @{text v_rule}.
However, we see that it is the product type of @{text 'v} and @{text t_rule_norm}.
This is because for the norm of a variable, we are only interested
in the \emph{smallest} norm of each of its terminal rules, and not
in all rules of its its terminal rules. Therefore, we aim to use this
type to store only the smallest norm of each variable.

Finally, @{text grammar_norms} is designated to hold the norms of all variables
possessing a finite norm.
*}

type_synonym ('t, 'v) t_rule_norm   = "nat \<times> ('t, 'v) t_rule"
type_synonym ('t, 'v) t_rules_norms = "('t, 'v) t_rule_norm list"
type_synonym ('t, 'v) v_rule_norm   = "('v \<times> ('t, 'v) t_rule_norm)"
type_synonym ('t, 'v) grammar_norms = "('t, 'v) v_rule_norm list"


subsection {* Norm orders *}

definition t_rule_norm_strip_vs where
  "t_rule_norm_strip_vs \<equiv> \<lambda>(n, t, vs). (n, t)"

definition v_rule_norm_strip_vs where
  "v_rule_norm_strip_vs \<equiv> \<lambda>(v, n, t, vs). (v, n, t)"

definition t_rule_norm_less ::
  "('t :: wellorder, 'v :: wellorder) t_rule_norm \<Rightarrow> ('t, 'v) t_rule_norm \<Rightarrow> bool" where
  "t_rule_norm_less n1 n2 \<equiv> t_rule_norm_strip_vs n1 < t_rule_norm_strip_vs n2"

definition t_rule_norm_less_eq ::
  "('t :: wellorder, 'v :: wellorder) t_rule_norm \<Rightarrow> ('t, 'v) t_rule_norm \<Rightarrow> bool" where
  "t_rule_norm_less_eq n1 n2 \<equiv> t_rule_norm_strip_vs n1 \<le> t_rule_norm_strip_vs n2"

definition v_rule_norm_less ::
  "('t :: wellorder, 'v :: wellorder) v_rule_norm \<Rightarrow> ('t, 'v) v_rule_norm \<Rightarrow> bool" where
  "v_rule_norm_less n1 n2 \<equiv> v_rule_norm_strip_vs n1 < v_rule_norm_strip_vs n2"

definition v_rule_norm_less_eq ::
  "('t :: wellorder, 'v :: wellorder) v_rule_norm \<Rightarrow> ('t, 'v) v_rule_norm \<Rightarrow> bool" where
  "v_rule_norm_less_eq n1 n2 \<equiv> v_rule_norm_strip_vs n1 \<le> v_rule_norm_strip_vs n2"

definition v_rule_norm_ord where
  "v_rule_norm_ord = {(n1, n2). v_rule_norm_less n1 n2}"

definition grammar_norms_ord ::
  "(('t :: wellorder, 'v :: wellorder) grammar_norms \<times> ('t, 'v) grammar_norms) set" where
  "grammar_norms_ord = lex v_rule_norm_ord"


subsection {* Functions *}

text {*
@{text norm_sum} sums up the supplied norms for a given variable word.
*}

definition norm_sum :: "('t, 'v) grammar_norms \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_sum norms vars \<equiv> \<Sum>(n, t, vs)\<leftarrow>map (lookup norms) vars. n"

text {*
@{text t_rule_has_norm} determines whether a given terminal rule can be
normed using an existing set of norms.
*}

definition t_rule_has_norm ::
  "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rule \<Rightarrow> bool" where
  "t_rule_has_norm norms \<equiv> \<lambda>(t, vs). set vs \<subseteq> keys norms"

definition t_rules_have_norm ::
  "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rules \<Rightarrow> bool" where
  "t_rules_have_norm norms rules \<equiv>
     \<exists>r \<in> set rules. t_rule_has_norm norms r"

text {*
@{text norm_of_t_rule} calculates the norm of a terminal rule, by summing
up the norms of all variables of the rule and by adding 1 to the result.
The latter is to account for the terminal which has norm 1.

Along with the length of the smallest terminal word, the norm also
stores the terminal rule. This is done so that we can later easily
construct the shortest terminal word producible by a variable word.
*}

definition norm_of_t_rule ::
  "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rule \<Rightarrow>
   ('t, 'v) t_rule_norm" where
  "norm_of_t_rule norms \<equiv> \<lambda>(t, vs). (Suc (norm_sum norms vs), t, vs)"

text {*
@{text norms_of_t_rules} calculates the norms of a set of terminal rules.
It just considers those rules which can be normed.
*}

definition norms_of_t_rules ::
  "('t, 'v) grammar_norms \<Rightarrow> ('t, 'v) t_rules \<Rightarrow>
   ('t, 'v) t_rules_norms" where
  "norms_of_t_rules norms rules \<equiv>
     [norm_of_t_rule norms r. r <- rules, t_rule_has_norm norms r]"

definition min_norm_of_t_rules ::
  "('t::linorder, 'v::linorder) grammar_norms \<Rightarrow> ('t, 'v) t_rules \<Rightarrow>
   ('t, 'v) t_rule_norm" where
  "min_norm_of_t_rules norms rules \<equiv>
     Min (set (norms_of_t_rules norms rules))"

definition v_rule_has_norm ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) v_rule \<Rightarrow>
   bool" where
  "v_rule_has_norm norms \<equiv> \<lambda>(v, rules). t_rules_have_norm norms rules"

definition mnotr_map ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   ('t, 'v) grammar_norms" where
  "mnotr_map norms =
     map (\<lambda>(v, rules). (v, min_norm_of_t_rules norms rules))"

text {*
When given a set of norms and a grammar, @{text v_rules_of_norms} obtains
a grammar consisting only of rules for those variables which are present
in the norms. Note that the resulting grammar does not have to be
a valid simple deterministic grammar, as certain terminal rules in
it may still contain references to variables which are not present
anymore in the new grammar (because they did not appear in the norm).

This function will later be useful in the refinement of norms.
*}

definition v_rules_of_norms ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   ('t, 'v) grammar" where
  "v_rules_of_norms norms gr =
     map (\<lambda>(v, n, t, vs). (v, lookup gr v)) norms"

text {*
@{text add_norms} takes a set of norms and variable rules (which should be
normable with the norms) and calculates an updated set of norms.
*}

definition add_norms ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   ('t, 'v) grammar_norms" where
  "add_norms norms yes = norms @ (mnotr_map norms yes)"

text {*
The norm iteration algorithm starts with a set of variable rules,
initially gr, and a set of norms, initially $\left[\right]$. Then,
in each iteration, the algorithm calculates the variable rules which
can be normed and those which cannot be normed, then calculates new
norms for those rules which can be normed, and recurses with the set
of rules which could not be normed and the updated norms. As sonn
as no rule can be normed anymore, the algorithm returns the most recent
norms and the remaining variable rules which could not be normed.

Note that this algorithm does not always calculate the final norms
of the grammar, as the norms can be non-minimal. For that, we later
minimise the obtained norms.
*}

definition iterate_norms ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow>
   (('t, 'v) grammar_norms \<times> ('t, 'v) grammar)" where
  "iterate_norms gr = partition_iterate v_rule_has_norm add_norms [] gr"

(*<*)
definition itno_invariant where
  "itno_invariant gr norms rest \<equiv> set rest \<subseteq> set gr \<and> keys gr = keys norms \<union> keys rest"

definition itno_invariant_sd where
  "itno_invariant_sd gr norms rest \<equiv> is_alist norms \<and> is_alist rest \<and> keys rest \<inter> keys norms = {}"

definition itno_invariant_sd_member where
  "itno_invariant_sd_member norms v rules \<equiv>
     t_rules_have_norm norms rules \<and> lookup norms v \<in> set (norms_of_t_rules norms rules)"

definition nog_invariant where
  "nog_invariant norms v rules \<equiv>
     t_rules_have_norm norms rules \<and> (v, min_norm_of_t_rules norms rules) \<in> set norms"

definition nog_invariant_n_t_vs where
  "nog_invariant_n_t_vs norms rules n t vs \<equiv>
     t_rules_have_norm norms rules \<and> (n, t, vs) = min_norm_of_t_rules norms rules"
(*>*)

definition gram_normed_fun ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow> bool" where
  "gram_normed_fun gr \<equiv> snd (iterate_norms gr) = []"

definition gram_nsd_fun ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow> bool" where
  "gram_nsd_fun gr \<equiv> gram_sd gr \<and> gram_normed_fun gr"

text {*
@{text refine_norms} obtains all rules of variables present in the set of
norms, and recalculates the norms of these rules.

Note that if the supplied norms have not been produced by @{text iterate_norms},
then the resulting norms may be greater than the supplied norms! For
example, if we have the grammar $A\to a$ and the norms $(A,0)$,
then the refinement will calculate $(A,1)$ to be the new norm, which
is bigger than the original norm. In any case, after a finite number
of applications of @{text refine_norms}, the norms will always decrease or
rest the same.
*}

definition refine_norms ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   ('t, 'v) grammar_norms" where
  "refine_norms norms gr = mnotr_map norms (v_rules_of_norms norms gr)"

definition rn_invariant ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   bool" where
  "rn_invariant norms gr \<equiv> (\<forall>(v, norm) \<in> set norms.
     t_rule_norm_less_eq (min_norm_of_t_rules norms (lookup gr v)) norm) \<and>
     is_alist norms \<and> keys norms \<subseteq> keys gr"

text {*
@{text minimise_norms} applies @{text refine_norms} until the resulting norms do
not change anymore. To ease the termination proof, the function employs
some conditional guards.
*}

function minimise_norms ::
  "('t::wellorder, 'v::wellorder) grammar_norms \<Rightarrow> ('t, 'v) grammar \<Rightarrow>
   ('t, 'v) grammar_norms" where
  "minimise_norms norms gr = (
     if is_alist gr \<and> rn_invariant norms gr \<and>
        refine_norms norms gr \<noteq> norms then
       minimise_norms (refine_norms norms gr) gr
     else norms)"
by auto

definition norms_of_grammar ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow>
   ('t, 'v) grammar_norms" where
  "norms_of_grammar gr \<equiv> minimise_norms (fst (iterate_norms gr)) gr"

text {*
@{text norm_fun} is the central norm calculation function.
*}

definition norm_fun ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_fun gr vars \<equiv> norm_sum (norms_of_grammar gr) vars"

text {*
@{text min_word_of_variables} obtains the shortest terminal word producible
by a variable word. This is not used in the norm calculation, but
for the correctness proof of @{text norm_fun}.
*}

function min_word_of_variables ::
  "('t :: wellorder, 'v :: wellorder) grammar \<Rightarrow> 'v list \<Rightarrow>
   't list" where
  "min_word_of_variables gr vars = (
     if gram_nsd_fun gr \<and> set vars \<subseteq> keys gr then
       concat (map (\<lambda>(n, t, vs). t # (min_word_of_variables gr vs))
                   (map (lookup (norms_of_grammar gr)) vars))
     else [])"
by auto


(*<*)
subsection {* Norm reduction *}

fun norm_reduce :: "('t :: wellorder, 'v :: wellorder) grammar_norms \<Rightarrow> 'v list \<Rightarrow> nat \<Rightarrow> 'v list" where
  "norm_reduce norms v 0 = v"
| "norm_reduce norms [] (Suc p) = []"
| "norm_reduce norms (vh#vt) (Suc p) = (
     let (n, _, v) = lookup norms vh in
     if Suc p < n then (norm_reduce norms v p) @ vt
     else norm_reduce norms vt (Suc p - n))"
(*>*)

end
