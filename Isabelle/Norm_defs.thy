header {* Norm definitions *}

(*<*)
theory Norm_defs imports
  AList_ext
begin
(*>*)

subsection {* Types *}

type_synonym ('t, 'v) t_rule  = "'t \<times> 'v list"
type_synonym ('t, 'v) t_rules = "('t, 'v) t_rule list"
type_synonym ('t, 'v) v_rule  = "('v \<times> ('t, 'v) t_rules)"
type_synonym ('t, 'v) grammar = "('t, 'v) v_rule list"

text {*
In the formalisation of grammars, the simplest type is @{text t_rule}, which stands for terminal
rule. It consists of a terminal followed by a list of variables. An example of this could be the
rule $aXY$ or $b$.
The type @{text t_rules} then represents the sum of several terminal rules. An example of this is
$aXY + b$.
The type @{text v_rule} saves a variable along with a list of terminal rules, to note which
variable the terminal rules belong to. An example would be $X \to aXY + b$.
A grammar then is nothing else than a list of variables together with their associated terminal
rules, which is exactly the type @{text grammar}. An example could be $X \to aXY + b, Y \to c$.
*}

subsection {* Grammar *}

text {*
We then continue with the formalisation of simple deterministic grammars.

First, we demand that the grammar should be an association list, meaning
that for each variable of the grammar, there should be exactly one
list of terminal rules for that grammar. Furthermore, we also require
that for all terminals in a list of terminal rules, there is exactly
one list of variables for that variables. This corresponds to the
fact that our grammars are deterministic, meaning that for each variable,
we have maximally one terminal rule starting with the same terminal.

Finally we make sure that all variables contained in terminal rules
are really variables of that grammar.
*}

definition gram_sd :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_sd gr \<equiv> is_alist gr \<and>
     (\<forall>(v, rules) \<in> set gr. is_alist rules \<and>
       (\<forall>(t, vars) \<in> set rules. set vars \<subseteq> keys gr))"


subsection {* Norm *}

text {*
We use the @{text eat_word} function to verify whether a terminal word can
be produced from a variable word. For this purpose, we use two lists,
$S_{t}$ and $S_{v}$, which are initialised with the terminal and
variable words, respectively. We use these lists as stacks, so we
refer to them as stacks from now on.

In case that both stacks are non-empty, we obtain the top terminal
$t$ and the top variable $v$ from the stacks. Then we check whether
there exists a terminal rule for $v$ with the terminal $t$, i.e.
whether we can produce a terminal word from $v$ that starts with
$t$. If this is not the case, then we just return both stacks (which
will be non-empty). Otherwise, we obtain the terminal rule for $v$
starting with $t$ and extract the list of variables $v'$ from it.
Then we pop $t$ and $v$ from their stacks, push $v'$ onto the variable
stack and call the algorithm with the updated stacks.

In case that at least one of the stacks is empty, we just return both
stacks as is. This case can be caused by the following scenarios:
\begin{itemize}
\item Both stacks are empty: This means that the empty terminal word is
accepted by the empty variable word, therefore we return two empty
stacks. This means that when @{text eat_word} returns two empty stacks, then
the original terminal word can be produced from the original variable
word.
\item Only the terminal stack is empty: This indicates that the terminal
word was too short for the variable word; however, we could find a
terminal word $t'$ such that $t@t'$ can be produced by $v$.
\item Only the variable stack is empty: This means that the terminal word
cannot be produced from the variable word; however, a prefix $t'$
of $t$ (being strictly smaller than $t$) exists such that $t'$
can be produced by $v$.
\end{itemize}
However, most of the time we are only interested in whether a terminal
word can be produced by a variable word, which the function word\_in\_variables
does by verifying whether @{text eat_word} returns two empty lists.
*}

fun eat_word :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = lookup gr vh in
     if th \<in> keys prods then eat_word gr tt ((lookup prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

text {*
However, most of the time we are only interested in whether a terminal
word can be produced by a variable word, which the function @{text word_in_variables}
does by verifying whether @{text eat_word} returns two empty lists.
*}

definition word_in_variables :: "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

text {*
The function @{text words_of_variables} then denotes the set of terminal
words which can be produced by a given variable word. Note that this
set can be infinite, for example for the grammar $X\to a+bX$.
*}

definition words_of_variables :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"

text {*
Next, we formalise what it means for a grammar to be normed: It means
that for each variable word $v$ consisting of variables of the grammar,
there exists at least one (finite) terminal word which can be produced
from $v$.
*}

definition gram_normed_def :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_normed_def gr \<equiv> \<forall>v. set v \<subseteq> keys gr \<longrightarrow> (\<exists>w. word_in_variables gr w v)"

text {*
The predicate @{text gram_nsd_def} just expresses that a grammar is normed
simple-deterministic.
*}

definition gram_nsd_def :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_nsd_def gr \<equiv> gram_sd gr \<and> gram_normed_def gr"

text {*
Finally, we can define norms: Given a variable word $v$, we can obtain
the set of terminal words producible from $v$. The norm is then the
length of the shortest of these terminal words.
*}

definition norm_def :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_def gr v \<equiv> Least (\<lambda>l. l \<in> (length ` (words_of_variables gr v)))"


subsection {* Equivalence *}

text {*
In the future, we might reason not only about the norms of simple
deterministic grammars, but also about their equivalence.
*}

definition variables_equiv :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv> words_of_variables gr v1 = words_of_variables gr v2"

(*<*)end(*>*)
