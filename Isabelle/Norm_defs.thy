header {* Norm definitions *}

theory Norm_defs imports
  AList_ext
begin

subsection {* Types *}

text {*
In the formalisation of grammars, the simplest type is @{text t_rule}, which stands for terminal
rule.
\footnote{While the name "terminal rule" might be misleading, we chose this name analogously to the
later defined type @{text v_rule}. The idea behind this is that a variable rule stores a variable
and associated data, while a terminal rule stores a terminal and associated data.}
It consists of a terminal followed by a list of variables. An example of this could be the
rule $aXY$ or $b$.
The type @{text t_rules} then represents the sum of several terminal rules. An example of this is
$aXY + b$.
The type @{text v_rule} contains a variable along with a list of terminal rules, to note which
variable the terminal rules belong to. An example would be $X \to aXY + b$.
A @{text grammar} then is a list of variables together with their associated terminal
rules. An example could be $X \to aXY + b, Y \to c$.
*}

type_synonym ('t, 'v) t_rule  = "'t \<times> 'v list"
type_synonym ('t, 'v) t_rules = "('t, 'v) t_rule list"
type_synonym ('t, 'v) v_rule  = "'v \<times> ('t, 'v) t_rules"
type_synonym ('t, 'v) grammar = "('t, 'v) v_rule list"

subsection {* Grammar *}

text {*
We continue with the formalisation of simple deterministic grammars.

First, we demand that the grammar should be an association list, meaning
that for each variable of the grammar, there should be exactly one
list of terminal rules for that variable. Furthermore, we require
that all terminal rules for a variable start with a different terminal.
This corresponds to the fact that our grammars are deterministic. Finally,
we make sure that all variables contained in terminal rules are really variables of that grammar.
*}

definition gram_sd :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_sd gr \<equiv> is_alist gr \<and>
     (\<forall>(v, rules) \<in> set gr. is_alist rules \<and>
       (\<forall>(t, vars) \<in> set rules. set vars \<subseteq> keys gr))"


subsection {* Norm *}

text {*
To verify whether a given variable word can produce a given terminal word,
we define a function called @{text eat_word}. This function takes a
simple deterministic grammar, a terminal word and a variable word, and
returns the pair of empty lists if the variable word produces the terminal word.
*}

fun eat_word ::
  "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow>
   ('t list \<times> 'v list)" where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = lookup gr vh in
     if th \<in> keys prods then eat_word gr tt ((lookup prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

text {*
In case that both terminal and variable words are non-empty, we obtain the first terminal
@{term th} and the first variable @{term vh} from the words. Then we check whether
there exists a terminal rule for @{term vh} with the terminal @{term th}, i.e.
whether we can produce a terminal word from @{term vh} that starts with
@{term th}. If this is not the case, then we just return both words (which
will be non-empty). Otherwise, we obtain the terminal rule for @{term vh}
starting with @{term th} and extract its associated list of variables.
Then we remove @{term th} and @{term vh} from the beginning of the words,
prepend the list of variables to the variable word and call the algorithm with the updated words.

In case at least one of the words is empty, we return both
words as is. This can be caused by the following scenarios:
\begin{itemize}
\item Both words are empty: This means that the empty terminal word is
accepted by the empty variable word, therefore we return two empty
words. This means that when @{text eat_word} returns two empty words, then
the original terminal word can be produced from the original variable
word.
\item Only the terminal word is empty: This indicates that the original terminal
word was too short for the original variable word; however, we could find a
terminal word @{term t'} such that @{term "t@t'"} can be produced by @{term v}.
\item Only the variable word is empty: This means that the terminal word
cannot be produced from the variable word; however, a strict prefix @{term t'}
of @{term t} exists such that @{term t'} can be produced by @{term v}.
\end{itemize}

However, most of the time we are only interested in whether a terminal
word can be produced by a variable word, which the function @{text word_in_variables}
does by verifying whether @{text eat_word} returns two empty lists.
*}

(*<*)
definition word_in_variables ::
  "('t, 'v) grammar \<Rightarrow> 't list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

text {*
The function @{text words_of_variables} then denotes the set of terminal
words which can be produced by a given variable word. Note that this
set can be infinite, for example for the grammar $X\to a+bX$.
*}

definition words_of_variables ::
  "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 't list set" where
  "words_of_variables gr v \<equiv> {w | w. word_in_variables gr w v}"
(*>*)

text {*
Next, we formalise what it means for a grammar to be normed: It means
that for each variable word @{term v} consisting of variables of the grammar,
there exists at least one (finite) terminal word which can be produced
from @{term v}. @{term word_in_variables} is a function that verifies via
@{term eat_word} whether a terminal word can be produced by a variable word.
*}

definition gram_normed_def :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_normed_def gr \<equiv>
     \<forall>v. set v \<subseteq> keys gr \<longrightarrow> (\<exists>w. word_in_variables gr w v)"

text {*
The predicate @{text gram_nsd_def} expresses that a grammar is normed
and simple deterministic.
*}

definition gram_nsd_def :: "('t, 'v) grammar \<Rightarrow> bool" where
  "gram_nsd_def gr \<equiv> gram_sd gr \<and> gram_normed_def gr"

text {*
Finally, we can define norms: Using the function @{term words_of_variables},
which uses @{term eat_word}, we obtain the set of terminal words producible
from a given variable word @{term v}.
The norm is then the length of the shortest of these terminal words.
*}

definition norm_def :: "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> nat" where
  "norm_def gr v \<equiv>
     Least (\<lambda>l. l \<in> (length ` (words_of_variables gr v)))"


(*<*)
subsection {* Equivalence *}

text {*
In the future, we might reason not only about the norms of simple
deterministic grammars, but also about their equivalence.
*}

definition variables_equiv ::
  "('t, 'v) grammar \<Rightarrow> 'v list \<Rightarrow> 'v list \<Rightarrow> bool" where
  "variables_equiv gr v1 v2 \<equiv>
     words_of_variables gr v1 = words_of_variables gr v2"
(*>*)

end
