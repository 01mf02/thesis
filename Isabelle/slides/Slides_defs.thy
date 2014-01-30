theory Slides_defs imports
  "../Norm_defs"
  "~~/src/HOL/Library/LaTeXsugar"
begin


text_raw {*
\lyxframe{Norm definition pt. 1}

\begin{block}{Simple deterministic grammars}
*}

definition gram_sd where
 "gram_sd gr \<equiv> is_alist gr \<and>
   (\<forall>(v, rules) \<in> set gr. is_alist rules \<and> rules \<noteq> [] \<and>
    (\<forall>(t, vars) \<in> set rules. set vars \<subseteq> keys gr))"

text_raw {*
\end{block}

\begin{block}{Acceptance of terminal words by variables}
*}

fun eat_word where
  "eat_word gr (th#tt) (vh#vt) = (
     let prods = lookup gr vh in
     if th \<in> keys prods then
       eat_word gr tt ((lookup prods th) @ vt)
     else (th#tt, vh#vt))"
| "eat_word gr t v = (t, v)"

text_raw {*
\end{block}
\lyxframeend{}

\lyxframe{Norm definition pt. 2}

\begin{block}{Terminal words of variable words}
*}

definition word_in_variables where
  "word_in_variables gr w v \<equiv> eat_word gr w v = ([], [])"

definition words_of_variables where
  "words_of_variables gr v \<equiv>
     {w | w. word_in_variables gr w v}"

text_raw {*
\end{block}

\begin{block}{Normedness of a grammar}
*}

definition gram_normed_def where
  "gram_normed_def gr \<equiv> \<forall>v. set v \<subseteq> keys gr \<longrightarrow>
     (\<exists>w. word_in_variables gr w v)"

definition gram_nsd_def where
  "gram_nsd_def gr \<equiv> gram_sd gr \<and> gram_normed_def gr"

text_raw {*
\end{block}
\lyxframeend{}

\lyxframe{Norm definition pt. 3}

\begin{block}{Norm}
*}

definition norm_def where
  "norm_def gr v \<equiv>
     LEAST l. l \<in> length ` (words_of_variables gr v)"

text_raw {*
\end{block}

\lyxframeend{}
*}

end
