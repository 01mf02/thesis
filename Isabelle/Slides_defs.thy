(*<*)theory Slides_defs imports
  Norm_defs
  "~~/src/HOL/Library/LaTeXsugar"
begin(*>*)

text {*
\lyxframe{Norm definition pt. 1}

\begin{block}{Simple deterministic grammars}
@{thm gram_sd_def}
\end{block}

\begin{block}{Acceptance of a terminal word}
@{thm eat_word.simps}
\end{block}

\lyxframeend{}


\lyxframe{Norm definition pt. 2}

\begin{block}{Terminal words of variable words}
@{thm word_in_variables_def}\\
@{thm words_of_variables_def}
\end{block}

\begin{block}{Normed-ness of a grammar}
@{thm gram_normed_def_def}\\
@{thm gram_nsd_def_def}
\end{block}

\begin{block}{Norm}
@{thm norm_def_def}
\end{block}

\lyxframeend{}
*}

(*<*)end(*>*)
