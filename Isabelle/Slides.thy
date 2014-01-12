(*<*)theory Slides imports
  Norm_defs
  Norm_proofs
  Tests
  "~~/src/HOL/Library/LaTeXsugar"
begin(*>*)

text {*
\lyxframe{Norm definition}

\begin{block}{Simple deterministic grammars}
@{thm gram_sd_def}
\end{block}

\begin{block}{Acceptance of a terminal word}
@{thm eat_word.simps}
\end{block}

\lyxframeend{}


\lyxframe{Norm definition}

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


\lyxframe{PI}

\begin{block}{Definition}
@{thm [display] partition_iterate.simps}
\end{block}

\begin{block}{Custom induction principle}
@{thm pi_induct}
\end{block}

\lyxframeend{}



\lyxframe{Central theorem}
@{thm[mode=Rule] nf_calcs_nd}
\lyxframeend{}


\lyxframe{Demo}
@{thm [display] test_gr4_def}
@{lemma "norms_of_grammar test_gr4 =
   [(1, 1, 0, []), (2, 2, 0, [1]), (4, 4, 0, [1, 1, 1]), (3, 3, 0, [2]), (5, 4, 23, [3])]" by eval}
\lyxframeend{}


*}

(*<*)end(*>*)
