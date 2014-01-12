(*<*)theory Slides_pi imports
  Partition_iterate
  "~~/src/HOL/Library/LaTeXsugar"
begin(*>*)

text {*
\lyxframe{@{text partition_iterate}}

\begin{block}{Definition}
@{thm [display] partition_iterate.simps}
\end{block}

\begin{block}{Custom induction principle}
@{thm pi_induct}
\end{block}

\lyxframeend{}
*}

(*<*)end(*>*)