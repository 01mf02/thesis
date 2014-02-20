theory Report_proofs
imports
  "../Norm_proofs"
  "~~/src/HOL/Library/LaTeXsugar"
begin

text {*
To show correctness of the norm calculation algorithm, we proved the following theorem:

\begin{center}
@{thm [mode=Rule] nf_calcs_nd}
\end{center}

This expresses that whenever @{term gr} is a normed simple deterministic grammar and the variable word
@{term  v} consists only of variables in @{term gr}, then @{term norm_fun} coincides with @{term norm_def}.
To prove this, we observe that both @{term "norm_fun gr v"} and @{term "norm_def gr v"} are
equivalent to the length of the shortest terminal word producible by @{term v} in @{term gr}, i.e.
@{term "length (min_word_of_variables gr v)"}. We expressed this by two other central theorems:

\begin{center}
@{thm [mode=Rule] mwov_len_calcs_nf}
\end{center}

\begin{center}
@{thm [mode=Rule] mwov_len_calcs_nd}
\end{center}

To employ the theorems above to prove our central theorem, we showed the relation
between @{term gram_nsd_fun} and @{term gram_nsd_def}, i.e.

\begin{center}
@{thm [mode=Rule] gnsdf_calcs_gnsdd}
\end{center}
*}

end
