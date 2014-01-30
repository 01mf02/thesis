theory Report_proofs
imports
  "../Norm_proofs"
begin

text {*

We want to show the following theorem:
@{thm [mode=Rule] nf_calcs_nd}

This expresses that whenever gr is a normed simple deterministic grammar and the variable word v
consists only of variables in gr, then @{term norm_fun} coincides with @{term norm_def}.
To prove this, we observe that both @{term "norm_fun gr v"} and @{term "norm_def gr v"} will be
equivalent to the length of the shortest terminal word producible by @{term v} in @{term gr}, i.e.
@{term "length (min_word_of_variables gr v)"}. We express this by two other central theorems:

@{thm [mode=Rule] mwov_len_calcs_nf}
@{thm [mode=Rule] mwov_len_calcs_nd}

To employ the theorems above to prove our central theorem, we need to show the relation
between @{term gram_nsd_fun} and @{term gram_nsd_def}, i.e.

@{thm [mode=Rule] gnsdf_calcs_gnsdd}
*}

end
