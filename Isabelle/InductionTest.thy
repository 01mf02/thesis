theory InductionTest imports Main
begin

function recursor where "recursor t g x = (if t x then x else recursor t g (g x))"
by auto

find_theorems name: "recursor."

lemma recursor_invariant:
  assumes B: "P a"
      and C: "\<And>x. P x \<Longrightarrow> P (g x)"
      and D: "recursor_dom (t, g, a)"
    shows "P (recursor t g a)"
(* proof (cases "t a")
  case True then show ?thesis using B recursor.psimps[OF D] by auto
next
  case False show ?thesis *) using B D proof (induct rule: recursor.pinduct[OF D])
    case (1 t g x)
    then show ?case sorry
  qed
(* qed *)

end
