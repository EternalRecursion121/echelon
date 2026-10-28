import Game.Levels.Axioms.L02_NegUnique

World "Axioms"
Level 3
Title "Minus one times a vector"

Introduction "
Lemma Two.I.1.16 (2): $(-1)\\cdot\\vec v + \\vec v = \\vec 0$, i.e. $(-1)\\cdot\\vec v$ *is* the
additive inverse of $\\vec v$. Your two earlier theorems are now tools.
"

namespace LinearAlgebraGame

/-- $(-1)\cdot \vec v + \vec v = \vec 0$. -/
Statement neg_one_smul_add {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (-1 : ℝ) • v + v = 0 := by
  Hint (hidden := true) "Idea: write the second $v$ as $1 \\cdot v$, then combine the scalars."
  Hint (hidden := true) "`nth_rw 2 [← one_smul ℝ {v}]`, then `rw [← add_smul]`."
  nth_rw 2 [← one_smul ℝ v]
  rw [← add_smul]
  rw [neg_add_cancel]
  Hint (hidden := true) "`exact zero_smul_eq_zero {v}`"
  exact zero_smul_eq_zero v

end LinearAlgebraGame

Conclusion "Now `-v` and `(-1)•v` are interchangeable — the game will let `simp` do this from here on."

/-- $1 \cdot v = v$ — Hefferon's condition (10). -/
TheoremDoc one_smul as "one_smul" in "Axioms"
/-- `nth_rw n [h]` rewrites only the n-th occurrence. -/
TacticDoc nth_rw
/-- $-a + a = 0$ (in ℝ, or in any group). -/
TheoremDoc neg_add_cancel as "neg_add_cancel" in "Axioms"

NewTactic nth_rw
NewTheorem one_smul neg_add_cancel LinearAlgebraGame.zero_smul_eq_zero
/-- disabled -/
TheoremDoc neg_one_smul as "neg_one_smul" in "Axioms"
DisabledTheorem neg_one_smul
DisabledTactic norm_num
