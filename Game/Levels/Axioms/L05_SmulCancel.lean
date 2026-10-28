import Game.Levels.Axioms.L04_SmulEqZero

World "Axioms"
Level 5
Title "Cancelling a nonzero vector"

-- @sheet 3 Q3b
/-! @answer
($\Leftarrow$) is immediate. ($\Rightarrow$) If $r_1\cdot\vec v = r_2\cdot\vec v$ then
$(r_1 - r_2)\cdot\vec v = r_1\cdot\vec v - r_2\cdot\vec v = \vec 0$, so by part (a)
(using $\vec v \neq \vec 0$) $r_1 - r_2 = 0$, i.e. $r_1 = r_2$.
-/
Introduction "
**Problem Sheet 3, Question 3(b).** (Still assuming $\\vec v \\neq \\vec 0$.) Prove that
$r_1 \\cdot \\vec v = r_2 \\cdot \\vec v$ if and only if $r_1 = r_2$.

Part (a) is in your inventory as `smul_eq_zero_iff_of_ne`.
"

namespace LinearAlgebraGame

/-- If $\vec v \neq \vec 0$ then $r_1\cdot\vec v = r_2\cdot\vec v$ if and only if $r_1 = r_2$. -/
Statement smul_cancel_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V)
    (hv : v ≠ 0) (r₁ r₂ : ℝ) : r₁ • v = r₂ • v ↔ r₁ = r₂ := by
  Hint "Move everything to one side: $(r_1 - r_2)\\cdot\\vec v = \\vec 0$, then use part (a)."
  constructor
  · intro h
    Hint (hidden := true) "`have h2 : (r₁ - r₂) • {v} = 0 := by rw [sub_smul, {h}, sub_self]`"
    have h2 : (r₁ - r₂) • v = 0 := by rw [sub_smul, h, sub_self]
    Hint (hidden := true) "`rw [smul_eq_zero_iff_of_ne {v} {hv}] at {h2}`, then `linarith`."
    rw [smul_eq_zero_iff_of_ne v hv] at h2
    linarith
  · intro h
    rw [h]

end LinearAlgebraGame

Conclusion "
So the map $r \\mapsto r\\cdot\\vec v$ is one-to-one whenever $\\vec v \\neq \\vec 0$ —
that is the whole of part (c).
"

DisabledTheorem smul_eq_zero smul_eq_zero_iff_left smul_eq_zero_iff_right smul_ne_zero_iff smul_left_injective smul_right_injective smul_left_inj smul_right_inj
DisabledTactic norm_num simp
TheoremTab "Vector spaces"
NewTheorem LinearAlgebraGame.smul_eq_zero_iff_of_ne sub_self sub_smul
