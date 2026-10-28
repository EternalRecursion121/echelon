import Game.Levels.Axioms.L05_SmulCancel

World "Axioms"
Level 6
Title "Nontrivial spaces are big"

-- @sheet 3 Q3c
/-! @answer
Let $V$ be nontrivial, so it contains some $\vec v \neq \vec 0$. By part (b) the map
$\mathbb{R} \to V$, $r \mapsto r\cdot\vec v$, is one-to-one: distinct reals give distinct
vectors. Since $\mathbb{R}$ is infinite, so is $V$.
-/
Introduction "
**Problem Sheet 3, Question 3(c).** Prove that any nontrivial vector space is infinite.

\"Nontrivial\" means: $V$ contains some $\\vec v \\neq \\vec 0$. In Lean, `Infinite V` says
the type $V$ is infinite.
"

namespace LinearAlgebraGame

/-- A vector space containing a nonzero vector is infinite. -/
Statement infinite_of_ne_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V)
    (hv : v ≠ 0) : Infinite V := by
  Hint "There are infinitely many reals $r$, and different $r$ give different $r\\cdot\\vec v$."
  Hint (hidden := true) "`apply Infinite.of_injective (fun r : ℝ => r • {v})` leaves you to
  show this map is one-to-one."
  apply Infinite.of_injective (fun r : ℝ => r • v)
  Hint (hidden := true) "Injective means: `intro r₁ r₂ h` gives `h : r₁ • {v} = r₂ • {v}` and
  asks for `r₁ = r₂`. Part (b) is `smul_cancel_iff`."
  intro r₁ r₂ h
  exact (smul_cancel_iff v hv r₁ r₂).mp h

end LinearAlgebraGame

Conclusion "
A vector space has either one element (just $\\vec 0$) or infinitely many. Part (d) applies
this to solution sets.
"

NewTheorem Infinite.of_injective LinearAlgebraGame.smul_cancel_iff
DisabledTheorem smul_left_injective smul_right_injective smul_left_inj smul_right_inj
DisabledTactic norm_num simp
TheoremTab "Vector spaces"
