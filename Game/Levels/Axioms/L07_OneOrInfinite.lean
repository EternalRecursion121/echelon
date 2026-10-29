import Game.Levels.Axioms.L06_Infinite

World "Axioms"
Level 7
Title "One or infinitely many"

-- @sheet 3 Q3d
/-! @answer
The solution set $S$ of a homogeneous system $A\vec x = \vec 0$ is nonempty (it contains
$\vec 0$) and is a vector space (it is closed under linear combinations, Sheet 2 Q4).
If $\vec 0$ is the only solution, $S$ has exactly one element. Otherwise $S$ contains some
$\vec x \neq \vec 0$, so $S$ is a nontrivial vector space and by part (c) it is infinite.
-/
Introduction "
**Problem Sheet 3, Question 3(d).** Use the fact that a nonempty solution set of a
homogeneous linear system is a vector space to draw the conclusion: the solution set has
either one element or infinitely many.

Here the system is $A\\vec x = \\vec 0$ for an $m\\times n$ matrix $A$. Since $\\vec 0$ is
always a solution, \"one element\" means the solution set is $\\{\\vec 0\\}$.

**The fact you may use.** The solution set, as a vector space, is
`LinearMap.ker A.mulVecLin` (the *null space* of $A$). Its elements are pairs
`⟨x, hx⟩` with `hx : A *ᵥ x = 0`, and Lean knows that
`Infinite (LinearMap.ker A.mulVecLin)` means the same as `Infinite` of the set below
(`Set.infinite_coe_iff`).

New: `by_cases h : P` splits the proof into two cases, one with `h : P` and one with `h : ¬P`.
"

namespace LinearAlgebraGame

open Matrix in
/-- The solution set of $A\vec x = \vec 0$ is $\{\vec 0\}$ or infinite. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    {x : Fin n → ℝ | A *ᵥ x = 0} = {0} ∨ Set.Infinite {x : Fin n → ℝ | A *ᵥ x = 0} := by
  Hint "Either there is a nonzero solution or there isn't. Split on that."
  Hint (hidden := true) "`by_cases h : ∃ x, A *ᵥ x = 0 ∧ x ≠ 0`"
  by_cases h : ∃ x, A *ᵥ x = 0 ∧ x ≠ 0
  · right
    obtain ⟨x, hx, hx0⟩ := h
    Hint "The null space contains the nonzero vector `⟨{x}, {hx}⟩`, so part (c) applies to it."
    Hint (hidden := true) "First show that pair is not zero:
    `have hne : (⟨{x}, {hx}⟩ : LinearMap.ker A.mulVecLin) ≠ 0`."
    have hne : (⟨x, hx⟩ : LinearMap.ker A.mulVecLin) ≠ 0 := by
      Hint (hidden := true) "`intro h0` then `apply {hx0}`: the pair is zero exactly when its
      first component is, `exact congrArg Subtype.val h0`."
      intro h0
      apply hx0
      exact congrArg Subtype.val h0
    Hint (hidden := true) "`have hinf := infinite_of_ne_zero _ {hne}`"
    have hinf := infinite_of_ne_zero _ hne
    Hint (hidden := true) "`exact Set.infinite_coe_iff.mp {hinf}`"
    exact Set.infinite_coe_iff.mp hinf
  · left
    Hint "Two sets are equal when they have the same elements: `ext x`."
    ext x
    constructor
    · intro hx
      Hint (hidden := true) "If `{x} ≠ 0` it would be a nonzero solution, contradicting `{h}`.
      `by_contra hne` then `exact {h} ⟨{x}, {hx}, hne⟩`."
      by_contra hne
      exact h ⟨x, hx, hne⟩
    · intro hx
      Hint (hidden := true) "`rw [{hx}]` then `exact mulVec_zero A`."
      rw [hx]
      exact mulVec_zero A

end LinearAlgebraGame

Conclusion "
This is Hefferon's second proof of the \"one or infinitely many\" theorem — now with no
row reduction at all, only the vector space axioms.
"

NewTheorem LinearAlgebraGame.infinite_of_ne_zero Set.infinite_coe_iff
DisabledTactic norm_num simp
TheoremTab "Vector spaces"
NewDefinition LinearMap.ker
NewTactic by_cases
