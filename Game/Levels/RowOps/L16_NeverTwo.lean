import Game.Levels.RowOps.L15_SheetTwoQ5

World "RowOps"
Level 16
Title "Never exactly two"

Introduction "
**Boss.** A linear system has no solution, exactly one, or infinitely many — never exactly
two. The key: if $\\vec v$ and $\\vec w$ are solutions of $A\\vec x = \\vec b$ then so is
$2\\vec v - \\vec w$ (the line through them goes on forever).

Useful: `mulVec_sub`, `mulVec_smul` (pull $A$ through $-$ and scalars).
"

namespace LinearAlgebraGame

open Matrix in
/-- No linear system $A\vec x = \vec b$ has exactly two solutions. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    ¬ ∃ v w, v ≠ w ∧ ∀ u, A *ᵥ u = b ↔ (u = v ∨ u = w) := by
  intro h
  obtain ⟨v, w, hne, h⟩ := h
  Hint "First note that $\\vec v$ and $\\vec w$ themselves are solutions."
  Hint (hidden := true) "`have hv : A *ᵥ v = b := (h v).mpr (Or.inl rfl)`"
  have hv : A *ᵥ v = b := (h v).mpr (Or.inl rfl)
  have hw : A *ᵥ w = b := (h w).mpr (Or.inr rfl)
  Hint (strict := true) "Now show $2\\vec v - \\vec w$ is a solution too."
  Hint (strict := true) (hidden := true) "`have hu : A *ᵥ ((2 : ℝ) • v - w) = b := by`
  `rw [mulVec_sub, mulVec_smul, hv, hw]`, then `ext i`, `norm_num`, `linear_combination`."
  have hu : A *ᵥ ((2 : ℝ) • v - w) = b := by
    rw [mulVec_sub, mulVec_smul, hv, hw]
    ext i
    norm_num
    linear_combination
  Hint "So $2\\vec v - \\vec w$ is $\\vec v$ or $\\vec w$. Either way $\\vec v = \\vec w$."
  rcases (h _).mp hu with h3 | h3
  · have hvw : v = w := by
      ext i
      have hi := congrFun h3 i
      norm_num at hi
      linear_combination hi
    exact hne hvw
  · have hvw : v = w := by
      ext i
      have hi := congrFun h3 i
      norm_num at hi
      linear_combination hi / 2
    exact hne hvw

end LinearAlgebraGame

Conclusion "
Two solutions give a whole line of them — so the number of solutions is $0$, $1$ or $\\infty$.
"

DisabledTactic linarith nlinarith
NewTheorem Matrix.mulVec_sub Matrix.mulVec_smul
