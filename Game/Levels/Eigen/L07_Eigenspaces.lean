import Game.Levels.Eigen.L06_CharEq

World "Eigen"
Level 7
Title "The eigenspaces"

-- @sheet 9 Q7b
/-! @answer
For $\lambda = 1$: $(T - I)\vec v = 0$ means $2v_1 + 2v_2 = 0$, $-v_1 - v_2 = 0$, so
$V_1 = \{t(1,-1)\} = [\{(1,-1)\}]$. For $\lambda = 2$: $(T-2I)\vec v = 0$ means
$v_1 + 2v_2 = 0$, so $V_2 = [\{(2,-1)\}]$.
-/
Introduction "
**Problem Sheet 9, Question 7** (part 2 of 3). Find the eigenspaces of
$T = \\begin{pmatrix} 3 & 2 \\\\ -1 & 0\\end{pmatrix}$.

The eigenspace $V_\\lambda = \\{\\vec v : T\\vec v = \\lambda \\vec v\\}$ (Def 3.12) is Mathlib's
`Module.End.eigenspace (Matrix.toLin' T) λ`. Useful: `Module.End.mem_eigenspace_iff`,
`Matrix.toLin'_apply`, `Submodule.mem_span_singleton : x ∈ span {y} ↔ ∃ a, a • y = x`.

**Prove:** $V_1 = [\\{(1,-1)\\}]$ and $V_2 = [\\{(2,-1)\\}]$.
"

namespace LinearAlgebraGame

/-- The eigenspaces of $T$ are $V_1 = [\{(1,-1)\}]$ and $V_2 = [\{(2,-1)\}]$. -/
Statement sheet9_q7b :
    Module.End.eigenspace (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 1
      = Submodule.span ℝ {![1, -1]} ∧
    Module.End.eigenspace (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 2
      = Submodule.span ℝ {![2, -1]} := by
  Hint "For each part, compare membership: $T\\vec v = \\lambda\\vec v$ is two linear
  equations in $v_0, v_1$."
  constructor
  · Hint (hidden := true) "`ext v`, then
    `rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Submodule.mem_span_singleton]`."
    ext v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Submodule.mem_span_singleton]
    constructor
    · intro h
      Hint (hidden := true) "`use v 0`. Get the two coordinate equations with
      `have h0 := congrFun h 0` and `have h1 := congrFun h 1`, then
      `simp [Matrix.mulVec, dotProduct] at h0 h1`."
      use v 0
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.mulVec, dotProduct] at h0 h1
      entrywise <;> simp <;> linarith
    · intro h
      obtain ⟨t, ht⟩ := h
      rw [← ht]
      entrywise <;> simp [Matrix.mulVec, dotProduct] <;> ring
  · ext v
    rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply, Submodule.mem_span_singleton]
    constructor
    · intro h
      Hint (hidden := true) "This time `use -v 1`."
      use -v 1
      have h0 := congrFun h 0
      have h1 := congrFun h 1
      simp [Matrix.mulVec, dotProduct] at h0 h1
      entrywise <;> simp <;> linarith
    · intro h
      obtain ⟨t, ht⟩ := h
      rw [← ht]
      entrywise <;> simp [Matrix.mulVec, dotProduct] <;> ring

end LinearAlgebraGame

Conclusion "$V_1 = [\\{(1,-1)\\}]$, $V_2 = [\\{(2,-1)\\}]$: each is a line through the origin."

NewTheorem Module.End.mem_eigenspace_iff Matrix.toLin'_apply
NewDefinition Module.End.eigenspace
TheoremTab "Eigen"
