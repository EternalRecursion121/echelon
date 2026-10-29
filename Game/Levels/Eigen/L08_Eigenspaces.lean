import Game.Levels.Eigen.L07_CharEq

World "Eigen"
Level 8
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
`Module.End.eigenspace (Matrix.toLin' T) λ`; `mem_eigenspace_toLin'` says
$\\vec v \\in V_\\lambda \\iff T\\vec v = \\lambda\\vec v$. The span of one vector is
`Submodule.span ℝ {v}`, and `Submodule.mem_span_singleton : x ∈ span {y} ↔ ∃ a, a • y = x`.

**Find** nonzero vectors $\\vec v, \\vec w$ with $V_1 = [\\{\\vec v\\}]$ and $V_2 = [\\{\\vec w\\}]$.
"

namespace LinearAlgebraGame

/-- Each eigenspace of $T$ is a line: $V_1 = [\{\vec v\}]$ and $V_2 = [\{\vec w\}]$ for some nonzero $\vec v, \vec w$. -/
Statement sheet9_q7b :
    ∃ v w : Fin 2 → ℝ, v ≠ 0 ∧ w ≠ 0 ∧
      Module.End.eigenspace (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 1
        = Submodule.span ℝ {v} ∧
      Module.End.eigenspace (Matrix.toLin' (!![3, 2; -1, 0] : Matrix (Fin 2) (Fin 2) ℝ)) 2
        = Submodule.span ℝ {w} := by
  Hint "Solve $(T - \\lambda I)\\vec v = \\vec 0$ for each $\\lambda$ to find $\\vec v$ and $\\vec w$.
  Then compare membership: $T\\vec v = \\lambda\\vec v$ is two linear equations in $v_0, v_1$."
  Hint (hidden := true) "$V_1$: $2v_0 + 2v_1 = 0$; $V_2$: $v_0 + 2v_1 = 0$.
  `use ![1, -1], ![2, -1]`."
  use ![1, -1], ![2, -1]
  Hint (hidden := true) "The two vectors are visibly nonzero (`simp` checks it):
  `refine ⟨by simp, by simp, ?_, ?_⟩`."
  refine ⟨by simp, by simp, ?_, ?_⟩
  · Hint (hidden := true) "`ext v`, then `rw [mem_eigenspace_toLin', Submodule.mem_span_singleton]`."
    ext v
    rw [mem_eigenspace_toLin', Submodule.mem_span_singleton]
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
    rw [mem_eigenspace_toLin', Submodule.mem_span_singleton]
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

NewTheorem LinearAlgebraGame.mem_eigenspace_toLin'
NewDefinition Module.End.eigenspace
TheoremTab "Eigen"
