import Game.Levels.RowOps.L05_SheetOneQ3c

World "RowOps"
Level 6
Title "More unknowns than equations"

-- @sheet 1 Q2
/-! @answer
**False.** The system $x + y + z = 0,\ x + y + z = 1$ has three unknowns and only two
equations, but subtracting the first equation from the second gives $0 = 1$, so it has no
solution.
-/
Introduction "
**Problem Sheet 1, Question 2.** True or false: a system with more unknowns than equations
has at least one solution.

A general system of $m$ equations in $n$ unknowns is `A *ᵥ x = b` with
`A : Matrix (Fin m) (Fin n) ℝ`. The goal is `¬ P ∨ P`: commit with `left` (false) or
`right` (true), then prove your choice. After `right` you prove the claim for every system
(`intro m n A b hmn`). After `left` you assume the claim as `h` and refute it: `h` is a big
\"for all\", which you can apply to a system of your choice, as in Lean Basics level 12 —
e.g. `h m n A b (by norm_num)` with concrete numbers and matrices (the `(by norm_num)` proves
$m < n$).

Tips: `congrFun hx 0` turns an equation of vectors `hx : u = v` into its entry 0,
`u 0 = v 0`; then `norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0` writes that row out
as an equation (the recipe from Lean Basics, with three unknowns).
"

namespace LinearAlgebraGame

open Matrix in
/-- True or false: every system with more unknowns than equations has a solution. -/
Statement : (¬ ∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) ∨
    (∀ (m n : ℕ) (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ), m < n → ∃ x, A *ᵥ x = b) := by
  Hint "Decide first: experiment with small systems, e.g. two equations in three unknowns."
  left
  intro h
  Hint "Pick two equations in three unknowns that contradict each other, and feed them to `{h}`."
  Hint (hidden := true) "Try $x + y + z = 0,\\ x + y + z = 1$:
  `obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)`."
  obtain ⟨x, hx⟩ := h 2 3 !![1, 1, 1; 1, 1, 1] ![0, 1] (by norm_num)
  have h0 := congrFun hx 0
  have h1 := congrFun hx 1
  Hint (hidden := true) "`norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1`"
  norm_num [mulVec, dotProduct, Fin.sum_univ_three] at h0 h1
  Hint (hidden := true) "`rowop h1 : 0 = 1 := h1 - h0`, then `norm_num at h1`."
  rowop h1 : 0 = 1 := h1 - h0
  norm_num at h1

end LinearAlgebraGame

Conclusion "**Answer: false.** $x+y+z = 0,\\ x+y+z = 1$ is a counterexample."

DisabledTactic linarith nlinarith
NewTheorem Fin.sum_univ_three
