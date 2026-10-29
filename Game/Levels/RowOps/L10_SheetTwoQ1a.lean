import Game.Levels.RowOps.L09_Classify

World "RowOps"
Level 10
Title "How many solutions? (a)–(c)"

-- @sheet 2 Q1a-c
/-! @answer
(a) $-3x + 2y = 0,\ -2y = 0$: back-substitution gives $y = 0$, $x = 0$ — **a unique solution**.
(b) $x + y = 4,\ y - z = 0$: $z$ is free ($y = z$, $x = 4 - z$) — **infinitely many**.
(c) $x + y = 4,\ 0 = 4$: the second row is false — **no solution**.
-/
Introduction "
**Problem Sheet 2, Question 1(a)–(c).** Each system is in echelon form. Say whether it has
a unique solution, no solution, or infinitely many solutions.

(a) $-3x + 2y = 0,\\ -2y = 0$ (b) $x + y = 4,\\ y - z = 0$ (c) $x + y = 4,\\ 0 = 4$

As in the last level: `left` (none), `right` then `left` (unique), or `right` twice
(infinitely many). Tools (Theorems tab, **Systems**):
- none: `NoSolution S` is `¬ ∃ v, S v` — assume a solution and derive something false.
- unique: **new** `rw [uniqueSolution_iff]` turns the goal into \"some `p` solves it, and every
  solution equals `p`\"; then `use` your solution.
- infinitely many: `apply infinitelyMany_of_line p d i`, as in the last level.
"

namespace LinearAlgebraGame

/-- Classify systems (a)–(c) of Sheet 2 Q1. -/
Statement :
    Classify (fun v : Fin 2 → ℝ => -3 * v 0 + 2 * v 1 = 0 ∧ -2 * v 1 = 0) ∧
    Classify (fun v : Fin 3 → ℝ => v 0 + v 1 = 4 ∧ v 1 - v 2 = 0) ∧
    Classify (fun v : Fin 2 → ℝ => v 0 + v 1 = 4 ∧ (0 : ℝ) = 4) := by
  Hint "Take the systems one at a time: `constructor`."
  constructor
  · Hint "(a): back-substitute. How many choices do you get?"
    right
    left
    Hint (hidden := true) "`rw [uniqueSolution_iff]`, then `use ![0, 0]`."
    rw [uniqueSolution_iff]
    use ![0, 0]
    constructor
    · norm_num
    · Hint "Every solution `v` must equal your vector: name the rows and run Gauss's method."
      intro v h
      obtain ⟨h1, h2⟩ := h
      rowop h2 : v 1 = 0 := h2 / (-2)
      rowop h1 : v 0 = 0 := (h1 - 2 * h2) / (-3)
      entrywise
      · norm_num
        exact h1
      · norm_num
        exact h2
  constructor
  · Hint "(b): is there a free variable?"
    right
    right
    Hint (hidden := true) "$z$ is free: the line $(4,0,0) + t(-1,1,1)$, whose direction is
    nonzero in position 1. `apply infinitelyMany_of_line ![4, 0, 0] ![-1, 1, 1] 1`"
    apply infinitelyMany_of_line ![4, 0, 0] ![-1, 1, 1] 1
    · norm_num
    · intro t
      constructor
      · norm_num
      · norm_num
  · Hint "(c): look at the second row."
    left
    Hint (hidden := true) "`intro h`, `obtain ⟨v, h1, h2⟩ := h`, then `norm_num at h2`."
    intro h
    obtain ⟨v, h1, h2⟩ := h
    norm_num at h2

end LinearAlgebraGame

Conclusion "**Answers:** (a) unique, (b) infinitely many, (c) none."

NewTheorem LinearAlgebraGame.uniqueSolution_iff
TheoremTab "Systems"

DisabledTactic linarith nlinarith
