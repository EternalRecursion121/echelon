import Game.Levels.RowOps.L11_SheetTwoQ1d

World "RowOps"
Level 12
Title "How many solutions? (f), (g)"

-- @sheet 2 Q1f-g
/-! @answer
(f) $2x + 2y = 4,\ y = 1,\ 0 = 4$: the last row is false — **no solution**.
(g) $x + y - 3z = -1,\ y - z = 2,\ z = 0,\ 0 = 0$: back-substitution gives $z = 0$, $y = 2$,
$x = -3$ — **a unique solution** $(-3, 2, 0)$.
-/
Introduction "
**Problem Sheet 2, Question 1(f), (g).** Unique solution, no solution, or infinitely many?

(f) $2x + 2y = 4,\\ y = 1,\\ 0 = 4$ (g) $x + y - 3z = -1,\\ y - z = 2,\\ z = 0,\\ 0 = 0$
"

namespace LinearAlgebraGame

/-- Classify systems (f) and (g) of Sheet 2 Q1. -/
Statement :
    Classify (fun v : Fin 2 → ℝ => 2 * v 0 + 2 * v 1 = 4 ∧ v 1 = 1 ∧ (0 : ℝ) = 4) ∧
    Classify (fun v : Fin 3 → ℝ =>
      v 0 + v 1 - 3 * v 2 = -1 ∧ v 1 - v 2 = 2 ∧ v 2 = 0 ∧ (0 : ℝ) = 0) := by
  constructor
  · Hint "(f): look at the last row."
    left
    intro h
    obtain ⟨v, h1, h2, h3⟩ := h
    norm_num at h3
  · Hint "(g): back-substitute from the bottom."
    right
    left
    Hint (hidden := true) "`rw [uniqueSolution_iff]`, then `use ![-3, 2, 0]`."
    rw [uniqueSolution_iff]
    use ![-3, 2, 0]
    constructor
    · norm_num
    · intro v h
      obtain ⟨h1, h2, h3, h4⟩ := h
      rowop h2 : v 1 = 2 := h2 + h3
      rowop h1 : v 0 = -3 := h1 - h2 + 3 * h3
      entrywise
      · norm_num
        exact h1
      · norm_num
        exact h2
      · norm_num
        exact h3

end LinearAlgebraGame

Conclusion "**Answers:** (f) none, (g) unique, $(-3, 2, 0)$."

DisabledTactic linarith nlinarith
