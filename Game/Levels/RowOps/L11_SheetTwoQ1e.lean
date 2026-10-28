import Game.Levels.RowOps.L10_SheetTwoQ1a

World "RowOps"
Level 11
Title "How many solutions? (II)"

-- @sheet 2 Q1e-g
/-! @answer
(e) $x - 3y = 2,\ 0 = 0$: $y$ is free ($x = 2 + 3y$) — **infinitely many**.
(f) $2x + 2y = 4,\ y = 1,\ 0 = 4$: the last row is false — **no solution**.
(g) $x + y - 3z = -1,\ y - z = 2,\ z = 0,\ 0 = 0$: back-substitution gives $z = 0$, $y = 2$,
$x = -3$ — **a unique solution** $(-3, 2, 0)$.
-/
Introduction "
**Problem Sheet 2, Question 1(e)–(g).** Unique solution, no solution, or infinitely many?

(e) $x - 3y = 2,\\ 0 = 0$ (f) $2x + 2y = 4,\\ y = 1,\\ 0 = 4$
(g) $x + y - 3z = -1,\\ y - z = 2,\\ z = 0,\\ 0 = 0$
"

namespace LinearAlgebraGame

/-- Classify systems (e)–(g) of Sheet 2 Q1. -/
Statement :
    Classify (fun v : Fin 2 → ℝ => v 0 - 3 * v 1 = 2 ∧ (0 : ℝ) = 0) ∧
    Classify (fun v : Fin 2 → ℝ => 2 * v 0 + 2 * v 1 = 4 ∧ v 1 = 1 ∧ (0 : ℝ) = 4) ∧
    Classify (fun v : Fin 3 → ℝ =>
      v 0 + v 1 - 3 * v 2 = -1 ∧ v 1 - v 2 = 2 ∧ v 2 = 0 ∧ (0 : ℝ) = 0) := by
  constructor
  · Hint "(e): a row $0 = 0$ says nothing. What is left?"
    right
    right
    apply infinitelyMany_of_line _ ![2, 0] ![3, 1]
    · intro h
      have h₁ := congrFun h 1
      norm_num at h₁
    · intro t
      constructor
      · norm_num
        linear_combination
      · norm_num
  constructor
  · Hint "(f): look at the last row."
    left
    intro h
    obtain ⟨v, h₁, h₂, h₃⟩ := h
    norm_num at h₃
  · Hint "(g): back-substitute from the bottom."
    right
    left
    use ![-3, 2, 0]
    constructor
    · norm_num
    · intro v h
      obtain ⟨h₁, h₂, h₃, h₄⟩ := h
      rowop h₂ : v 1 = 2 := h₂ + h₃
      rowop h₁ : v 0 = -3 := h₁ - h₂ + 3 * h₃
      ext i
      fin_cases i
      · norm_num
        exact h₁
      · norm_num
        exact h₂
      · norm_num
        exact h₃

end LinearAlgebraGame

Conclusion "**Answers:** (e) infinitely many, (f) none, (g) unique, $(-3, 2, 0)$."

DisabledTactic linarith nlinarith
