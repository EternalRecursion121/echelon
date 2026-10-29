import Game.Levels.RowOps.L10_SheetTwoQ1a

World "RowOps"
Level 11
Title "How many solutions? (d), (e)"

-- @sheet 2 Q1d-e
/-! @answer
(d) $3x + 6y + z = -0.5,\ -z = 2.5$: $z = -2.5$ and $y$ is free ($x = 2/3 - 2y$) —
**infinitely many**.
(e) $x - 3y = 2,\ 0 = 0$: $y$ is free ($x = 2 + 3y$) — **infinitely many**.
-/
Introduction "
**Problem Sheet 2, Question 1(d), (e).** Unique solution, no solution, or infinitely many?

(d) $3x + 6y + z = -0.5,\\ -z = 2.5$ (e) $x - 3y = 2,\\ 0 = 0$
"

namespace LinearAlgebraGame

/-- Classify systems (d) and (e) of Sheet 2 Q1. -/
Statement :
    Classify (fun v : Fin 3 → ℝ => 3 * v 0 + 6 * v 1 + v 2 = -0.5 ∧ -v 2 = 2.5) ∧
    Classify (fun v : Fin 2 → ℝ => v 0 - 3 * v 1 = 2 ∧ (0 : ℝ) = 0) := by
  constructor
  · Hint "(d): $z$ is determined. Is $y$?"
    right
    right
    Hint (hidden := true) "$y$ is free: the line $(2/3, 0, -5/2) + t(-2, 1, 0)$.
    `apply infinitelyMany_of_line ![2/3, 0, -5/2] ![-2, 1, 0] 1`"
    apply infinitelyMany_of_line ![2/3, 0, -5/2] ![-2, 1, 0] 1
    · norm_num
    · intro t
      constructor
      · norm_num
        Hint (hidden := true) "What is left is pure algebra: `linear_combination`."
        linear_combination
      · norm_num
  · Hint "(e): a row $0 = 0$ says nothing. What is left?"
    right
    right
    Hint (hidden := true) "`apply infinitelyMany_of_line ![2, 0] ![3, 1] 1`"
    apply infinitelyMany_of_line ![2, 0] ![3, 1] 1
    · norm_num
    · intro t
      constructor
      · norm_num
        linear_combination
      · norm_num

end LinearAlgebraGame

Conclusion "**Answers:** (d) infinitely many, (e) infinitely many."

DisabledTactic linarith nlinarith
