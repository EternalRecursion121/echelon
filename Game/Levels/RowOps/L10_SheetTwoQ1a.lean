import Game.Levels.RowOps.L09_SheetOneQ9b

World "RowOps"
Level 10
Title "How many solutions? (I)"

-- @sheet 2 Q1a-d
/-! @answer
(a) $-3x + 2y = 0,\ -2y = 0$: back-substitution gives $y = 0$, $x = 0$ — **a unique solution**.
(b) $x + y = 4,\ y - z = 0$: $z$ is free ($y = z$, $x = 4 - z$) — **infinitely many**.
(c) $x + y = 4,\ 0 = 4$: the second row is false — **no solution**.
(d) $3x + 6y + z = -0.5,\ -z = 2.5$: $z = -2.5$ and $y$ is free ($x = 2/3 - 2y$) —
**infinitely many**.
-/
Introduction "
**Problem Sheet 2, Question 1(a)–(d).** Each system is in echelon form. Say whether it has
a unique solution, no solution, or infinitely many solutions.

(a) $-3x + 2y = 0,\\ -2y = 0$ (b) $x + y = 4,\\ y - z = 0$ (c) $x + y = 4,\\ 0 = 4$
(d) $3x + 6y + z = -0.5,\\ -z = 2.5$

A system is a condition on a vector `v`; `v 0, v 1, v 2` play the roles of $x, y, z$.
`Classify S` means `NoSolution S ∨ UniqueSolution S ∨ InfinitelyMany S`: choose with
`left` (none), `right` then `left` (unique), or `right` twice (infinitely many). Use
`constructor` to take the four parts one at a time.

For infinitely many, exhibit a line of solutions with `infinitelyMany_of_line`.
New: `apply f` reduces the goal to the hypotheses of `f`.
"

namespace LinearAlgebraGame

/-- Classify systems (a)–(d) of Sheet 2 Q1. -/
Statement :
    Classify (fun v : Fin 2 → ℝ => -3 * v 0 + 2 * v 1 = 0 ∧ -2 * v 1 = 0) ∧
    Classify (fun v : Fin 3 → ℝ => v 0 + v 1 = 4 ∧ v 1 - v 2 = 0) ∧
    Classify (fun v : Fin 2 → ℝ => v 0 + v 1 = 4 ∧ (0 : ℝ) = 4) ∧
    Classify (fun v : Fin 3 → ℝ => 3 * v 0 + 6 * v 1 + v 2 = -0.5 ∧ -v 2 = 2.5) := by
  constructor
  · Hint "(a): back-substitute. How many choices do you get?"
    right
    left
    Hint (hidden := true) "`use ![0, 0]`, check it, then show every solution equals it."
    use ![0, 0]
    constructor
    · norm_num
    · intro v h
      obtain ⟨h1, h2⟩ := h
      rowop h2 : v 1 = 0 := h2 / (-2)
      rowop h1 : v 0 = 0 := (h1 - 2 * h2) / (-3)
      ext i
      fin_cases i
      · norm_num
        exact h1
      · norm_num
        exact h2
  constructor
  · Hint "(b): is there a free variable?"
    right
    right
    Hint (hidden := true) "$z$ is free: the line $(4,0,0) + t(-1,1,1)$.
    `apply infinitelyMany_of_line _ ![4, 0, 0] ![-1, 1, 1]`"
    apply infinitelyMany_of_line _ ![4, 0, 0] ![-1, 1, 1]
    · Hint (hidden := true) "A vector with a nonzero component is nonzero: `intro h`,
      `have h1 := congrFun h 1`, `norm_num at h1`."
      intro h
      have h1 := congrFun h 1
      norm_num at h1
    · intro t
      constructor
      · norm_num
      · norm_num
  constructor
  · Hint "(c): look at the second row."
    left
    intro h
    obtain ⟨v, h1, h2⟩ := h
    norm_num at h2
  · Hint "(d): $z$ is determined. Is $y$?"
    right
    right
    apply infinitelyMany_of_line _ ![2/3, 0, -5/2] ![-2, 1, 0]
    · intro h
      have h1 := congrFun h 1
      norm_num at h1
    · intro t
      constructor
      · norm_num
        linear_combination
      · norm_num

end LinearAlgebraGame

Conclusion "**Answers:** (a) unique, (b) infinitely many, (c) none, (d) infinitely many."

NewDefinition LinearAlgebraGame.Classify LinearAlgebraGame.NoSolution LinearAlgebraGame.UniqueSolution LinearAlgebraGame.InfinitelyMany

NewTheorem LinearAlgebraGame.infinitelyMany_of_line
TheoremTab "Systems"

DisabledTactic linarith nlinarith
NewTactic apply
