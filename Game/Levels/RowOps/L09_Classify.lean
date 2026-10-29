import Game.Levels.RowOps.L08_SheetOneQ9b

World "RowOps"
Level 9
Title "How many solutions?"

Introduction "
Sheet 2 asks you to *classify* systems: no solution, exactly one, or infinitely many. In this
game a system is a condition on a vector `v`, written `fun v : Fin 2 → ℝ => …` (read: \"the
condition, as a function of `v`\"); `v 0, v 1, v 2` play the roles of $x, y, z$.

`Classify S` means `NoSolution S ∨ UniqueSolution S ∨ InfinitelyMany S` (Definitions tab). You
choose with `left` (none), `right` then `left` (unique), or `right` twice (infinitely many).

This level: the single equation $x + y = 2$. For **infinitely many**, give a whole line of
solutions: `apply infinitelyMany_of_line p d i` with a point `p`, a direction `d` and a
position `i` where `d` is nonzero (Theorems tab, **Systems**).

**New: `apply`.** `apply f` uses a theorem `f` whose conclusion matches the goal, and leaves
you to prove what `f` still needs — here two goals: `d i ≠ 0`, and \"every point
`p + t • d` of the line is a solution\".
"

namespace LinearAlgebraGame

/-- Classify the system $x + y = 2$. -/
Statement : Classify (fun v : Fin 2 → ℝ => v 0 + v 1 = 2) := by
  Hint "One equation, two unknowns: is there a free variable?"
  Hint (hidden := true) "Infinitely many: `right`, then `right` again."
  right
  right
  Hint "Which variable is free? Write the solutions as a point plus all multiples of a
  direction, and pick a position where the direction is nonzero."
  Hint (hidden := true) "With $y$ free: the line $(2, 0) + t(-1, 1)$, nonzero in position 1.
  `apply infinitelyMany_of_line ![2, 0] ![-1, 1] 1`"
  apply infinitelyMany_of_line ![2, 0] ![-1, 1] 1
  · Hint (hidden := true) "`norm_num`"
    norm_num
  · Hint "Every point of the line: `intro t`, then check the equation."
    intro t
    Hint (hidden := true) "`norm_num` evaluates the entries and the sum."
    norm_num

end LinearAlgebraGame

Conclusion "A free variable gives a line of solutions, so infinitely many."

NewDefinition LinearAlgebraGame.Classify LinearAlgebraGame.NoSolution LinearAlgebraGame.UniqueSolution LinearAlgebraGame.InfinitelyMany
NewTheorem LinearAlgebraGame.infinitelyMany_of_line
TheoremTab "Systems"
DisabledTactic linarith nlinarith
NewTactic apply
