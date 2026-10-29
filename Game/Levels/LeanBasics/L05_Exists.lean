import Game.Levels.LeanBasics.L04_And

World "LeanBasics"
Level 5
Title "There exists"

Introduction "
\"Solve this equation\" is often the goal `∃ x, …`. Prove it by naming a solution.
For example, for `∃ x : ℝ, x + 1 = 5` you would write `use 4`: Lean puts `4` in place of
`x` and leaves you to check `4 + 1 = 5` (which `norm_num` does).

**Typing:** `∃` is `\\ex`, `∀` is `\\all`.
"

/-- There is a real number $x$ with $2x = 6$. -/
Statement : ∃ x : ℝ, 2 * x = 6 := by
  Hint "Which number $x$ satisfies $2x = 6$? Then `use` it."
  use 3
  Hint "Now check the arithmetic."
  Hint (hidden := true) "`norm_num`"
  norm_num

Conclusion "Many \"find the solution\" questions on the sheets look like this: you supply
the witness, Lean checks it."

NewTactic use
