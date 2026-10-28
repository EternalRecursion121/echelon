import Game.Levels.LeanBasics.L04_And

World "LeanBasics"
Level 5
Title "There exists"

Introduction "
\"Solve this equation\" is often the goal `∃ x, …`. Prove it by naming a solution:
`use 3` puts `3` in place of `x`, and you then check that it works.
"

/-- There is a real number $x$ with $2x = 6$. -/
Statement : ∃ x : ℝ, 2 * x = 6 := by
  Hint "Which number works? `use` it."
  use 3
  norm_num

Conclusion "Many \"find the solution\" questions on the sheets look like this: you supply
the witness, Lean checks it."

NewTactic use
