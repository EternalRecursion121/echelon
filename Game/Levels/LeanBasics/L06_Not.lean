import Game.Levels.LeanBasics.L05_Exists

World "LeanBasics"
Level 6
Title "Not"

Introduction "
`¬ P` means \"P leads to a contradiction\". To prove it, `intro hp` assumes `P`; your goal
becomes `False`. A hypothesis like `1 = 2` gives you `False` via `norm_num at h`.
"

/-- If $x = 1$ then $x \neq 2$. -/
Statement (x : ℝ) (h : x = 1) : x ≠ 2 := by
  Hint "`≠` is `¬ (… = …)`. Start with `intro h2`."
  intro h2
  Hint "Substitute what you know about `x` into `{h2}`: `rw [{h}] at {h2}`."
  rw [h] at h2
  Hint (hidden := true) "`{h2}` now claims `1 = 2`. `norm_num at {h2}` sees that it is false."
  norm_num at h2

/-- `intro h` moves an assumption into the context: for goals `P → Q`, `¬ P` and `∀ x, …`. -/
TacticDoc intro
NewTactic intro
