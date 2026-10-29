import Game.Levels.LeanBasics.L07_Implies

World "LeanBasics"
Level 8
Title "Not"

Introduction "
`¬ P` means `P → False`: \"P leads to a contradiction\". So prove it like an
\"if … then\": `intro hp` assumes `P`, and your goal becomes `False`. A hypothesis that is
plainly false, like `h : 1 = 2`, finishes the job: `norm_num at h` sees that it is false.

**Typing:** `¬` is `\\not`, `≠` is `\\ne`.
"

/-- If $x = 1$ then $x \neq 2$. -/
Statement (x : ℝ) (h : x = 1) : x ≠ 2 := by
  Hint "`x ≠ 2` means `¬ (x = 2)`. Assume `x = 2` and give the assumption a *new* name
  (not `{h}`, which is taken), for example `intro h2`."
  intro h2
  Hint "Substitute what you know about `x` into `{h2}` (as in the last level)."
  Hint (hidden := true) "`rw [{h}] at {h2}`"
  rw [h] at h2
  Hint (hidden := true) "`{h2}` now claims `1 = 2`. `norm_num at {h2}` sees that it is false."
  norm_num at h2

