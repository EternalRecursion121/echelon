import Game.Levels.LeanBasics.L05_Exists

World "LeanBasics"
Level 6
Title "Not"

Introduction "
`¬ P` means \"P leads to a contradiction\". To prove it, `intro hp` assumes `P`; your goal
becomes `False`. A hypothesis like `1 = 2` gives you `False` via `norm_num at h`.

**Names matter.** When you `intro` something, give it a *new* name. If you reuse a name
that is already taken (say `intro h` when there is already an `h`), the old `h` is hidden:
it is shown with a † and you can no longer refer to it. If that happens, press Retry and
pick a fresh name.

**Typing:** `¬` is `\\not`, `≠` is `\\ne`.
"

/-- If $x = 1$ then $x \neq 2$. -/
Statement (x : ℝ) (h : x = 1) : x ≠ 2 := by
  Hint "`x ≠ 2` means `¬ (x = 2)`. Assume `x = 2` and give the assumption a *new* name
  (not `{h}`, which is taken), for example `intro h2`."
  intro h2
  Hint "Substitute what you know about `x` into `{h2}`: `rw [{h}] at {h2}`."
  rw [h] at h2
  Hint (hidden := true) "`{h2}` now claims `1 = 2`. `norm_num at {h2}` sees that it is false."
  norm_num at h2

NewTactic intro
