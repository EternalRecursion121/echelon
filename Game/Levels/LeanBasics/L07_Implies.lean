import Game.Levels.LeanBasics.L06_Exists

World "LeanBasics"
Level 7
Title "If … then"

Introduction "
To prove `P → Q` (\"if $P$ then $Q$\"), assume `P` and prove `Q`: `intro hp` adds the
assumption `hp : P` (you choose the name) and leaves the goal `Q`.

Many tactics also work on a hypothesis instead of the goal: add `at h`.
`rw [hp] at h` rewrites inside `h`, and `norm_num at h` simplifies the arithmetic in `h`.

**Names matter.** When you `intro` something, give it a *new* name. If you reuse a name
that is already taken (say `intro h` when there is already an `h`), the old `h` is hidden:
it is shown with a † and you can no longer refer to it. If that happens, press Retry and
pick a fresh name.

**Typing:** `→` is `\\to`.
"

/-- If $y = x + 1$, then $x = 2$ implies $y = 3$. -/
Statement (x y : ℝ) (h : y = x + 1) : x = 2 → y = 3 := by
  Hint "Assume $x = 2$, under a new name: `intro hx`."
  intro hx
  Hint "Put what you know about `x` into `{h}`: `rw [{hx}] at {h}`."
  rw [hx] at h
  Hint "Let the calculator tidy up `{h}`: `norm_num at {h}`."
  norm_num at h
  Hint (hidden := true) "`exact {h}`"
  exact h

Conclusion "Most theorems are \"if … then\": `intro` is how every such proof starts."

NewTactic intro
