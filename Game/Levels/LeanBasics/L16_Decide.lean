import Game.Levels.LeanBasics.L15_MatVec

World "LeanBasics"
Level 16
Title "Commit, then prove"

-- A decide level: the goal is "P or not P"; you choose a side before proving it.
Introduction "
Many sheet questions say *\"true or false?\"*. In this game they look like this: the goal
is `¬ P ∨ P`. You commit with `left` (false) or `right` (true), then prove your choice.
Work it out on paper first: if you pick the wrong side, the goal becomes impossible — just
press Retry and choose the other side.

To refute a \"for all\", assume it and feed it a counterexample, as in level 11
(e.g. `have h7 := h 7` is the fact for $x = 7$).
"

/-- True or false: for every real $x$, $x \cdot x = x$. -/
Statement : (¬ ∀ x : ℝ, x * x = x) ∨ (∀ x : ℝ, x * x = x) := by
  Hint "Decide first: try a few values of $x$."
  left
  Hint "To refute a \"for all\", assume it with `intro h` and find a counterexample."
  intro h
  Hint "`{h}` says something about *every* $x$. Apply it to your counterexample
  (as in level 11: `have … := {h} …`)."
  Hint (hidden := true) "`have h2 := {h} 2` specialises it to $x = 2$; then `norm_num at h2`."
  have h2 := h 2
  norm_num at h2

