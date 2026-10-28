import Game.Levels.LeanBasics.L08_Vectors

World "LeanBasics"
Level 9
Title "Commit, then prove"

-- A decide level: the goal is "P or not P"; you choose a side before proving it.
Introduction "
Many sheet questions say *\"true or false?\"*. In this game they look like this: the goal
is `¬ P ∨ P`. You commit with `left` (false) or `right` (true), then prove your choice.
Choose wrong and you will get stuck — which is the lesson.

**Claim:** for every real $x$, $x \\cdot x = x$.
"

/-- True or false: for every real $x$, $x \cdot x = x$. -/
Statement : (¬ ∀ x : ℝ, x * x = x) ∨ (∀ x : ℝ, x * x = x) := by
  Hint "Decide first. Is it true for $x = 2$?"
  left
  Hint "To refute a \"for all\", assume it with `intro h` and find a counterexample."
  intro h
  Hint (hidden := true) "`have h2 := {h} 2` specialises it to $x = 2$."
  have h2 := h 2
  norm_num at h2

NewTactic «have»
