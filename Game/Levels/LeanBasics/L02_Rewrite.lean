import Game.Levels.LeanBasics.L01_Exact

World "LeanBasics"
Level 2
Title "Rewriting"

Introduction "
`rw [h]` uses an equation `h : a = b` to replace `a` by `b` in the goal.
`rw [← h]` replaces `b` by `a` instead.
"

/-- If $x = y$ and $y = 5$ then $x = 5$. -/
Statement (x y : ℝ) (h₁ : x = y) (h₂ : y = 5) : x = 5 := by
  Hint "Rewrite the `x` in the goal using `{h₁}`."
  rw [h₁]
  Hint (hidden := true) "The goal is now exactly `{h₂}`."
  exact h₂

NewTactic rw
NewHiddenTactic rewrite
