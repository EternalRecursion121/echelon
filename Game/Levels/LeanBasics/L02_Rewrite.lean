import Game.Levels.LeanBasics.L01_Exact

World "LeanBasics"
Level 2
Title "Rewriting"

Introduction "
`rw [h]` uses an equation `h : a = b` to replace `a` by `b` in the goal.
`rw [← h]` replaces `b` by `a` instead.

**Typing symbols.** Type a backslash code and then a space: `\\l` gives `←`, `\\R` gives `ℝ`,
`\\to` gives `→`. Hover over any symbol in the editor to see how to type it. The full table
is under **Game Info** in the menu.
"

/-- If $x = y$ and $y = 5$ then $x = 5$. -/
Statement (x y : ℝ) (h1 : x = y) (h2 : y = 5) : x = 5 := by
  Hint "Rewrite the `x` in the goal using `{h1}`."
  rw [h1]
  Hint (hidden := true) "The goal is now exactly `{h2}`."
  exact h2

NewTactic rw
NewHiddenTactic rewrite
