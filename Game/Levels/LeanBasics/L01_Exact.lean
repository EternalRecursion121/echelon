import Game.Metadata

World "LeanBasics"
Level 1
Title "Goals and hypotheses"

Introduction "
A Lean proof is a conversation with a *goal* (after `⊢`) and the *hypotheses* above it.
Here the hypothesis `h` says exactly what the goal says.
"

/-- If $x = 3$ then $x = 3$. -/
Statement (x : ℝ) (h : x = 3) : x = 3 := by
  Hint "`exact h` closes the goal when `h` is literally the goal."
  exact h

Conclusion "Every proof in this game ends, eventually, with a step like this one."

NewTactic exact
