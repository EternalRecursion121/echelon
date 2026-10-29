import Game.Levels.LeanBasics.L03_NormNum

World "LeanBasics"
Level 4
Title "Using an \"and\""

Introduction "
A system of equations is a big \"and\". To *use* a hypothesis `h : P ∧ Q`, take it apart:
`obtain ⟨hp, hq⟩ := h` replaces `h` by its two halves `hp : P` and `hq : Q` (you choose the
names).

**Typing:** the angle brackets `⟨ ⟩` are `\\<` and `\\>`; `∧` is `\\and`.
"

/-- If $x = 1$ and $y = 2$, then $y = 2$. -/
Statement (x y : ℝ) (h : x = 1 ∧ y = 2) : y = 2 := by
  Hint "Take `{h}` apart: `obtain ⟨hx, hy⟩ := {h}`."
  obtain ⟨hx, hy⟩ := h
  Hint "The goal is now one of your hypotheses."
  Hint (hidden := true) "`exact {hy}`"
  exact hy

Conclusion "`obtain` is how you read off the equations of a system you are given."

NewTactic obtain
