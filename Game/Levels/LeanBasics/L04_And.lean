import Game.Levels.LeanBasics.L03_NormNum

World "LeanBasics"
Level 4
Title "And"

Introduction "
A system of equations is a big \"and\". To *use* `h : P ∧ Q`, split it with
`obtain ⟨hp, hq⟩ := h`. To *prove* `P ∧ Q`, use `constructor`, which leaves two goals.

**Typing:** the angle brackets `⟨ ⟩` are `\\<` and `\\>`; `∧` is `\\and`.
"

/-- If $x = 1$ and $y = 2$, then $y = 2$ and $x = 1$. -/
Statement (x y : ℝ) (h : x = 1 ∧ y = 2) : y = 2 ∧ x = 1 := by
  Hint "Take `{h}` apart: `obtain ⟨hx, hy⟩ := {h}`."
  obtain ⟨hx, hy⟩ := h
  Hint "Now `constructor` splits the goal into two."
  constructor
  · Hint "Two goals now (see the tabs). This one is literally one of your assumptions —
    which? Close it with `exact` followed by that assumption's name."
    Hint (hidden := true) "`exact {hy}`"
    exact hy
  · Hint (hidden := true) "`exact {hx}`"
    exact hx

NewTactic constructor obtain
