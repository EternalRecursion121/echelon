import Game.Levels.LeanBasics.L09_Or

World "LeanBasics"
Level 10
Title "If and only if"

Introduction "
`P ↔ Q` (\"P if and only if Q\") is two implications. To *prove* it, `constructor` gives
two goals: `P → Q` and `Q → P` — prove each with `intro`.

To *use* a hypothesis `h : P ↔ Q`: `h.mp` is its forward direction `P → Q` and `h.mpr` the
backward one `Q → P` (so `h.mp hp : Q` when `hp : P`). `rw [h]` also works: it replaces `P`
by `Q`.

**Typing:** `↔` is `\\iff`.
"

/-- If $x = y$, then $x = 2 \iff y = 2$. -/
Statement (x y : ℝ) (h : x = y) : x = 2 ↔ y = 2 := by
  Hint "Split the \"iff\" into its two directions: `constructor`."
  constructor
  · Hint "Forward direction: assume `x = 2` (`intro h2`) and prove `y = 2`."
    intro h2
    Hint (hidden := true) "`rw [← {h}]` turns `y` into `x`; then `exact {h2}`."
    rw [← h]
    exact h2
  · Hint "Backward direction: assume `y = 2` and prove `x = 2`."
    intro h2
    Hint (hidden := true) "`rw [{h}]`, then `exact {h2}`."
    rw [h]
    exact h2

Conclusion "Sheet questions of the form \"show these are equivalent\" start with this `constructor`."
