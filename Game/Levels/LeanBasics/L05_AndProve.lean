import Game.Levels.LeanBasics.L04_AndUse

World "LeanBasics"
Level 5
Title "Proving an \"and\""

Introduction "
To *prove* `P ∧ Q`, use `constructor`: it leaves two goals, `P` and `Q`.

**Two goals.** After `constructor` there are two goals (tabs). In the editor you write each
goal's proof after a bullet `·` (typed `\\.`), indented under it:
```
constructor
· exact …
· exact …
```
**Shortcut:** if you already have both halves, `exact ⟨hp, hq⟩` builds `P ∧ Q` in one go —
the same angle brackets as `obtain`, used the other way round.

**Typing:** `·` is `\\.`.
"

/-- If $x = 1$ and $y = 2$, then $y = 2$ and $x = 1$. -/
Statement (x y : ℝ) (hx : x = 1) (hy : y = 2) : y = 2 ∧ x = 1 := by
  Hint "`constructor` splits the goal into two."
  Hint (hidden := true) "Or in one step: `exact ⟨{hy}, {hx}⟩`."
  constructor
  · Hint "Two goals now (see the tabs). This one is literally one of your assumptions —
    which? Close it with `exact` followed by that assumption's name."
    Hint (hidden := true) "`exact {hy}`"
    exact hy
  · Hint (hidden := true) "`exact {hx}`"
    exact hx

Conclusion "Proving a system of equations holds is exactly this: one goal per equation."

NewTactic constructor
