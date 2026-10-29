import Game.Levels.LeanBasics.L06_Not

World "LeanBasics"
Level 7
Title "Or, and case splits"

Introduction "
Two moves with \"or\":
- To *prove* `P ∨ Q`, pick the side you can prove: `left` turns the goal into `P`,
  `right` turns it into `Q`.
- To *use* `h : P ∨ Q`, split into two cases with `rcases h with hp | hq`. You then get
  **two goals** (two tabs): the first where `hp : P` holds, the second where `hq : Q`
  holds. Each still has the original goal, and you prove it once per case.

**Typing:** `∨` is `\\or`; the bar `|` is on your keyboard.
"

/-- If $x = 1$ or $x = 2$, then $x \cdot x = 1$ or $x \cdot x = 4$. -/
Statement (x : ℝ) (h : x = 1 ∨ x = 2) : x * x = 1 ∨ x * x = 4 := by
  Hint "Split on `{h}`: `rcases {h} with h1 | h2`."
  rcases h with h1 | h2
  · Hint "This is the case `{h1} : x = 1` (the other case is in the next tab). The goal is
    still an \"or\": which side is true when $x = 1$?"
    Hint (hidden := true) "$1 \\cdot 1 = 1$, so the left side. `left`, then `rw [{h1}]`, then `norm_num`."
    left
    rw [h1]
    norm_num
  · Hint "Now the case `{h2} : x = 2`. Which side is true now?"
    Hint (hidden := true) "`right`, then `rw [{h2}]`, then `norm_num`."
    right
    rw [h2]
    norm_num

NewTactic left right rcases
