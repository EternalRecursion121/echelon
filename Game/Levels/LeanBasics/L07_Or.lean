import Game.Levels.LeanBasics.L06_Not

World "LeanBasics"
Level 7
Title "Or, and case splits"

Introduction "
To prove `P ∨ Q`, pick a side with `left` or `right`. To use `h : P ∨ Q`, split into
two cases with `rcases h with hp | hq`.
"

/-- If $x = 1$ or $x = 2$, then $x^2 = 1$ or $x^2 = 4$. -/
Statement (x : ℝ) (h : x = 1 ∨ x = 2) : x * x = 1 ∨ x * x = 4 := by
  Hint "Split on `{h}`: `rcases {h} with h1 | h2`."
  rcases h with h1 | h2
  · Hint "Here `x = 1`. Which side of the goal is true?"
    left
    rw [h1]
    norm_num
  · right
    rw [h2]
    norm_num

/-- `left` / `right` choose which side of a goal `P ∨ Q` to prove. -/
TacticDoc left
/-- See `left`. -/
TacticDoc right
/-- `rcases h with h1 | h2` splits `h : P ∨ Q` into two cases; `rcases h with ⟨a, b⟩`
takes apart `∧` and `∃`. -/
TacticDoc rcases
NewTactic left right rcases
