import Game.Levels.LeanBasics.L08_Components

World "LeanBasics"
Level 9
Title "Vectors: equal entry by entry"

Introduction "
Two vectors are equal when they agree in every position. The tactic `entrywise` turns
`u = v` into one goal per position — `u 0 = v 0`, `u 1 = v 1`, … — shown as tabs.

(Under the hood, `entrywise` is `ext i` followed by `fin_cases i` — two tactics you will also use on their own later: `ext` reduces an equation of vectors to one entry `i`, and `fin_cases i` splits into the possible positions.)
"

/-- $(1, 2) + (3, 4) = (4, 6)$. -/
Statement : (![1, 2] : Fin 2 → ℝ) + ![3, 4] = ![4, 6] := by
  Hint "Check entry by entry: `entrywise`."
  entrywise
  · Hint "Position 0: $1 + 3 = 4$. The calculator handles it."
    Hint (hidden := true) "`norm_num`"
    norm_num
  · Hint "Position 1 (the other tab): $2 + 4 = 6$."
    norm_num

Conclusion "Here `norm_num` could actually have done the whole thing at once — but
entry-by-entry is the method that still works when the entries are letters, not numbers.

(Under the hood `entrywise` is `ext i` followed by `fin_cases i`; you'll meet those two
later, where they're useful on their own.)"

NewTactic entrywise ext fin_cases
