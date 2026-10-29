import Game.Levels.LeanBasics.L12_ForAllExists

World "LeanBasics"
Level 13
Title "Vectors"

Introduction "
In this game a vector in $\\mathbb R^n$ is written with square brackets after an
exclamation mark: `![3, 7]` is the vector $\\begin{pmatrix}3\\\\7\\end{pmatrix}$ in $\\mathbb R^2$.
Its type is `Fin 2 → ℝ`: `Fin 2` is the set of positions $\\{0, 1\\}$.

A vector is really a *function* from positions to numbers, so `v 0` is its first entry and
`v 1` its second. **Positions are numbered from 0.**

Two vectors are equal when they agree in every position. The tactic `entrywise` turns
`u = v` into one goal per position — `u 0 = v 0`, `u 1 = v 1`, … — shown as tabs.
`norm_num` can read off an entry of a vector written out with `![…]`.

(Under the hood, `entrywise` is `ext i` followed by `fin_cases i` — two tactics you will
also use on their own later: `ext` reduces an equation of vectors to one entry `i`, and
`fin_cases i` splits into the possible positions.)
"

/-- If $x = 1$ then $(x, 2) + (3, 4) = (4, 6)$. -/
Statement (x : ℝ) (h : x = 1) : ![x, 2] + ![3, 4] = (![4, 6] : Fin 2 → ℝ) := by
  Hint "Check entry by entry: `entrywise`."
  entrywise
  · Hint "Position 0 (the first tab): $x + 3 = 4$. Get rid of `x` first, then calculate."
    Hint (hidden := true) "`rw [{h}]`, then `norm_num`."
    rw [h]
    norm_num
  · Hint "Position 1 (the other tab): $2 + 4 = 6$."
    Hint (hidden := true) "`norm_num`"
    norm_num

Conclusion "Entry by entry is the method that always works for vectors: it turns one vector
equation into a few equations between numbers."

NewTactic entrywise ext fin_cases
NewDefinition Fin
