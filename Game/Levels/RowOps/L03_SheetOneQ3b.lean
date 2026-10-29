import Game.Levels.RowOps.L02_SheetOneQ1

World "RowOps"
Level 3
Title "Two lines that cross"

-- @sheet 1 Q3b
/-! @answer
$$\left(\begin{array}{cc|c}1&1&1\\1&-1&-1\end{array}\right)
\xrightarrow{-\rho_1+\rho_2}\left(\begin{array}{cc|c}1&1&1\\0&-2&-2\end{array}\right),$$
so $y = 1$ and $x = 0$: the solution set is $\left\{\begin{pmatrix}0\\1\end{pmatrix}\right\}$.
-/
Introduction "
**Problem Sheet 1, Question 3(b).** Solve using matrix notation, expressing the solution
using vectors: $x + y = 1,\\ x - y = -1$.

The answer is a vector $\\vec p$: the claim says the system holds exactly when
`![x, y] = p`. Supply your `p` with `use`. To prove two vectors equal, `entrywise`
(Lean Basics); to read an equation of vectors `h : u = v` entry by entry, `congrFun h 0` is
its entry 0, `u 0 = v 0`.
"

namespace LinearAlgebraGame

/-- The solution set of $x + y = 1,\ x - y = -1$ is a single vector $\vec p$. -/
Statement : ∃ p : Fin 2 → ℝ, ∀ x y : ℝ, (x + y = 1 ∧ x - y = -1) ↔ ![x, y] = p := by
  Hint "Solve the system on paper, then `use` the solution vector (written `![…, …]`)."
  Hint (hidden := true) "`use ![0, 1]`, then `intro x y` and `constructor`."
  use ![0, 1]
  intro x y
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := h
    Hint "Eliminate $x$ from the second row."
    Hint (hidden := true) "`rowop h2 : y = 1 := (h1 - h2) / 2`"
    rowop h2 : y = 1 := (h1 - h2) / 2
    rowop h1 : x = 0 := h1 - h2
    Hint "Now prove the vector equation entry by entry. The entries (`![x, y] 0` and so on) are
    not evaluated yet: in each entry run `norm_num` before anything else (a warning that it
    did nothing in some entry is harmless)."
    Hint (hidden := true) "`entrywise`, then in each case `norm_num` and `exact`."
    entrywise
    · norm_num
      exact h1
    · norm_num
      exact h2
  · intro h
    Hint "Read off the two entries of `{h}`."
    Hint (hidden := true) "`have hx := congrFun {h} 0`, `have hy := congrFun {h} 1`, then
    `norm_num at hx hy`, `rw [hx, hy]` and `norm_num`."
    have hx := congrFun h 0
    have hy := congrFun h 1
    norm_num at hx hy
    rw [hx, hy]
    norm_num

end LinearAlgebraGame

Conclusion "**Answer:** the single vector $(0, 1)$."

TheoremTab "Vectors"

DisabledTactic linarith nlinarith
NewTheorem congrFun
