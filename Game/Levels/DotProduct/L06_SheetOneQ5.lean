import Game.Levels.DotProduct.L05_SheetOneQ6

World "DotProduct"
Level 6
Title "Two planes meet in a line"

-- @sheet 1 Q5
/-! @answer
A common point satisfies $t(1,1,1) + s(0,1,3) = (1,1,0) + k(0,3,0) + m(2,0,4)$, i.e.
$t = 1 + 2m$, $t + s = 1 + 3k$, $t + 3s = 4m$. Gauss's method gives $s = (2m-1)/3$ and
$k = (8m-1)/9$ with $m$ free, so the common points are
$(1+2m,\ (2+8m)/3,\ 4m)$. With $\mu = 2m/3$ the intersection is the **line
$\{(1, 2/3, 0) + \mu(3, 4, 6) \mid \mu \in \mathbb R\}$**. Conversely each such point lies in
the first plane ($t = 1 + 3\mu$, $s = \mu - 1/3$) and the second
($k = 4\mu/3 - 1/9$, $m = 3\mu/2$).
-/
Introduction "
**Problem Sheet 1, Question 5.** Intersect these planes:
$$\\{t(1,1,1) + s(0,1,3) \\mid t, s \\in \\mathbb R\\},\\qquad
\\{(1,1,0) + k(0,3,0) + m(2,0,4) \\mid k, m \\in \\mathbb R\\}.$$

You supply the intersection as a line $\\{\\vec p + \\mu\\vec d\\}$ (`use p, d`): the claim
says a vector lies on both planes exactly when it lies on your line.

**New: `<;>`.** `tac1 <;> tac2` runs `tac2` on *every* goal that `tac1` produces. So
`entrywise <;> norm_num <;> linear_combination` checks all three entries of a vector
equation at once (when each entry is plain algebra).
"

namespace LinearAlgebraGame

/-- The two planes meet in a line $\{\vec p + \mu\vec d \mid \mu \in \mathbb R\}$. -/
Statement : ∃ p d : Fin 3 → ℝ, ∀ v : Fin 3 → ℝ,
    ((∃ t s : ℝ, v = t • ![1, 1, 1] + s • ![0, 1, 3]) ∧
      (∃ k m : ℝ, v = ![1, 1, 0] + k • ![0, 3, 0] + m • ![2, 0, 4])) ↔
    ∃ μ : ℝ, v = p + μ • d := by
  Hint "Solve on paper first: equate the two descriptions and use Gauss's method. One
  parameter stays free — that gives the line. `use` its point and direction."
  Hint (hidden := true) "`use ![1, 2/3, 0], ![3, 4, 6]`, then `intro v` and `constructor`."
  use ![1, 2/3, 0], ![3, 4, 6]
  intro v
  constructor
  · intro h
    obtain ⟨⟨t, s, h1⟩, ⟨k, m, h2⟩⟩ := h
    Hint "Equate the two descriptions of $\\vec v$ and read off three equations. (For equations,
    `h1.symm` flips `h1`, and `h1.trans h2` chains `a = b` and `b = c` into `a = c`.)"
    Hint (hidden := true) "`have e := h1.symm.trans h2` (`h1.symm` flips `h1`; `.trans` chains
    two equations), then `congrFun e 0` etc. and `norm_num at`."
    have e := h1.symm.trans h2
    have e₀ := congrFun e 0
    have e₁ := congrFun e 1
    have e₂ := congrFun e 2
    norm_num at e₀ e₁ e₂
    Hint (hidden := true) "With the line $(1, 2/3, 0) + \\mu(3,4,6)$: $m$ is free and
    $\\mu = 2m/3$. `use 2 * m / 3`, `rw [h2]`, then `entrywise`."
    use 2 * m / 3
    rw [h2]
    entrywise
    · norm_num
      linear_combination
    · norm_num
      Hint (hidden := true) "`linear_combination (2 * e₀ + e₂ - 3 * e₁) / 3`"
      linear_combination (2 * e₀ + e₂ - 3 * e₁) / 3
    · norm_num
      linear_combination
  · intro h
    obtain ⟨μ, hμ⟩ := h
    rw [hμ]
    Hint "Find the parameters for each plane."
    constructor
    · Hint (hidden := true) "`use 1 + 3 * μ, μ - 1/3`, then
      `entrywise <;> norm_num <;> linear_combination`."
      use 1 + 3 * μ, μ - 1/3
      entrywise <;> norm_num <;> linear_combination
    · Hint (hidden := true) "`use 4 * μ / 3 - 1/9, 3 * μ / 2`"
      use 4 * μ / 3 - 1/9, 3 * μ / 2
      entrywise <;> norm_num <;> linear_combination

end LinearAlgebraGame

Conclusion "**Answer:** the line $\\{(1, 2/3, 0) + \\mu(3,4,6) \\mid \\mu \\in \\mathbb R\\}$."
