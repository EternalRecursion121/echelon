import Game.Levels.RowOps.L13_SheetTwoQ3Generic

World "RowOps"
Level 14
Title "A parameter: a = 1 and a = −1"

-- @sheet 2 Q3
/-! @answer
Case $a = 1$: both equations read $x + y = 1$, so $y$ is free and the solution set is
**$\{(1, 0) + t(-1, 1) \mid t \in \mathbb R\}$ — infinitely many solutions**.
Case $a = -1$: the equations are $-x + y = 1$ and $x - y = 1$; adding them gives $0 = 2$.
**No solution.**
-/
Introduction "
**Problem Sheet 2, Question 3, cases $a = 1$ and $a = -1$.** Solve
$ax + y = a^2,\\ x + ay = 1$ when $a = 1$, and when $a = -1$.

The claim has two parts (`constructor`):
1. for $a = 1$: the solution set is a line $\\{\\vec p + t\\vec d\\}$ — supply $\\vec p$, $\\vec d$
   as in level 4;
2. for $a = -1$: decide whether there is a solution (`left`: none, `right`: there is one).

(The value of $a$ is substituted and tidied: for $a = 1$ the system reads $x + y = 1,\\ x + y = 1$;
for $a = -1$ it reads $-x + y = 1,\\ x - y = 1$.)
"

namespace LinearAlgebraGame

/-- The cases $a = 1$ and $a = -1$ of $ax + y = a^2,\ x + ay = 1$. -/
Statement :
    (∃ p d : Fin 2 → ℝ, ∀ x y : ℝ,
      (x + y = 1 ∧ x + y = 1) ↔ ∃ t : ℝ, ![x, y] = p + t • d) ∧
    ((¬ ∃ x y : ℝ, -x + y = 1 ∧ x - y = 1) ∨
      (∃ x y : ℝ, -x + y = 1 ∧ x - y = 1)) := by
  constructor
  · Hint "For $a = 1$ the two rows are the same equation. Which variable is free?"
    Hint (hidden := true) "`use ![1, 0], ![-1, 1]`, then `intro x y` and `constructor`."
    use ![1, 0], ![-1, 1]
    intro x y
    constructor
    · intro h
      obtain ⟨h1, h2⟩ := h
      Hint (hidden := true) "With $y$ free: `use y`, `entrywise`, `norm_num` and
      `linear_combination h2`."
      use y
      entrywise
      · Hint "The entries are still unevaluated (`(p + t • d) 0` and so on): `norm_num` evaluates
        them first, then the entry is ordinary algebra."
        norm_num
        linear_combination h2
      · norm_num
    · intro h
      obtain ⟨t, ht⟩ := h
      have hx := congrFun ht 0
      have hy := congrFun ht 1
      norm_num at hx hy
      rw [hx, hy]
      constructor
      · linear_combination
      · linear_combination
  · Hint "For $a = -1$: run Gauss's method on paper, then commit."
    left
    intro h
    obtain ⟨x, y, h1, h2⟩ := h
    Hint "Add the two rows."
    Hint (hidden := true) "`rowop h2 : 0 = 2 := h1 + h2`, then `norm_num at h2`."
    rowop h2 : 0 = 2 := h1 + h2
    norm_num at h2

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 2 Q3:** $a \\ne \\pm 1$: unique solution
$\\left(\\frac{a^2+a+1}{a+1}, \\frac{-a}{a+1}\\right)$; $a = 1$: infinitely many
(the line $x + y = 1$); $a = -1$: none.
"

DisabledTactic linarith nlinarith
