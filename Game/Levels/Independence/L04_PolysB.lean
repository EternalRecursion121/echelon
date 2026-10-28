import Game.Levels.Independence.L03_PolysA

World "Independence"
Level 4
Title "Four polynomials"

-- @sheet 3 Q4b
/-! @answer
**Dependent.** Setting
$c_1(8 + 3x + 3x^2) + c_2(x + 2x^2) + c_3(2 + 2x + 2x^2) + c_4(8 - 2x + 5x^2) = 0$ and comparing
coefficients gives three homogeneous equations in four unknowns
($8c_1 + 2c_3 + 8c_4 = 0$, $3c_1 + c_2 + 2c_3 - 2c_4 = 0$, $3c_1 + 2c_2 + 2c_3 + 5c_4 = 0$),
which must have a nontrivial solution; Gauss's method gives e.g.
$(c_1, c_2, c_3, c_4) = (-17, -35, 48, 5)$:
$$-17(8+3x+3x^2) - 35(x+2x^2) + 48(2+2x+2x^2) + 5(8-2x+5x^2) = 0.$$
-/
Introduction "
**Problem Sheet 3, Question 4(b).** Is
$\\{8 + 3x + 3x^2,\\ x + 2x^2,\\ 2 + 2x + 2x^2,\\ 8 - 2x + 5x^2\\}$ (in $\\mathcal{P}_3$)
linearly dependent or independent?

`Fintype.not_linearIndependent_iff` says a family is dependent iff some combination with
coefficients `g` sums to zero while some `g i ≠ 0`. Find the coefficients by Gauss's method
on paper (three equations, four unknowns), then let Lean check them.

Decide: `left` for dependent, `right` for independent.
"

namespace LinearAlgebraGame

/-- Is $\{8 + 3x + 3x^2, x + 2x^2, 2 + 2x + 2x^2, 8 - 2x + 5x^2\}$ linearly independent? -/
Statement : (¬ LinearIndependent ℝ
      ![(![8, 3, 3, 0] : Poly 3), ![0, 1, 2, 0], ![2, 2, 2, 0], ![8, -2, 5, 0]]) ∨
    LinearIndependent ℝ
      ![(![8, 3, 3, 0] : Poly 3), ![0, 1, 2, 0], ![2, 2, 2, 0], ![8, -2, 5, 0]] := by
  Hint "Four vectors, but only three coefficients ($1, x, x^2$) to match."
  left
  rw [Fintype.not_linearIndependent_iff]
  Hint (hidden := true) "Gauss's method gives the relation `use ![-17, -35, 48, 5]`."
  use ![-17, -35, 48, 5]
  constructor
  · Hint (hidden := true) "Check each coefficient: `ext i`, then
    `fin_cases i <;> simp [Fin.sum_univ_four] <;> norm_num`."
    ext i
    fin_cases i <;> simp [Fin.sum_univ_four] <;> norm_num
  · use 0
    norm_num

end LinearAlgebraGame

Conclusion "**Answer: dependent**, e.g. $-17p_1 - 35p_2 + 48p_3 + 5p_4 = 0$."

TheoremTab "Independence"
NewTheorem Fin.sum_univ_four Fintype.not_linearIndependent_iff
