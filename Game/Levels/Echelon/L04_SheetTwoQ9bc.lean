import Game.Levels.Echelon.L03_SheetTwoQ9a

World "Echelon"
Level 4
Title "Column relations survive"

-- @sheet 2 Q9b-c
/-! @answer
(b) **Conjecture:** any linear relation among the columns of a matrix is preserved by every
row operation (indeed by any sequence of them).
(c) A relation $c_1\,\text{col}_1 + \dots + c_n\,\text{col}_n = \vec 0$ says exactly
$B\vec c = \vec 0$. A row operation (or a sequence of them) replaces $B$ by $EB$ for an
elementary matrix (product) $E$, and $(EB)\vec c = E(B\vec c) = E\vec 0 = \vec 0$. For
Q9 the relation is $\vec c = (1, 1, -1)$.
-/
Introduction "
**Problem Sheet 2, Question 9(b), (c).** Make a conjecture, and briefly sketch an argument
why it holds.

A column relation $c_1\\,\\text{col}_1 + \\dots + c_n\\,\\text{col}_n = \\vec 0$ is the equation
$B\\vec c = \\vec 0$, and row operations multiply $B$ on the left. Lean checks the formal core
below. Also write your conjecture (b) and sketch (c) in a comment `-- Explain:` inside your
proof.
"

namespace LinearAlgebraGame

open Matrix in
/-- If $B\vec c = \vec 0$ then $(EB)\vec c = \vec 0$ for every matrix $E$. -/
Statement {m n : ℕ} (E : Matrix (Fin m) (Fin m) ℝ) (B : Matrix (Fin m) (Fin n) ℝ)
    (c : Fin n → ℝ) (h : B *ᵥ c = 0) : (E * B) *ᵥ c = 0 := by
  Hint "$(EB)\\vec c = E(B\\vec c)$."
  Hint (hidden := true) "`rw [← mulVec_mulVec, h, mulVec_zero]`"
  Hint (hidden := true) "Model explanation: (b) every linear relation among the columns survives every
  row operation. (c) the relation is $B\\vec c = \\vec 0$; a row operation is $B \\mapsto EB$, and
  $(EB)\\vec c = E(B\\vec c) = \\vec 0$."
  rw [← mulVec_mulVec, h, mulVec_zero]

end LinearAlgebraGame

Conclusion "Row operations change the rows but never the linear relations among the columns."

DisabledTactic simp
NewTheorem Matrix.mulVec_mulVec Matrix.mulVec_zero
