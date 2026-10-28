import Game.Metadata
import Game.Ch45

World "Volume"
Level 1
Title "Products"

Introduction "
**Theorem Four.II.1.5 / 1.4:** $|TS| = |T|\\,|S|$ (`Matrix.det_mul`). Hefferon's proof: a
transformation scales every box by $|\\det|$, and doing two transformations in a row scales
by the product.

Use it to show that $TS$ and $ST$ always have the same determinant, even though
$TS \\ne ST$ in general.
"

namespace LinearAlgebraGame

/-- $\det(TS) = \det(ST)$. -/
Statement {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℝ) : (T * S).det = (S * T).det := by
  Hint "Both sides are a product of two real numbers."
  Hint (hidden := true) "`rw [Matrix.det_mul, Matrix.det_mul, mul_comm]`."
  rw [Matrix.det_mul, Matrix.det_mul, mul_comm]

end LinearAlgebraGame

Conclusion "Determinants turn matrix multiplication (non-commutative) into real multiplication (commutative)."

DisabledTheorem Matrix.det_mul_comm
DisabledTactic simp norm_num
TheoremTab "Det"
