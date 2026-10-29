import Game.Metadata
import Game.Ch45

World "Volume"
Level 1
Title "Products"

Introduction "
**Theorem Four.II.1.5:** $|TS| = |T|\\,|S|$ (`Matrix.det_mul`).

Hefferon's proof reuses the Determinant world. If $|S| = 0$ both sides are $0$. Otherwise
consider $d(T) = |TS|/|S|$. Row operations on $T$ are row operations on $TS$ (the rows of
$TS$ are the rows of $T$ times $S$), so $d$ satisfies the four conditions, and $d(I) = 1$.
By uniqueness, $d$ *is* the determinant: $|TS|/|S| = |T|$.
Geometrically: $S$ scales every box by $|\\det S|$, then $T$ scales by $|\\det T|$.

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
