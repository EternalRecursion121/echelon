import Game.Levels.DotProduct.L03_SheetOneQ7

World "DotProduct"
Level 4
Title "Equal lengths, perpendicular diagonals"

-- @sheet 1 Q8
/-! @answer
Expanding, $(\vec u + \vec v)\cdot(\vec u - \vec v) = \vec u\cdot\vec u - \vec u\cdot\vec v
+ \vec v\cdot\vec u - \vec v\cdot\vec v = |\vec u|^2 - |\vec v|^2$. So the two vectors are
perpendicular iff $|\vec u|^2 = |\vec v|^2$, iff $|\vec u| = |\vec v|$ (lengths are
$\ge 0$, and $|\vec v| = \sqrt{\vec v\cdot\vec v}$).
-/
Introduction "
**Problem Sheet 1, Question 8.** Show that $|\\vec u| = |\\vec v|$ if and only if
$\\vec u + \\vec v$ and $\\vec u - \\vec v$ are perpendicular.

Perpendicular means the dot product is $0$. New: `linarith` (linear arithmetic from
hypotheses) is unlocked.
"

namespace LinearAlgebraGame

/-- $|\vec u| = |\vec v| \iff (\vec u + \vec v)\cdot(\vec u - \vec v) = 0$. -/
Statement {n : ℕ} (u v : Fin n → ℝ) : len u = len v ↔ (u + v) ⬝ᵥ (u - v) = 0 := by
  Hint "Expand $(\\vec u + \\vec v)\\cdot(\\vec u - \\vec v)$ first."
  Hint (hidden := true) "`rw [add_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v u]`"
  rw [add_dotProduct, dotProduct_sub, dotProduct_sub, dotProduct_comm v u]
  constructor
  · intro h
    Hint (hidden := true) "`len_sq u : len u ^ 2 = u ⬝ᵥ u`. `rw [← len_sq u, ← len_sq v, h]`, then `ring`."
    rw [← len_sq u, ← len_sq v, h]
    ring
  · intro h
    Hint "From `h`, $\\vec u\\cdot\\vec u = \\vec v\\cdot\\vec v$; and $|\\vec v|$ is defined from $\\vec v\\cdot\\vec v$."
    Hint (hidden := true) "`rw [len, len, show u ⬝ᵥ u = v ⬝ᵥ v by linarith]`"
    rw [len, len, show u ⬝ᵥ u = v ⬝ᵥ v by linarith]

end LinearAlgebraGame

Conclusion "The diagonals of a parallelogram are perpendicular exactly when it is a rhombus."

TheoremTab "Dot"
NewTactic linarith «show»
NewTheorem dotProduct_sub LinearAlgebraGame.len_sq sub_dotProduct dotProduct_comm
