import Game.Levels.DotProduct.L07_CauchySchwarz

World "DotProduct"
Level 8
Title "The triangle inequality"

Introduction "
Hefferon One.II.2.5: $|\\vec u + \\vec v| \\le |\\vec u| + |\\vec v|$. Square both sides:
$|\\vec u + \\vec v|^2 = |\\vec u|^2 + 2\\,\\vec u\\cdot\\vec v + |\\vec v|^2$, and Cauchy–Schwarz
bounds the middle term.
"

namespace LinearAlgebraGame

/-- $|\vec u + \vec v| \le |\vec u| + |\vec v|$. -/
Statement len_add_le {n : ℕ} (u v : Fin n → ℝ) : len (u + v) ≤ len u + len v := by
  Hint "Collect the facts: Cauchy–Schwarz, and the expansion of $(\\vec u+\\vec v)\\cdot(\\vec u+\\vec v)$."
  have h := cauchy_schwarz u v
  Hint (strict := true) (hidden := true) "`have e : (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by`
  `rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm v u]` then `ring`."
  have e : (u + v) ⬝ᵥ (u + v) = u ⬝ᵥ u + 2 * (u ⬝ᵥ v) + v ⬝ᵥ v := by
    rw [add_dotProduct, dotProduct_add, dotProduct_add, dotProduct_comm v u]
    ring
  Hint (strict := true) (hidden := true) "`nlinarith [len_sq (u + v), len_sq u, len_sq v, len_nonneg (u + v),
  len_nonneg u, len_nonneg v, le_abs_self (u ⬝ᵥ v)]`"
  nlinarith [len_sq (u + v), len_sq u, len_sq v, len_nonneg (u + v), len_nonneg u, len_nonneg v,
    le_abs_self (u ⬝ᵥ v)]

end LinearAlgebraGame

Conclusion "`len_add_le` is now in your inventory."

NewTactic positivity
NewTheorem LinearAlgebraGame.len_nonneg le_abs_self
