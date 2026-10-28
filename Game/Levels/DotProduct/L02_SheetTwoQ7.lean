import Game.Levels.DotProduct.L01_Length

World "DotProduct"
Level 2
Title "The dot product is linear"

-- @sheet 2 Q7
/-! @answer
$$\vec u\cdot(k\vec v + m\vec w) = \sum_i u_i(kv_i + mw_i) = \sum_i (k\,u_iv_i + m\,u_iw_i)
= k\sum_i u_iv_i + m\sum_i u_iw_i = k(\vec u\cdot\vec v) + m(\vec u\cdot\vec w).$$
-/
Introduction "
**Problem Sheet 2, Question 7.** Show that the inner product operation is *linear*: for
$\\vec u, \\vec v, \\vec w \\in \\mathbb R^n$ and $k, m \\in \\mathbb R$,
$\\vec u \\cdot (k\\vec v + m\\vec w) = k(\\vec u\\cdot\\vec v) + m(\\vec u\\cdot\\vec w)$.

`rw [dotProduct]` unfolds a dot product into its sum. To show two sums are equal
term by term, `congr 1` then `ext i`.
"

namespace LinearAlgebraGame

/-- $\vec u\cdot(k\vec v + m\vec w) = k(\vec u\cdot\vec v) + m(\vec u\cdot\vec w)$. -/
Statement {n : ℕ} (u v w : Fin n → ℝ) (k m : ℝ) :
    u ⬝ᵥ (k • v + m • w) = k * (u ⬝ᵥ v) + m * (u ⬝ᵥ w) := by
  Hint "Write everything as sums, pull $k$ and $m$ inside, and combine into one sum."
  Hint (hidden := true) "`rw [dotProduct, dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum,
  ← Finset.sum_add_distrib]`"
  rw [dotProduct, dotProduct, dotProduct, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  Hint "Now compare the sums term by term."
  Hint (hidden := true) "`congr 1`, then `ext i`."
  congr 1
  ext i
  Hint (hidden := true) "`rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]`,
  then `ring`."
  rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
  ring

end LinearAlgebraGame

Conclusion "From now on `dotProduct_add` and `dotProduct_smul` (and their mirror images) are in your inventory."

DisabledTactic norm_num simp
DisabledTheorem dotProduct_add dotProduct_smul add_dotProduct smul_dotProduct
TheoremTab "Sums"

NewTactic congr ring
NewTheorem Finset.mul_sum Finset.sum_add_distrib Pi.add_apply Pi.smul_apply smul_eq_mul
