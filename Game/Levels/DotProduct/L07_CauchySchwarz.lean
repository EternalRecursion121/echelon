import Game.Levels.DotProduct.L06_SheetOneQ5

World "DotProduct"
Level 7
Title "Cauchy–Schwarz"

Introduction "
**Boss.** The Cauchy–Schwarz inequality (Hefferon One.II.2.4):
$|\\vec u\\cdot\\vec v| \\le |\\vec u|\\,|\\vec v|$.

The idea: a length squared is never negative. Apply that to
$\\vec w = (\\vec v\\cdot\\vec v)\\,\\vec u - (\\vec u\\cdot\\vec v)\\,\\vec v$. Expanding (granted as
`dot_expand`) gives
$0 \\le (\\vec v\\cdot\\vec v)\\big[(\\vec u\\cdot\\vec u)(\\vec v\\cdot\\vec v) - (\\vec u\\cdot\\vec v)^2\\big]$,
and you can divide by $\\vec v\\cdot\\vec v$ unless it is $0$ — in which case $\\vec v = \\vec 0$.

New: `nlinarith` (`linarith` that may multiply hypotheses).

**Dot notation on facts.** If `h : a ≤ b` then `h.eq_or_lt : a = b ∨ a < b` (the lemma
`LE.le.eq_or_lt` applied to `h`), `h.symm` flips an equation, and for an iff `h.mp`/`h.mpr`
are its two directions (Lean Basics, level 10).
"

namespace LinearAlgebraGame

/-- $|\vec u\cdot\vec v| \le |\vec u|\,|\vec v|$. -/
Statement cauchy_schwarz {n : ℕ} (u v : Fin n → ℝ) : |u ⬝ᵥ v| ≤ len u * len v := by
  Hint "First prove the squared version $(\\vec u\\cdot\\vec v)^2 \\le (\\vec u\\cdot\\vec u)(\\vec v\\cdot\\vec v)$."
  Hint (hidden := true) "`have key : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by`"
  have key : (u ⬝ᵥ v) ^ 2 ≤ (u ⬝ᵥ u) * (v ⬝ᵥ v) := by
    Hint (hidden := true) "`have h := dot_self_nonneg ((v ⬝ᵥ v) • u - (u ⬝ᵥ v) • v)` and
    `rw [dot_expand] at h`."
    have h := dot_self_nonneg ((v ⬝ᵥ v) • u - (u ⬝ᵥ v) • v)
    rw [dot_expand] at h
    Hint (strict := true) "Two cases: $\\vec v\\cdot\\vec v = 0$ or $> 0$."
    Hint (strict := true) (hidden := true) "`rcases (dot_self_nonneg v).eq_or_lt with h0 | h0`"
    rcases (dot_self_nonneg v).eq_or_lt with h0 | h0
    · Hint (hidden := true) "`have hv : v = 0 := dotProduct_self_eq_zero.mp h0.symm`, then
      `rw [hv, dotProduct_zero, zero_dotProduct]` and `norm_num`."
      have hv : v = 0 := dotProduct_self_eq_zero.mp h0.symm
      rw [hv, dotProduct_zero, zero_dotProduct]
      norm_num
    · Hint (hidden := true) "`nlinarith` can divide `h` by the positive `v ⬝ᵥ v`."
      nlinarith
  Hint "Now take square roots."
  Hint (hidden := true) "`rw [len, len, ← Real.sqrt_mul (dot_self_nonneg u)]`, then
  `exact Real.abs_le_sqrt key`."
  rw [len, len, ← Real.sqrt_mul (dot_self_nonneg u)]
  exact Real.abs_le_sqrt key

end LinearAlgebraGame

Conclusion "Cauchy–Schwarz is now `cauchy_schwarz` in your inventory. It makes angles make sense: the cosine is between $-1$ and $1$."

NewTactic nlinarith
DisabledTheorem Finset.sum_mul_sq_le_sq_mul_sq Finset.inner_mul_le_norm_mul_norm
NewTheorem LinearAlgebraGame.dot_expand dotProduct_zero Real.sqrt_mul Real.abs_le_sqrt LE.le.eq_or_lt LinearAlgebraGame.dot_self_nonneg dotProduct_self_eq_zero zero_dotProduct
