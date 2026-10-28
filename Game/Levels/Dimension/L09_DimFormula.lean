import Game.Levels.Dimension.L08_SumBasis

World "Dimension"
Level 9
Title "The dimension formula"

-- @sheet 6 Q1c
/-! @answer
With the bases of (b): $\dim(U\cap W) = k$, $\dim U = j + k$, $\dim W = k + p$, and by (b)
$\dim(U + W) = j + k + p$. So
$\dim(U+W) = j + k + p = (j + k) + (k + p) - k = \dim U + \dim W - \dim(U\cap W)$.
(Such bases always exist in finite dimensions: start from a basis of $U\cap W$ and extend it
to bases of $U$ and of $W$, Corollary Two.III.2.12.)
-/
Introduction "
**Problem Sheet 6, Question 1(c).** Conclude that
$\\dim(U + W) = \\dim(U) + \\dim(W) - \\dim(U \\cap W)$.

We keep the setting of (b): the bases are given (in finite dimensions they always exist, by
extending a basis of $U\\cap W$ — Corollary 2.12). `IsBasisOf.finrank_eq` counts a basis:
the number of indices of `Fin j ⊕ Fin k` is `j + k` (`Fintype.card_sum`, `Fintype.card_fin`).
"

namespace LinearAlgebraGame

/-- $\dim(U+W) = \dim U + \dim W - \dim(U\cap W)$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V)
    {j k p : ℕ} (β : Fin k → V) (μ : Fin j → V) (ω : Fin p → V)
    (hβ : IsBasisOf β (U ⊓ W)) (hU : IsBasisOf (Sum.elim μ β) U)
    (hW : IsBasisOf (Sum.elim β ω) W) :
    Module.finrank ℝ ↥(U ⊔ W) =
      Module.finrank ℝ U + Module.finrank ℝ W - Module.finrank ℝ ↥(U ⊓ W) := by
  Hint "Count every basis, using (b) for $U + W$."
  Hint (hidden := true) "`rw [(sum_basis U W β μ ω hβ hU hW).finrank_eq, hU.finrank_eq,
  hW.finrank_eq, hβ.finrank_eq]`"
  rw [(sum_basis U W β μ ω hβ hU hW).finrank_eq, hU.finrank_eq, hW.finrank_eq, hβ.finrank_eq]
  Hint (hidden := true) "`simp only [Fintype.card_sum, Fintype.card_fin]` then `omega`."
  simp only [Fintype.card_sum, Fintype.card_fin]
  omega

end LinearAlgebraGame

Conclusion "
**The dimension formula**: $\\dim(U+W) = \\dim U + \\dim W - \\dim(U\\cap W)$. Mathlib's
`Submodule.finrank_sup_add_finrank_inf_eq` is now fully earned.
"

DisabledTheorem Submodule.finrank_sup_add_finrank_inf_eq
TheoremTab "Sums"
NewTheorem LinearAlgebraGame.sum_basis Fintype.card_sum Fintype.card_fin
