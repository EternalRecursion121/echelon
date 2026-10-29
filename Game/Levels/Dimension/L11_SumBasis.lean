import Game.Levels.Dimension.L10_Sum

World "Dimension"
Level 11
Title "Boss: a basis for U + W"

-- @sheet 6 Q1b
/-! @answer
*Spanning:* $U + W$ is spanned by a basis of $U$ together with a basis of $W$, i.e. by
$\vec\mu$'s, $\vec\beta$'s and $\vec\omega$'s (the $\vec\beta$'s twice).
*Independence:* suppose $\sum a_i\vec\mu_i + \sum b_i\vec\beta_i + \sum c_i\vec\omega_i = \vec 0$.
Then $\vec x = \sum c_i\vec\omega_i \in W$, and $\vec x = -(\sum a_i\vec\mu_i + \sum
b_i\vec\beta_i) \in U$, so $\vec x \in U\cap W$, hence $\vec x = \sum d_i\vec\beta_i$. Then
$\sum d_i\vec\beta_i - \sum c_i\vec\omega_i = \vec 0$ is a relation in the basis of $W$, so
all $c_i = 0$. The original relation becomes $\sum a_i\vec\mu_i + \sum b_i\vec\beta_i = \vec 0$, a
relation in the basis of $U$, so all $a_i, b_i = 0$.
-/
Introduction "
**Problem Sheet 6, Question 1(b).** Suppose that $U$ and $W$ are subspaces of a vector space.
Suppose that the sequence $\\langle\\vec\\beta_1, \\dots, \\vec\\beta_k\\rangle$ is a basis for
$U \\cap W$. Finally, suppose that the prior sequence has been expanded to give a sequence
$\\langle\\vec\\mu_1, \\dots, \\vec\\mu_j, \\vec\\beta_1, \\dots, \\vec\\beta_k\\rangle$ that is a basis for
$U$, and a sequence $\\langle\\vec\\beta_1, \\dots, \\vec\\beta_k, \\vec\\omega_1, \\dots, \\vec\\omega_p\\rangle$
that is a basis for $W$. Prove that this sequence
$\\langle\\vec\\mu_1, \\dots, \\vec\\mu_j, \\vec\\beta_1, \\dots, \\vec\\beta_k, \\vec\\omega_1, \\dots,
\\vec\\omega_p\\rangle$ is a basis for the sum $U + W$.

Concatenation of sequences is `Sum.elim`. The index bookkeeping is granted:
- `linearIndependent_sum_elim_iff` and `linearIndependent_sum_elim₃_iff` write out
  independence of a concatenation as \"only the trivial relation\";
- `span_range_sum_elim`: the span of a concatenation is the sum of the spans.
"

namespace LinearAlgebraGame

/-- The concatenation $\langle \mu, \beta, \omega\rangle$ is a basis of $U + W$. -/
Statement sum_basis {V : Type*} [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V)
    {j k p : ℕ} (β : Fin k → V) (μ : Fin j → V) (ω : Fin p → V)
    (hβ : IsBasisOf β (U ⊓ W)) (hU : IsBasisOf (Sum.elim μ β) U)
    (hW : IsBasisOf (Sum.elim β ω) W) :
    IsBasisOf (Sum.elim (Sum.elim μ β) ω) (U ⊔ W) := by
  Hint "Unpack the three bases and write their spans and independence out with the granted
  lemmas."
  obtain ⟨hβi, hβs⟩ := hβ
  obtain ⟨hUi, hUs⟩ := hU
  obtain ⟨hWi, hWs⟩ := hW
  rw [span_range_sum_elim] at hUs hWs
  rw [linearIndependent_sum_elim_iff] at hUi hWi
  constructor
  · rw [linearIndependent_sum_elim₃_iff]
    intro a b c h
    Hint "The key vector is $x = \\sum c_l \\omega_l$. Show it lies in $U \\cap W$."
    have hx : ∑ l, c l • ω l ∈ U ⊓ W := by
      constructor
      · Hint "In $U$: it is minus the rest of the relation."
        have : ∑ l, c l • ω l = -(∑ i, a i • μ i + ∑ i, b i • β i) :=
          eq_neg_of_add_eq_zero_right h
        rw [this, ← hUs]
        apply Submodule.neg_mem
        Hint (hidden := true) "`exact Submodule.add_mem_sup ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a, rfl⟩) ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨b, rfl⟩)`"
        exact Submodule.add_mem_sup ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨a, rfl⟩)
          ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨b, rfl⟩)
      · rw [← hWs]
        exact Submodule.mem_sup_right ((Submodule.mem_span_range_iff_exists_fun ℝ).mpr ⟨c, rfl⟩)
    Hint "So $x = \\sum d_i\\beta_i$ for some $d$."
    rw [← hβs, Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨d, hd⟩ := hx
    Hint "Then $\\sum d_i\\beta_i + \\sum (-c_l)\\omega_l = 0$ is a relation in the basis of $W$."
    Hint (hidden := true) "`obtain ⟨-, hc⟩ := hWi d (-c) (by simp [{hd}])`: `simp` knows
    `neg_smul` and `Finset.sum_neg_distrib`, and `{hd}` cancels the two sums."
    obtain ⟨-, hc⟩ := hWi d (-c) (by simp [hd])
    have hc0 : c = 0 := neg_eq_zero.mp hc
    Hint "With $c = 0$ the original relation is a relation in the basis of $U$."
    Hint (hidden := true) "`rw [{hc0}] at {h}` and `simp at {h}` remove the zero terms."
    rw [hc0] at h
    simp at h
    obtain ⟨ha, hb⟩ := hUi a b h
    exact ⟨ha, hb, hc0⟩
  · Hint "Spanning: both sides are sums of the spans of the $\\mu$'s, $\\beta$'s and
    $\\omega$'s; only the bracketing (and a repeated $\\beta$-span) differ."
    rw [span_range_sum_elim, span_range_sum_elim, ← hUs, ← hWs]
    Hint (hidden := true) "`rw [sup_assoc, sup_assoc, ← sup_assoc (Submodule.span ℝ (Set.range β)), sup_idem]`"
    rw [sup_assoc, sup_assoc, ← sup_assoc (Submodule.span ℝ (Set.range β)), sup_idem]

end LinearAlgebraGame

Conclusion "
The union of the two extended bases, with the shared part counted once, is a basis of $U+W$.
"

NewTheorem LinearAlgebraGame.linearIndependent_sum_elim_iff LinearAlgebraGame.linearIndependent_sum_elim₃_iff LinearAlgebraGame.span_range_sum_elim eq_neg_of_add_eq_zero_right neg_eq_zero sup_assoc sup_idem
TheoremTab "Sums"
