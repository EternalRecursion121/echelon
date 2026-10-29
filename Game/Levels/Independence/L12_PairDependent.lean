import Game.Levels.Independence.L11_GaussSubset

World "Independence"
Level 12
Title "When are two vectors dependent?"

Introduction "
Corollary Two.II.1.19 (next level) for just two vectors: $\\vec u, \\vec v$ are dependent
exactly when $\\vec u = \\vec 0$ or $\\vec v$ is a multiple of $\\vec u$.

`Submodule.mem_span_singleton` says $\\vec v \\in [\\{\\vec u\\}]$ iff $\\vec v = a\\vec u$ for some
$a$, and `smul_eq_zero` says $a\\vec u = \\vec 0$ iff $a = 0$ or $\\vec u = \\vec 0$ (you proved the
key case in the Ten Conditions world).
"

namespace LinearAlgebraGame

/-- $\vec u, \vec v$ are dependent iff $\vec u = \vec 0$ or $\vec v \in [\{\vec u\}]$. -/
Statement pair_dependent_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (u v : V) :
    ¬ LinearIndependent ℝ ![u, v] ↔ u = 0 ∨ v ∈ Submodule.span ℝ {u} := by
  rw [LinearIndependent.pair_iff]
  constructor
  · intro h
    Hint "Contrapositive: if neither alternative holds, every relation $a\\vec u + b\\vec v =
    \\vec 0$ is trivial. Is $b = 0$? If not, solve for $\\vec v$."
    Hint (hidden := true) "`by_contra hcon`, `apply {h}`, `intro a b hab`, `by_cases hb : b = 0`."
    by_contra hcon
    apply h
    intro a b hab
    by_cases hb : b = 0
    · Hint (hidden := true) "`rw [{hb}, zero_smul, add_zero] at {hab}`, then
      `rcases smul_eq_zero.mp {hab} with ha | hu`."
      rw [hb, zero_smul, add_zero] at hab
      rcases smul_eq_zero.mp hab with ha | hu
      · exact ⟨ha, hb⟩
      · exfalso
        exact hcon (Or.inl hu)
    · exfalso
      apply hcon
      right
      rw [Submodule.mem_span_singleton]
      Hint (hidden := true) "`use -a / b`, then a `calc` as in the extension lemma:
      `(-a / b) • u = b⁻¹ • (-(a • u + b • v)) + b⁻¹ • (b • v) := by module`,
      `_ = v := by rw [{hab}, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ {hb}, one_smul]`."
      use -a / b
      calc (-a / b) • u = b⁻¹ • (-(a • u + b • v)) + b⁻¹ • (b • v) := by module
        _ = v := by
            rw [hab, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hb, one_smul]
  · Hint "Each alternative hands you a nontrivial relation."
    intro h hli
    rcases h with h | h
    · Hint (hidden := true) "`have h1 := {hli} 1 0 (by rw [{h}]; module)`, then `norm_num at h1`."
      have h1 := hli 1 0 (by rw [h]; module)
      norm_num at h1
    · rw [Submodule.mem_span_singleton] at h
      obtain ⟨a, ha⟩ := h
      Hint (hidden := true) "`have h1 := {hli} {a} (-1) (by rw [← {ha}]; module)`, then `norm_num at h1`."
      have h1 := hli a (-1) (by rw [← ha]; module)
      norm_num at h1

end LinearAlgebraGame

Conclusion "
Two vectors are dependent exactly when one of them is a multiple of the other (where
$\\vec 0 = 0\\cdot\\vec v$ counts as a multiple).
"

TheoremTab "Independence"
NewTheorem smul_eq_zero Submodule.mem_span_singleton
