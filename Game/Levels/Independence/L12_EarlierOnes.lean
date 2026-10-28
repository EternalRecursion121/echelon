import Game.Levels.Independence.L11_SubsetIndep

World "Independence"
Level 12
Title "Blame an earlier vector (boss)"

Introduction "
**Corollary Two.II.1.19.** $\\{\\vec s_1, \\ldots, \\vec s_n\\}$ is linearly dependent if and
only if some $\\vec s_i$ is a linear combination of $\\vec s_1, \\ldots, \\vec s_{i-1}$
(for $i = 1$ that means $\\vec s_1 = \\vec 0$, the empty combination).

Prove it for three vectors. `Submodule.mem_span_singleton` says $\\vec v \\in [\\{\\vec u\\}]$
iff $\\vec v = a\\vec u$ for some $a$, and `smul_eq_zero` says $a\\vec u = \\vec 0$ iff $a = 0$ or
$\\vec u = \\vec 0$ (you proved this in the Ten Conditions world).
"

namespace LinearAlgebraGame

/-- $\vec u, \vec v, \vec w$ are dependent iff $\vec u = \vec 0$, or $\vec v \in [\{\vec u\}]$, or
$\vec w \in [\{\vec u, \vec v\}]$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V) :
    ¬ LinearIndependent ℝ ![u, v, w] ↔
      u = 0 ∨ v ∈ Submodule.span ℝ {u} ∨ w ∈ Submodule.span ℝ {u, v} := by
  rw [linIndep_three_iff]
  constructor
  · intro hdep
    Hint "Contrapositive: if none of the three alternatives holds, every relation
    $a\\vec u + b\\vec v + c\\vec w = \\vec 0$ is trivial. Show $c = 0$ first (else $\\vec w$ is
    a combination of $\\vec u, \\vec v$), then $b = 0$, then $a = 0$."
    Hint (hidden := true) "`by_contra hcon`, `apply {hdep}`, `intro a b c hrel`."
    by_contra hcon
    apply hdep
    intro a b c hrel
    Hint (hidden := true) "`have hc : c = 0 := by by_contra hc; apply {hcon}; right; right; …` —
    as in the extension lemma."
    have hc : c = 0 := by
      by_contra hc
      apply hcon
      right
      right
      rw [Submodule.mem_span_pair]
      use -a / c, -b / c
      calc (-a / c) • u + (-b / c) • v = c⁻¹ • (-(a • u + b • v + c • w)) + c⁻¹ • (c • w) := by
            module
        _ = w := by
            rw [hrel, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [hc, zero_smul, add_zero] at hrel
    have hb : b = 0 := by
      by_contra hb
      apply hcon
      right
      left
      rw [Submodule.mem_span_singleton]
      use -a / b
      calc (-a / b) • u = b⁻¹ • (-(a • u + b • v)) + b⁻¹ • (b • v) := by module
        _ = v := by
            rw [hrel, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hb, one_smul]
    rw [hb, zero_smul, add_zero] at hrel
    Hint (hidden := true) "`rcases smul_eq_zero.mp {hrel} with ha | hu`"
    rcases smul_eq_zero.mp hrel with ha | hu
    · exact ⟨ha, hb, hc⟩
    · exfalso
      apply hcon
      left
      exact hu
  · Hint "Each alternative hands you a nontrivial relation."
    intro h hli
    rcases h with h | h | h
    · Hint (hidden := true) "`have h1 := {hli} 1 0 0 (by rw [{h}]; module)`, `norm_num at h1`."
      have h1 := hli 1 0 0 (by rw [h]; module)
      norm_num at h1
    · rw [Submodule.mem_span_singleton] at h
      obtain ⟨a, ha⟩ := h
      have h1 := hli a (-1) 0 (by rw [← ha]; module)
      norm_num at h1
    · rw [Submodule.mem_span_pair] at h
      obtain ⟨a, b, hab⟩ := h
      have h1 := hli a b (-1) (by rw [← hab]; module)
      norm_num at h1

end LinearAlgebraGame

Conclusion "
Read left to right, this is an algorithm: walk along the list and throw away any vector that
lies in the span of the ones kept so far.
"

TheoremTab "Independence"
NewTheorem smul_eq_zero Submodule.mem_span_singleton
