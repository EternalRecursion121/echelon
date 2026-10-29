import Game.Levels.Independence.L08_SpanInsert

World "Independence"
Level 9
Title "The extension lemma"

Introduction "
**Lemma Two.II.1.15.** Suppose $S$ is linearly independent and $\\vec v \\notin S$. Then
$S \\cup \\{\\vec v\\}$ is linearly independent if and only if $\\vec v \\notin [S]$.

Prove it for $S = \\{\\vec u, \\vec w\\}$. `Submodule.mem_span_pair` says
$\\vec x \\in [\\{\\vec u, \\vec w\\}]$ iff $\\vec x = a\\vec u + b\\vec w$ for some $a, b$.

**New:** `exfalso` replaces the goal by `False` (to prove anything from a contradiction).
"

namespace LinearAlgebraGame

/-- If $\vec u, \vec w$ are independent, then $\vec u, \vec w, \vec x$ are independent iff
$\vec x \notin [\{\vec u, \vec w\}]$. -/
Statement extension_lemma {V : Type*} [AddCommGroup V] [Module ℝ V] (u w x : V)
    (hli : LinearIndependent ℝ ![u, w]) :
    LinearIndependent ℝ ![u, w, x] ↔ x ∉ Submodule.span ℝ {u, w} := by
  rw [LinearIndependent.pair_iff] at hli
  rw [linIndep_three_iff]
  constructor
  · Hint "If $\\vec x = a\\vec u + b\\vec w$ then $a\\vec u + b\\vec w + (-1)\\vec x = \\vec 0$ is a
    nontrivial relation."
    intro h hx
    rw [Submodule.mem_span_pair] at hx
    obtain ⟨a, b, hab⟩ := hx
    Hint (hidden := true) "`have h1 := {h} a b (-1) (by rw [← {hab}]; module)` then `norm_num at h1`."
    have h1 := h a b (-1) (by rw [← hab]; module)
    norm_num at h1
  · intro hx a b c hrel
    Hint "Is $c = 0$? If so, the relation is one between $\\vec u$ and $\\vec w$ alone. If
    not, you can solve for $\\vec x$."
    Hint (hidden := true) "`by_cases hc : c = 0`"
    by_cases hc : c = 0
    · rw [hc, zero_smul, add_zero] at hrel
      obtain ⟨ha, hb⟩ := hli a b hrel
      exact ⟨ha, hb, hc⟩
    · exfalso
      apply hx
      rw [Submodule.mem_span_pair]
      Hint (hidden := true) "`use -a / c, -b / c`, then a `calc`:
      `(-a / c) • u + (-b / c) • w = c⁻¹ • (-(a • u + b • w + c • x)) + c⁻¹ • (c • x) := by module`,
      `_ = x := by rw [{hrel}, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ {hc}, one_smul]`."
      use -a / c, -b / c
      calc (-a / c) • u + (-b / c) • w = c⁻¹ • (-(a • u + b • w + c • x)) + c⁻¹ • (c • x) := by
            module
        _ = x := by
            rw [hrel, neg_zero, smul_zero, zero_add, smul_smul, inv_mul_cancel₀ hc, one_smul]

end LinearAlgebraGame

Conclusion "
Example (Hefferon): $\\{1 - x, 1 + x\\} \\cup \\{2 + 2x\\}$ is dependent, but
$\\{1 - x, 1 + x\\} \\cup \\{2 + x^2\\}$ is independent.
"

TheoremTab "Independence"
NewTheorem Submodule.mem_span_pair
NewTactic exfalso
