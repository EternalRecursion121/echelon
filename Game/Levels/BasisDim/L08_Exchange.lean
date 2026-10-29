import Game.Levels.BasisDim.L07_ColSpace

World "BasisDim"
Level 8
Title "Boss: the exchange lemma"

Introduction "
**Lemma Two.III.2.2 (Exchange Lemma).** Let $B = \\langle\\vec\\beta_1, \\dots, \\vec\\beta_n\\rangle$
be a basis and $\\vec v = c_1\\vec\\beta_1 + \\dots + c_n\\vec\\beta_n$ with $c_i \\neq 0$. Then
exchanging $\\vec\\beta_i$ for $\\vec v$ gives another basis.

This is the engine behind *all bases have the same size* (Theorem 2.4): exchange the vectors
of one basis into the other, one at a time. Lean's dimension `Module.finrank` comes with that
theorem already proved (granted from Mathlib); this level shows the key step. We prove it for
three vectors
(exchanging $\\vec\\beta_1$), which has every idea of the general proof but none of the
index bookkeeping. Independence and spanning are written out explicitly:
- independent: the only relation $a\\vec\\beta_1 + b\\vec\\beta_2 + c\\vec\\beta_3 = \\vec 0$ is trivial;
- spanning: every $x$ is some $a\\vec\\beta_1 + b\\vec\\beta_2 + c\\vec\\beta_3$.

New: `field_simp` clears denominators (given the nonzero facts it needs), and `match_scalars` reduces an equation of vectors written as combinations to equations between their coefficients.
"

namespace LinearAlgebraGame

/-- If $\langle\beta_1,\beta_2,\beta_3\rangle$ is a basis and $v = c_1\beta_1 + c_2\beta_2 + c_3\beta_3$
with $c_1 \ne 0$, then $\langle v, \beta_2, \beta_3\rangle$ is a basis. -/
Statement exchange_three {V : Type*} [AddCommGroup V] [Module ℝ V] (β₁ β₂ β₃ v : V)
    (c₁ c₂ c₃ : ℝ)
    (hind : ∀ a b c : ℝ, a • β₁ + b • β₂ + c • β₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0)
    (hspan : ∀ x : V, ∃ a b c : ℝ, x = a • β₁ + b • β₂ + c • β₃)
    (hv : v = c₁ • β₁ + c₂ • β₂ + c₃ • β₃) (hc : c₁ ≠ 0) :
    (∀ a b c : ℝ, a • v + b • β₂ + c • β₃ = 0 → a = 0 ∧ b = 0 ∧ c = 0) ∧
    (∀ x : V, ∃ a b c : ℝ, x = a • v + b • β₂ + c • β₃) := by
  constructor
  · Hint "Independence. Substitute $v$: a relation among $v, \\beta_2, \\beta_3$ is a relation
    among $\\beta_1, \\beta_2, \\beta_3$ with coefficients $a c_1$, $a c_2 + b$, $a c_3 + c$."
    intro a b c h
    Hint (hidden := true) "`obtain ⟨h1, h2, h3⟩ := hind (a * c₁) (a * c₂ + b) (a * c₃ + c)
    (by rw [← {h}, hv]; module)`"
    obtain ⟨h1, h2, h3⟩ := hind (a * c₁) (a * c₂ + b) (a * c₃ + c) (by rw [← h, hv]; module)
    Hint "Now $a c_1 = 0$ and $c_1 \\neq 0$."
    have ha : a = 0 := (mul_eq_zero.mp h1).resolve_right hc
    rw [ha] at h2 h3
    refine ⟨ha, by linarith, by linarith⟩
  · Hint "Spanning. Since $c_1 \\ne 0$, solve for
    $\\beta_1$ in terms of $v, \\beta_2, \\beta_3$ (divide by $c_1$) and substitute into $x = a\\beta_1 + b\\beta_2 + c\\beta_3$."
    intro x
    obtain ⟨a, b, c, rfl⟩ := hspan x
    Hint (hidden := true) "`refine ⟨a / c₁, b - a * c₂ / c₁, c - a * c₃ / c₁, ?_⟩`"
    refine ⟨a / c₁, b - a * c₂ / c₁, c - a * c₃ / c₁, ?_⟩
    rw [hv]
    Hint (hidden := true) "Compare the coefficient of each vector with `match_scalars`, then
    `field_simp` and `ring`."
    match_scalars <;> field_simp <;> ring

end LinearAlgebraGame

Conclusion "
Repeating exchanges (Theorem 2.4) shows any two bases have the same number of elements, so
*dimension* is well defined. From now on Mathlib's `Module.finrank` is the dimension: the
number of vectors in any basis.
"

NewTactic field_simp match_scalars

TheoremTab "Dimension"
NewTheorem mul_eq_zero
