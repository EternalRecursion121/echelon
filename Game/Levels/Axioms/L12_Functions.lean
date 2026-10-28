import Game.Levels.Axioms.L11_Rationals

World "Axioms"
Level 12
Title "Functions are vectors"

Introduction "
The functions $f : \\mathbb{R} \\to \\mathbb{R}$ form a vector space under the *pointwise*
operations: $(f + g)(x) = f(x) + g(x)$ and $(r\\cdot f)(x) = r\\cdot f(x)$. Lean already knows
this (it is a `Module ℝ (ℝ → ℝ)`), and the next world uses it constantly. The rewrite rules
are `Pi.add_apply` and `Pi.smul_apply`; `smul_eq_mul` turns `•` between two reals into `*`.
"

namespace LinearAlgebraGame

/-- $(r\cdot(f + g))(x) = r f(x) + r g(x)$. -/
Statement (f g : ℝ → ℝ) (r x : ℝ) : (r • (f + g)) x = r * f x + r * g x := by
  Hint "Unfold the operations one at a time, from the outside in."
  Hint (hidden := true) "`rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]`"
  rw [Pi.smul_apply, Pi.add_apply, smul_eq_mul, mul_add]

end LinearAlgebraGame

Conclusion "
Every function-space identity reduces, point by point, to an identity of real numbers.
"

NewTheorem Pi.zero_apply Pi.neg_apply mul_add
DisabledTactic simp
TheoremTab "Vector spaces"
