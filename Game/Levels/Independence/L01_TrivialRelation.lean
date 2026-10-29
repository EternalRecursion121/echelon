import Game.Metadata
import Game.Ch2a

World "Independence"
Level 1
Title "Only the trivial relation"

Introduction "
Hefferon's Definition Two.II.1.4: a set is *linearly independent* if none of its members is
a linear combination of the others. **Lemma 1.5** gives the practical test: $S$ is
independent if and only if the only linear relationship
$c_0\\vec s_0 + \\cdots + c_n\\vec s_n = \\vec 0$ among distinct members is the trivial one,
$c_0 = \\cdots = c_n = 0$.

Why? If a relation has a nonzero coefficient, that vector can be *isolated*: it is a
combination of the others. Prove this for three vectors.

New tactic: `module` proves identities in a vector space that follow from the axioms alone
(like `ring` for numbers), e.g. `a • u + b • v - b • v = a • u`.
"

namespace LinearAlgebraGame

/-- If $a\vec u + b\vec v + c\vec w = \vec 0$ with $a \neq 0$, then
$\vec u = -\frac ba\vec v - \frac ca\vec w$. -/
Statement isolate_of_relation {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V)
    (a b c : ℝ) (h : a • u + b • v + c • w = 0) (ha : a ≠ 0) :
    u = (-b / a) • v + (-c / a) • w := by
  Hint "Multiply the relation by $a^\{-1}$. A `calc` chain works well:
  $u = a^\{-1}(a u) = a^\{-1}(a u + b v + c w - b v - c w) = \\ldots$"
  Hint (hidden := true) "`calc u = a⁻¹ • (a • u) := by rw [smul_smul, inv_mul_cancel₀ {ha}, one_smul]`
  then `_ = a⁻¹ • (a • u + b • v + c • w - b • v - c • w) := by module`
  then `_ = (-b / a) • v + (-c / a) • w := by rw [{h}]; module`."
  calc u = a⁻¹ • (a • u) := by rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
    _ = a⁻¹ • (a • u + b • v + c • w - b • v - c • w) := by module
    _ = (-b / a) • v + (-c / a) • w := by rw [h]; module

end LinearAlgebraGame

Conclusion "
So \"some nontrivial relation\" and \"some vector is a combination of the others\" are the
same thing. Next level: how Lean states independence.
"

DisabledTactic field_simp
TheoremTab "Independence"

NewTactic «module»
