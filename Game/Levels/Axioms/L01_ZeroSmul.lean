import Game.Metadata
import Game.Ch2a

World "Axioms"
Level 1
Title "Zero times anything"

Introduction "
A vector space is a set $V$ with $+$ and $\\cdot$ satisfying Hefferon's ten conditions
(Definition Two.I.1.1). Your inventory holds just the conditions this proof needs, plus one cancellation law. There is no automation.

Our first theorem is Lemma Two.I.1.16 (1): $0 \\cdot \\vec v = \\vec 0$.
It is *not* one of the axioms; we must earn it.
"

namespace LinearAlgebraGame

/-- For every vector $\vec v$, $0 \cdot \vec v = \vec 0$. -/
Statement zero_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (0 : ℝ) • v = 0 := by
  Hint "Idea: $0 = 0 + 0$. What does that say about $0 \\cdot v$?"
  Hint (hidden := true) "So $0 \\cdot v + 0 \\cdot v = 0 \\cdot v + \\vec 0$. State that with `have`, then cancel."
  Hint (hidden := true) "`have h : (0:ℝ) • {v} + (0:ℝ) • {v} = (0:ℝ) • {v} + 0`"
  have h : (0:ℝ) • v + (0:ℝ) • v = (0:ℝ) • v + 0 := by
    Hint (hidden := true) "Rewrite the left side with `← add_smul`, then `add_zero` twice."
    rw [← add_smul, add_zero, add_zero]
  Hint (hidden := true) "Cancel $0 \\cdot v$ on the left of both sides of `{h}`."
  exact add_left_cancel h

end LinearAlgebraGame

Conclusion "
That is exactly the textbook proof, line for line. From now on `zero_smul_eq_zero` is in
your inventory.
"

DisabledTactic norm_num simp
DisabledTheorem zero_smul
TheoremTab "Vector spaces"
NewTheorem add_left_cancel add_smul add_zero
