import Game.Levels.Axioms.L08_RealsAxioms

World "Axioms"
Level 9
Title "Positive quadratics"

-- @sheet 3 Q1
/-! @answer
$P$ is not a vector space: it has no zero vector. The zero polynomial is not in $P$ since its
coefficients are $0 \notin \mathbb{R}^+$. More directly, suppose $z \in P$ satisfied
$p + z = p$ for all $p \in P$. Taking $p = z$ gives $z + z = z$, so the constant coefficient
satisfies $2a_0 = a_0$, i.e. $a_0 = 0$, contradicting $a_0 > 0$. (Also, $P$ is not closed
under scalar multiplication: $(-1)\cdot(1 + x + x^2) \notin P$.)
-/
Introduction "
**Problem Sheet 3, Question 1.** Show that, under the usual polynomial operations, the set
$$P := \\{a_0 + a_1x + a_2x^2 \\mid a_0, a_1, a_2 \\in \\mathbb{R}^+\\}$$
(where $\\mathbb{R}^+$ is the set of reals greater than zero) is not a vector space.

In Lean, $P$ is `PosQuad` (see Definitions) with the usual addition `PosQuad.add`.
The usual scalar multiplication is not even an operation $\\mathbb{R} \\times P \\to P$
(think of $r = -1$), so we prove something stronger: **no** scalar multiplication
whatsoever makes $P$, with the usual addition, satisfy the ten conditions.

This is a *decide* level: `left` claims \"not a vector space\", `right` claims \"vector space\".
"

namespace LinearAlgebraGame

/-- Is there a scalar multiplication making $P$ (with the usual $+$) a vector space? -/
Statement : (¬ ∃ smul : ℝ → PosQuad → PosQuad, VectorSpaceAxioms PosQuad PosQuad.add smul) ∨
    (∃ smul : ℝ → PosQuad → PosQuad, VectorSpaceAxioms PosQuad PosQuad.add smul) := by
  Hint "Which of the ten conditions could fail no matter how scalars act? Think about the
  zero vector."
  left
  intro h
  obtain ⟨smul, hV⟩ := h
  Hint (hidden := true) "`obtain ⟨z, hz⟩ := {hV}.has_zero` gives the would-be zero vector."
  obtain ⟨z, hz⟩ := hV.has_zero
  Hint "What does `{hz}` say about $z + z$? Compare constant coefficients."
  Hint (hidden := true) "Feed `{z}` to `{hz}` itself: $z + z = z$. Now look at the constant coefficient."
  Hint (hidden := true) "`have h1 := congrArg PosQuad.a₀ ({hz} {z})`, then
  `rw [PosQuad.add_a₀] at h1`."
  have h1 := congrArg PosQuad.a₀ (hz z)
  rw [PosQuad.add_a₀] at h1
  Hint (hidden := true) "`{z}.pos₀` says the constant coefficient is positive: `linarith [{z}.pos₀]`."
  linarith [z.pos₀]

end LinearAlgebraGame

Conclusion "
**Answer: not a vector space.** A zero vector $z$ would satisfy $z + z = z$, forcing its
coefficients to be $0 \\notin \\mathbb{R}^+$.
"

NewDefinition LinearAlgebraGame.PosQuad
NewTheorem LinearAlgebraGame.PosQuad.add_a₀
TheoremTab "Vector spaces"
