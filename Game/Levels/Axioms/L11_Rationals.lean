import Game.Levels.Axioms.L10_ZeroSum

World "Axioms"
Level 11
Title "The rationals over the reals"

-- @sheet 4 Q1
/-! @answer
**No.** Real scalar multiplication does not stay inside $\mathbb{Q}$: $\sqrt 2 \in \mathbb{R}$
and $1 \in \mathbb{Q}$, but $\sqrt 2 \cdot 1 = \sqrt 2 \notin \mathbb{Q}$, so the closure
condition (6) fails. (In fact no real vector space structure on $\mathbb{Q}$ exists at all:
by Sheet 3 Q3(c), $r \mapsto r\cdot 1$ would inject the uncountable $\mathbb{R}$ into the
countable $\mathbb{Q}$.)
-/
Introduction "
**Problem Sheet 4, Question 1.** Is the set of rational numbers a vector space over
$\\mathbb{R}$ under the usual addition and scalar multiplication operations?

To be a vector space, $\\mathbb{Q}$ would need a scalar multiplication
`smul : ℝ → ℚ → ℚ` that agrees with the usual product, i.e. `smul r q` equals $rq$
(read as a real number), and that satisfies the ten conditions.

Decide: `left` for \"no\", `right` for \"yes\".
"

namespace LinearAlgebraGame

/-- Is $\mathbb{Q}$, with the usual operations, a real vector space? -/
Statement : (¬ ∃ smul : ℝ → ℚ → ℚ, (∀ r q, (smul r q : ℝ) = r * q) ∧
      VectorSpaceAxioms ℚ (· + ·) smul) ∨
    (∃ smul : ℝ → ℚ → ℚ, (∀ r q, (smul r q : ℝ) = r * q) ∧ VectorSpaceAxioms ℚ (· + ·) smul) := by
  Hint "Is $\\mathbb\{Q}$ closed under multiplication by *real* scalars? Try $\\sqrt 2 \\cdot 1$."
  left
  intro h
  obtain ⟨smul, hs, hV⟩ := h
  Hint (hidden := true) "`have h1 := {hs} (Real.sqrt 2) 1`, then
  `rw [Rat.cast_one, mul_one] at h1`."
  have h1 := hs (Real.sqrt 2) 1
  rw [Rat.cast_one, mul_one] at h1
  Hint (hidden := true) "Now √2 equals a rational number. `irrational_sqrt_two.ne_rat` says it
  doesn't: `exact irrational_sqrt_two.ne_rat _ h1.symm`."
  exact irrational_sqrt_two.ne_rat _ h1.symm

end LinearAlgebraGame

Conclusion "
**Answer: no** — $\\sqrt2 \\cdot 1 \\notin \\mathbb{Q}$, so closure under scalar
multiplication fails.
"

NewTheorem Rat.cast_one irrational_sqrt_two Irrational.ne_rat
TheoremTab "Vector spaces"
