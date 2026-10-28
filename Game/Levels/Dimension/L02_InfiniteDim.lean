import Game.Levels.Dimension.L01_Exchange

World "Dimension"
Level 2
Title "Infinite dimension breaks it"

-- @sheet 4 Q10c
/-! @answer
Take $W = \mathbb R[x]$ (all polynomials) and $U = x\cdot\mathbb R[x]$, the polynomials with
zero constant term. Then $U \subsetneq W$ ($1 \notin U$). But multiplication by $x$ is an
injective linear map $W \to U$ and onto $U$, so $U \cong W$: both have the countable basis
$\langle 1, x, x^2, \dots\rangle$ resp. $\langle x, x^2, x^3,\dots\rangle$ and the same
(infinite) dimension. So equal dimension does not force $U = W$. The proof of (b) breaks
because a basis of $U$ with "as many" elements as a basis of $W$ need not span $W$ — counting
only works for finite sets. (In Lean, `finrank` is 0 for infinite-dimensional spaces, so the
naive `finrank` statement would be true for the wrong reason; `Module.rank` is the honest
cardinal-valued dimension.)
-/
Introduction "
**Problem Sheet 4, Question 10(c).** Show that the prior item does not hold if $U$ and $W$
are infinite-dimensional.

An *explain level*. We use $W = \\mathbb R[x]$ (`Polynomial ℝ`) and
$U = $ the range of $p \\mapsto x\\cdot p$. Warning: `Module.finrank` is $0$ for every
infinite-dimensional space, so we measure with `Module.rank`, the cardinal-valued dimension.

Useful: `LinearMap.mulLeft ℝ Polynomial.X` is $p \\mapsto x p$; an injective linear map is
an isomorphism onto its range (`LinearEquiv.ofInjective`), and isomorphic spaces have equal
rank (`LinearEquiv.rank_eq`). `Polynomial.X_dvd_iff` says $x \\mid p$ iff $p(0) = 0$.

Also write, as a comment starting `-- Explain:`, why the argument of (b) fails here.
"

namespace LinearAlgebraGame

/-- There is a proper subspace $U \subsetneq \mathbb R[x]$ with
$\operatorname{rank} U = \operatorname{rank} \mathbb R[x]$. -/
Statement : ∃ U : Submodule ℝ (Polynomial ℝ),
    U ≠ ⊤ ∧ Module.rank ℝ U = Module.rank ℝ (Polynomial ℝ) := by
  Hint "Multiplication by $x$ is injective, so its range is a copy of $\\mathbb R[x]$ inside
  $\\mathbb R[x]$. But $1$ is not in the range."
  have hinj : Function.Injective (LinearMap.mulLeft ℝ (Polynomial.X : Polynomial ℝ)) := by
    intro p q h
    exact mul_left_cancel₀ Polynomial.X_ne_zero h
  Hint (hidden := true) "`refine ⟨LinearMap.range (LinearMap.mulLeft ℝ Polynomial.X), ?_,
  (LinearEquiv.ofInjective _ {hinj}).rank_eq.symm⟩`"
  refine ⟨LinearMap.range (LinearMap.mulLeft ℝ Polynomial.X), ?_,
    (LinearEquiv.ofInjective _ hinj).rank_eq.symm⟩
  intro htop
  Hint "If the range were everything, $1 = x\\cdot p$ for some $p$."
  obtain ⟨p, hp⟩ := (LinearMap.range_eq_top.mp htop) 1
  have hX : (Polynomial.X : Polynomial ℝ) ∣ 1 := ⟨p, hp.symm⟩
  rw [Polynomial.X_dvd_iff] at hX
  -- Explain: in (b) a basis of U with dim W elements is independent in W, hence spans W —
  -- that counting step needs finiteness. Here x·ℝ[x] ≅ ℝ[x] has the same (infinite)
  -- dimension, but 1 ∉ x·ℝ[x]. (finrank would say 0 = 0 for any two infinite-dim spaces.)
  Hint (hidden := true) "Model explanation: *the proof of (b) used that $\\dim W$ independent
  vectors in $W$ span $W$, a counting argument that only works for finite sets. Here
  $x\\mathbb R[x] \\cong \\mathbb R[x]$ have equal infinite dimension yet differ.* Close with
  `simp at {hX}`."
  simp at hX

end LinearAlgebraGame

Conclusion "
$x\\,\\mathbb R[x] \\subsetneq \\mathbb R[x]$, yet both have the same (countably infinite)
dimension.
"

TheoremTab "Dimension"
NewTheorem Polynomial.X_ne_zero LinearEquiv.ofInjective LinearEquiv.rank_eq Polynomial.X_dvd_iff LinearMap.range_eq_top
NewDefinition Polynomial LinearMap.mulLeft Module.rank LinearEquiv LinearEquiv.ofInjective LinearMap.range
