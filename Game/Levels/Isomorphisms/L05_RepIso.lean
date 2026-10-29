import Game.Levels.Isomorphisms.L04_BasisCorrespondence

World "Isomorphisms"
Level 5
Title "Every n-dimensional space is ℝⁿ"

Introduction "
Take the previous level's construction with $W = \\mathbb R^n$ and $D$ the standard basis:
$\\hat f$ sends $\\vec v$ to its coordinate vector. That map is $\\mathrm{Rep}_B$, and Lean
packages it, already proved to be an isomorphism, as `B.equivFun : V ≃ₗ[ℝ] (Fin n → ℝ)`.

Prove Hefferon Theorem Three.I.2.3 in the form: a finite-dimensional $V$ has dimension $n$
if and only if $V \\cong \\mathbb R^n$.

Useful: `Module.finBasisOfFinrankEq ℝ V h` is a basis of $V$ indexed by `Fin n` when
`h : finrank ℝ V = n`.
"

namespace LinearAlgebraGame

/-- $\dim V = n \iff V \cong \mathbb R^n$. -/
Statement finrank_eq_iff_iso_fin {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (n : ℕ) :
    Module.finrank ℝ V = n ↔ Nonempty (V ≃ₗ[ℝ] (Fin n → ℝ)) := by
  constructor
  · intro h
    Hint "Pick a basis $B$ of $V$ with $n$ vectors; then Rep_B (`B.equivFun`) is the isomorphism."
    Hint (hidden := true) "`exact ⟨(Module.finBasisOfFinrankEq ℝ V {h}).equivFun⟩`"
    exact ⟨(Module.finBasisOfFinrankEq ℝ V h).equivFun⟩
  · Hint "Isomorphisms preserve dimension, and $\\dim \\mathbb R^n = n$."
    rintro ⟨e⟩
    Hint (hidden := true) "`rw [{e}.finrank_eq, Module.finrank_fin_fun]`"
    rw [e.finrank_eq, Module.finrank_fin_fun]

end LinearAlgebraGame

Conclusion "
*Dimension characterises finite-dimensional spaces up to isomorphism.* Combined with Level 3:
two finite-dimensional spaces are isomorphic exactly when their dimensions agree.
"

NewDefinition Module.Basis.equivFun Module.finBasisOfFinrankEq
DisabledTheorem FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq FiniteDimensional.nonempty_linearEquiv_of_finrank_eq
DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTheorem LinearEquiv.finrank_eq
