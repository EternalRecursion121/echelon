import Game.Levels.FromScratch.L05_SubspaceBridge

World "FromScratch"
Level 6
Title "Bridge: span and independence"

Introduction "
Your `spanOf v` has the same members as Mathlib's `Submodule.span ℝ (Set.range v)`, and your
`LinIndep v` is Mathlib's `LinearIndependent ℝ v`. After this level you may freely move between
the game's definitions and Mathlib's.

When both sides of an `↔` become the same statement once definitions are unfolded, `rfl`
closes it.
"

namespace LinearAlgebraGame

/-- `spanOf v` has the members of Mathlib's span, and `LinIndep v` is Mathlib's
`LinearIndependent`. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) :
    (∀ x, x ∈ spanOf v ↔ x ∈ Submodule.span ℝ (Set.range v)) ∧
      (LinIndep v ↔ LinearIndependent ℝ v) := by
  constructor
  · Hint "Unfold both memberships into \"is a combination $\\sum_i c_i\\vec v_i$\"."
    intro x
    Hint (hidden := true) "`rw [mem_spanOf, Submodule.mem_span_range_iff_exists_fun]`"
    rw [mem_spanOf, Submodule.mem_span_range_iff_exists_fun]
  · Hint "Mathlib's `Fintype.linearIndependent_iff` turns the right side into exactly your
    definition."
    Hint (hidden := true) "`rw [Fintype.linearIndependent_iff]`, then `rfl`."
    rw [Fintype.linearIndependent_iff]
    rfl

end LinearAlgebraGame

Conclusion "
Everything Mathlib proves about `Submodule.span` and `LinearIndependent` now applies to your
own definitions, and vice versa.
"

TheoremTab "From Scratch"
