import Game.Levels.FromScratch.L05_SubspaceBridge

World "FromScratch"
Level 6
Title "Bridge: span and independence (boss)"

Introduction "
Finally, your `spanOf` is Mathlib's `Submodule.span ℝ (Set.range v)` (as a set), and your
`LinIndep` is Mathlib's `LinearIndependent ℝ v`. After this level you may freely move between
the game's definitions and Mathlib's.
"

namespace LinearAlgebraGame

/-- `spanOf v` is Mathlib's span, and `LinIndep v` is Mathlib's `LinearIndependent`. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) :
    spanOf v = Submodule.span ℝ (Set.range v) ∧ (LinIndep v ↔ LinearIndependent ℝ v) := by
  constructor
  · Hint "Sets are equal when they have the same members: `ext x`. Then unfold both
    memberships."
    ext x
    Hint (hidden := true) "`rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, mem_spanOf]`"
    rw [SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun, mem_spanOf]
  · Hint "Mathlib's `Fintype.linearIndependent_iff` turns the right side into exactly your
    definition."
    Hint (hidden := true) "`unfold LinIndep`, then `rw [Fintype.linearIndependent_iff]`."
    unfold LinIndep
    rw [Fintype.linearIndependent_iff]

end LinearAlgebraGame

Conclusion "
Everything Mathlib proves about `Submodule.span` and `LinearIndependent` now applies to your
own definitions, and vice versa.
"

TheoremTab "From Scratch"
