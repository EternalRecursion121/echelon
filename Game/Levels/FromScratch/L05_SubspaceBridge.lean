import Game.Levels.FromScratch.L04_OwnIndep

World "FromScratch"
Level 5
Title "Bridge: subspaces"

Introduction "
Mathlib's subspaces are `Submodule ℝ V`. Prove your `IsSubsp` describes exactly their carriers.
"

namespace LinearAlgebraGame

/-- `IsSubsp S` iff `S` is the carrier of a Mathlib `Submodule`. -/
Statement scratch_subspace_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) :
    IsSubsp S ↔ ∃ W : Submodule ℝ V, (W : Set V) = S := by
  constructor
  · intro h
    Hint (hidden := true) "`refine ⟨\{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩`"
    refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, rfl⟩
    · intro x y hx hy
      exact h.add_mem x y hx hy
    · exact h.zero_mem
    · intro c x hx
      exact h.smul_mem c x hx
  · intro h
    obtain ⟨W, rfl⟩ := h
    constructor
    · exact W.zero_mem
    · intro x y hx hy
      exact W.add_mem hx hy
    · intro c x hx
      exact W.smul_mem c hx

end LinearAlgebraGame

Conclusion "Same concept, two packagings."

TheoremTab "From Scratch"
