import Game.Levels.FromScratch.L04_OwnIndep

World "FromScratch"
Level 5
Title "Bridge: subspaces"

Introduction "
Mathlib's subspaces are `Submodule ℝ V`. Prove your `IsSubsp` describes exactly their carriers.

To build a `Submodule` with carrier `S`, write it out field by field as in Subspaces level 1:

`refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩`

(the last goal, \"its set is `S`\", is `rfl`). For the converse, your own subspace test
`scratch_subspace_test` (level 2) reduces `IsSubsp ↑W` to two checks.
"

namespace LinearAlgebraGame

/-- `IsSubsp S` iff `S` is the carrier of a Mathlib `Submodule`. -/
Statement scratch_subspace_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) :
    IsSubsp S ↔ ∃ W : Submodule ℝ V, (W : Set V) = S := by
  constructor
  · Hint "Build the `Submodule` with carrier `S`; each closure field comes from a field of
    `IsSubsp S`."
    intro h
    Hint (hidden := true) "`refine ⟨\{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩`"
    refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩
    · intro x y hx hy
      Hint (hidden := true) "`exact {h}.add_mem {x} {y} {hx} {hy}`"
      exact h.add_mem x y hx hy
    · exact h.zero_mem
    · intro c x hx
      exact h.smul_mem c x hx
    · rfl
  · Hint "Use your own subspace test: a `Submodule` is nonempty and closed under combinations."
    intro h
    Hint (hidden := true) "`obtain ⟨W, rfl⟩ := {h}` replaces `S` by `↑W`; then
    `rw [scratch_subspace_test]` and `constructor`."
    obtain ⟨W, rfl⟩ := h
    rw [scratch_subspace_test]
    constructor
    · Hint (hidden := true) "`exact ⟨0, W.zero_mem⟩`"
      exact ⟨0, W.zero_mem⟩
    · intro c₁ c₂ s₁ s₂ h1 h2
      Hint (hidden := true) "`exact W.add_mem (W.smul_mem c₁ {h1}) (W.smul_mem c₂ {h2})`"
      exact W.add_mem (W.smul_mem c₁ h1) (W.smul_mem c₂ h2)

end LinearAlgebraGame

Conclusion "Same concept, two packagings."

TheoremTab "From Scratch"
