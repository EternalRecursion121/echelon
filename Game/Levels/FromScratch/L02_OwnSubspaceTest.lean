import Game.Levels.FromScratch.L01_PlaneAxioms

World "FromScratch"
Level 2
Title "Your own subspaces"

Introduction "
The game's `IsSubsp S` (see Definitions) says: $\\vec 0 \\in S$, and $S$ is closed under $+$
and under scalar multiplication. Prove Hefferon's subspace test (Lemma Two.I.2.9) for it, in
both directions. It is named `scratch_subspace_test`; level 5 reuses it.
"

namespace LinearAlgebraGame

/-- `IsSubsp S` iff $S$ is nonempty and closed under pairwise linear combinations. -/
Statement scratch_subspace_test {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) :
    IsSubsp S ↔
      S.Nonempty ∧ ∀ (c₁ c₂ : ℝ) (s₁ s₂ : V), s₁ ∈ S → s₂ ∈ S → c₁ • s₁ + c₂ • s₂ ∈ S := by
  constructor
  · intro h
    constructor
    · Hint (hidden := true) "`exact ⟨0, {h}.zero_mem⟩`"
      exact ⟨0, h.zero_mem⟩
    · intro c₁ c₂ s₁ s₂ h1 h2
      Hint (hidden := true) "`exact {h}.add_mem _ _ ({h}.smul_mem c₁ s₁ {h1}) ({h}.smul_mem c₂ s₂ {h2})`"
      exact h.add_mem _ _ (h.smul_mem c₁ s₁ h1) (h.smul_mem c₂ s₂ h2)
  · intro h
    obtain ⟨⟨s, hs⟩, hc⟩ := h
    Hint "As in the Subspaces world: special combinations with coefficients $0$ and $1$."
    constructor
    · have h0 := hc 0 0 s s hs hs
      rw [zero_smul, add_zero] at h0
      exact h0
    · intro x y hx hy
      have h1 := hc 1 1 x y hx hy
      rw [one_smul, one_smul] at h1
      exact h1
    · intro c x hx
      have h1 := hc c 0 x x hx hx
      rw [zero_smul, add_zero] at h1
      exact h1

end LinearAlgebraGame

Conclusion "Hefferon's two-condition test and the three-condition definition agree.
From now on this is `scratch_subspace_test`."

NewDefinition LinearAlgebraGame.IsSubsp

TheoremTab "From Scratch"
