import Game.Levels.Subspaces.L05_ODE

World "Subspaces"
Level 6
Title "The span is the smallest subspace"

Introduction "
The *span* $[S]$ of $S = \\{\\vec v_0, \\ldots, \\vec v_{n-1}\\}$ is the set of all linear
combinations $c_0\\vec v_0 + \\cdots + c_{n-1}\\vec v_{n-1}$ (Definition Two.I.2.13). In Lean,
`Submodule.span ℝ (Set.range v)`, and `Submodule.mem_span_range_iff_exists_fun` says
exactly that its members are the combinations $\\sum_i c_i\\vec v_i$.

**Lemma Two.I.2.15.** $[S]$ is a subspace containing $S$, and it is the *smallest* one: it is
inside every subspace $W$ that contains $S$.

For subspaces, `U ≤ W` means $U \\subseteq W$: every vector of `U` is in `W`. So a goal
`U ≤ W` starts with `intro x hx` (`hx : x ∈ U`, goal `x ∈ W`).
"

namespace LinearAlgebraGame

/-- The span of $\vec v_0, \ldots, \vec v_{n-1}$ contains each $\vec v_i$ and lies inside every
subspace containing them all. -/
Statement span_smallest {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) :
    (∀ i, v i ∈ Submodule.span ℝ (Set.range v)) ∧
    ∀ W : Submodule ℝ V, (∀ i, v i ∈ W) → Submodule.span ℝ (Set.range v) ≤ W := by
  constructor
  · intro i
    Hint (hidden := true) "`apply Submodule.subset_span` then `exact Set.mem_range_self {i}`."
    apply Submodule.subset_span
    exact Set.mem_range_self i
  · intro W hW x hx
    Hint "A member of the span is a combination $\\sum_i c_i\\vec v_i$. Each term lies in
    `{W}`, so their sum does too."
    Hint (hidden := true) "`rw [Submodule.mem_span_range_iff_exists_fun] at {hx}` and
    `obtain ⟨c, rfl⟩ := {hx}`."
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, rfl⟩ := hx
    Hint (hidden := true) "`apply Submodule.sum_mem`, `intro i _`, `apply Submodule.smul_mem`."
    apply Submodule.sum_mem
    intro i _
    apply Submodule.smul_mem
    exact hW i

end LinearAlgebraGame

Conclusion "
In Mathlib this is `Submodule.span_le`: `span S ≤ W ↔ S ⊆ W`. It is now in your inventory.
"

DisabledTheorem Submodule.span_le
DisabledTactic simp
TheoremTab "Subspaces"

NewDefinition Submodule.span
NewTheorem Set.mem_range_self Submodule.sum_mem Submodule.add_mem Submodule.mem_span_range_iff_exists_fun Submodule.smul_mem Submodule.subset_span
