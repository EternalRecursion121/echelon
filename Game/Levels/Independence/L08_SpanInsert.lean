import Game.Levels.Independence.L07_Triangular

World "Independence"
Level 8
Title "Adding a vector to a spanning set"

Introduction "
**Lemma Two.II.1.2.** For any $\\vec v$ and set $S$:
$[S \\cup \\{\\vec v\\}] = [S]$ if and only if $\\vec v \\in [S]$.

In Lean, $S \\cup \\{\\vec v\\}$ is `insert v S`. Mathlib's `Submodule.span_le`
(`span S ≤ W ↔ S ⊆ W`, which you proved as \"the span is the smallest subspace\") is now in
your inventory, along with `Submodule.span_mono` (`S ⊆ T → span S ≤ span T`).
"

namespace LinearAlgebraGame

/-- $\vec v \in [S]$ if and only if $[S \cup \{\vec v\}] = [S]$. -/
Statement span_insert_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) (v : V) :
    v ∈ Submodule.span ℝ S ↔ Submodule.span ℝ (insert v S) = Submodule.span ℝ S := by
  constructor
  · intro hv
    Hint "Two subspaces are equal when each is inside the other: `apply le_antisymm`."
    apply le_antisymm
    · Hint "It suffices that $S \\cup \\\{\\vec v\\} \\subseteq [S]$."
      Hint (hidden := true) "`rw [Submodule.span_le]`, `intro x hx`, then
      `rcases hx with rfl | hx`."
      rw [Submodule.span_le]
      intro x hx
      rcases hx with rfl | hx
      · exact hv
      · exact Submodule.subset_span hx
    · Hint (hidden := true) "`exact Submodule.span_mono (Set.subset_insert v S)`"
      exact Submodule.span_mono (Set.subset_insert v S)
  · intro h
    Hint "$\\vec v$ is certainly in $[S \\cup \\\{\\vec v\\}]$."
    Hint (hidden := true) "`rw [← {h}]`, then
    `exact Submodule.subset_span (Set.mem_insert v S)`."
    rw [← h]
    exact Submodule.subset_span (Set.mem_insert v S)

end LinearAlgebraGame

Conclusion "
So adding a vector to a set leaves the span unchanged exactly when the vector was already
in the span.
"

DisabledTheorem Submodule.span_insert_eq_span Submodule.mem_span_insert
TheoremTab "Independence"
NewTheorem Submodule.span_le Set.mem_insert Set.subset_insert Submodule.span_mono le_antisymm
