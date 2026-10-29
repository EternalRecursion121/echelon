import Game.Levels.Subspaces.L08_Complement

World "Subspaces"
Level 9
Title "Nested unions"

Introduction "
Warm-up for Sheet 4 Q5(b) (the next level): if one subspace contains the other, their union
is a subspace — because the union is just the bigger one.

`A ∪ B` is the union of the two sets of vectors; `(A : Set V) ⊆ B` says every vector of $A$
is in $B$.
"

namespace LinearAlgebraGame

/-- If $A \subseteq B$ or $B \subseteq A$, then $A \cup B$ is a subspace. -/
Statement union_subspace_of_subset {V : Type*} [AddCommGroup V] [Module ℝ V]
    (A B : Submodule ℝ V) (h : (A : Set V) ⊆ B ∨ (B : Set V) ⊆ A) :
    ∃ W : Submodule ℝ V, (W : Set V) = (A : Set V) ∪ B := by
  Hint "If $A \\subseteq B$ then $A \\cup B = B$. Split into the two cases."
  rcases h with h | h
  · Hint (hidden := true) "`use B`, then `rw [Set.union_eq_self_of_subset_left {h}]`."
    use B
    rw [Set.union_eq_self_of_subset_left h]
  · use A
    rw [Set.union_eq_self_of_subset_right h]

end LinearAlgebraGame

Conclusion "
That was the easy direction. Now the converse.
"

TheoremTab "Subspaces"
NewTheorem Set.union_eq_self_of_subset_left Set.union_eq_self_of_subset_right
