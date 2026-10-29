import Game.Levels.Subspaces.L09_UnionNested

World "Subspaces"
Level 10
Title "Unions (boss)"

-- @sheet 4 Q5b
/-! @answer
**$A \cup B$ is a subspace if and only if $A \subseteq B$ or $B \subseteq A$.**
($\Leftarrow$) If $A \subseteq B$ then $A \cup B = B$, a subspace; similarly if
$B \subseteq A$.
($\Rightarrow$) Suppose $A \cup B$ is a subspace but $A \not\subseteq B$ and
$B \not\subseteq A$. Pick $\vec a \in A \setminus B$ and $\vec b \in B \setminus A$. Then
$\vec a + \vec b \in A \cup B$. If $\vec a + \vec b \in A$ then
$\vec b = (\vec a + \vec b) - \vec a \in A$, a contradiction; if $\vec a + \vec b \in B$ then
$\vec a = (\vec a + \vec b) - \vec b \in B$, also a contradiction.
-/
Introduction "
**Problem Sheet 4, Question 5(b).** When is $A \\cup B$ a subspace? Provide an equivalent
condition in terms of sets and prove its equivalence.

The statement gives the condition; you prove the equivalence. The direction $\\Leftarrow$ is
the previous level, `union_subspace_of_subset`.
"

namespace LinearAlgebraGame

/-- $A \cup B$ is a subspace if and only if one of $A$, $B$ contains the other. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : Submodule ℝ V) :
    (∃ W : Submodule ℝ V, (W : Set V) = (A : Set V) ∪ B) ↔
      (A : Set V) ⊆ B ∨ (B : Set V) ⊆ A := by
  constructor
  · intro h
    obtain ⟨W, hW⟩ := h
    Hint "If $A \\subseteq B$ you are done. Otherwise take $\\vec a \\in A\\setminus B$ and
    any $\\vec b \\in B$; where can $\\vec a + \\vec b$ live?"
    Hint (hidden := true) "`by_cases hAB : (A : Set V) ⊆ B`"
    by_cases hAB : (A : Set V) ⊆ B
    · left
      exact hAB
    · right
      intro b hb
      by_contra hbA
      Hint (hidden := true) "`rw [Set.not_subset] at {hAB}` and `obtain ⟨a, haA, haB⟩ := {hAB}`."
      rw [Set.not_subset] at hAB
      obtain ⟨a, haA, haB⟩ := hAB
      Hint (hidden := true) "Show `a ∈ W` and `b ∈ W`, e.g.
      `have ha : a ∈ W := by rw [mem_iff_of_coe_eq {hW}]; exact Or.inl {haA}`.
      Then `have hab : a + b ∈ W := W.add_mem ha hb'`."
      have ha : a ∈ W := by
        rw [mem_iff_of_coe_eq hW]
        exact Or.inl haA
      have hb' : b ∈ W := by
        rw [mem_iff_of_coe_eq hW]
        exact Or.inr hb
      have hab : a + b ∈ W := W.add_mem ha hb'
      rw [mem_iff_of_coe_eq hW] at hab
      Hint "Two cases: $\\vec a + \\vec b \\in A$ or $\\vec a + \\vec b \\in B$. Subtract."
      rcases hab with hab | hab
      · apply hbA
        Hint (hidden := true) "`have := A.sub_mem {hab} {haA}`, then
        `rw [add_sub_cancel_left] at this`."
        have := A.sub_mem hab haA
        rw [add_sub_cancel_left] at this
        exact this
      · apply haB
        have := B.sub_mem hab hb
        rw [add_sub_cancel_right] at this
        exact this
  · Hint (hidden := true) "`exact union_subspace_of_subset A B`"
    exact union_subspace_of_subset A B

end LinearAlgebraGame

Conclusion "
**Answer: exactly when one contains the other.** This is why Mathlib's `A ⊔ B` is not the
union but the *sum* $A + B$: the smallest subspace containing both.
"

TheoremTab "Subspaces"
NewTheorem Set.not_subset Submodule.sub_mem add_sub_cancel_left add_sub_cancel_right
