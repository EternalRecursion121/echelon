import Game.Levels.Subspaces.L08_Complement

World "Subspaces"
Level 9
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

The statement gives the condition; you prove the equivalence.
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
      Hint (hidden := true) "Show `a ∈ (W : Set V)` and `b ∈ (W : Set V)` (rewrite with
      `{hW}`), then `have hab : a + b ∈ (W : Set V) := W.add_mem ha hb'`."
      have ha : a ∈ (W : Set V) := by
        rw [hW]
        exact Or.inl haA
      have hb' : b ∈ (W : Set V) := by
        rw [hW]
        exact Or.inr hb
      have hab : a + b ∈ (W : Set V) := W.add_mem ha hb'
      rw [hW] at hab
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
  · intro h
    Hint "If $A \\subseteq B$ then $A \\cup B = B$."
    rcases h with h | h
    · use B
      Hint (hidden := true) "`rw [Set.union_eq_self_of_subset_left {h}]`"
      rw [Set.union_eq_self_of_subset_left h]
    · use A
      rw [Set.union_eq_self_of_subset_right h]

end LinearAlgebraGame

Conclusion "
**Answer: exactly when one contains the other.** This is why Mathlib's `A ⊔ B` is not the
union but the *sum* $A + B$: the smallest subspace containing both.
"

TheoremTab "Subspaces"
NewTheorem Set.not_subset Set.union_eq_self_of_subset_left Set.union_eq_self_of_subset_right Submodule.sub_mem add_sub_cancel_left add_sub_cancel_right
