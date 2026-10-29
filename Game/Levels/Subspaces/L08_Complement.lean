import Game.Levels.Subspaces.L07_Intersection

World "Subspaces"
Level 8
Title "Complements"

-- @sheet 4 Q5c
/-! @answer
**Never.** Every subspace contains $\vec 0$, and $\vec 0 \in A$, so $\vec 0 \notin V\setminus A$.
Hence $V \setminus A$ is never a subspace.
-/
Introduction "
**Problem Sheet 4, Question 5(c).** Let $A$ be a subspace of $V$. When is the complement
$V \\setminus A$ a subspace?

In Lean the complement is `(A : Set V)ᶜ` (displayed `(↑A)ᶜ`), and `x ∈ (↑A)ᶜ` *means*
`x ∉ A`, i.e. `x ∈ A → False`: a hypothesis `h : x ∈ (↑A)ᶜ` can be applied to a proof of
`x ∈ A` to give `False`. Decide, for an arbitrary subspace $A$: is the
complement a subspace (`right`: some subspace $W$ has exactly the complement as its set of
vectors) or not (`left`)? Your proof must work for every $A$ — write in a comment
`-- Explain:` what this says about *when* $V \\setminus A$ is a subspace.
"

namespace LinearAlgebraGame

/-- Is the complement of the subspace $A$ a subspace? -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (A : Submodule ℝ V) :
    (¬ ∃ W : Submodule ℝ V, (W : Set V) = (A : Set V)ᶜ) ∨
      (∃ W : Submodule ℝ V, (W : Set V) = (A : Set V)ᶜ) := by
  Hint "Decide first: run the subspace conditions on $V \\setminus A$ one at a time."
  left
  intro h
  obtain ⟨W, hW⟩ := h
  Hint (hidden := true) "`have h0 := W.zero_mem`, then `rw [mem_iff_of_coe_eq {hW}] at h0`."
  have h0 := W.zero_mem
  rw [mem_iff_of_coe_eq hW] at h0
  Hint (hidden := true) "`{h0}` says $\\vec 0 \\notin A$, i.e. it is a function from
  `0 ∈ A` to `False`: `exact {h0} A.zero_mem`."
  exact h0 A.zero_mem

end LinearAlgebraGame

Conclusion "**Answer: never** — $V \\setminus A$ misses $\\vec 0$."

TheoremTab "Subspaces"
