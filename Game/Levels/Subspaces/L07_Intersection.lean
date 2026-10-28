import Game.Levels.Subspaces.L06_Span

World "Subspaces"
Level 7
Title "Intersections"

-- @sheet 4 Q5a
/-! @answer
**Always.** $\vec 0 \in A$ and $\vec 0 \in B$, so $A \cap B \neq \emptyset$. If
$\vec x, \vec y \in A\cap B$ and $c_1, c_2 \in \mathbb{R}$ then $c_1\vec x + c_2\vec y \in A$
because $A$ is a subspace, and likewise $\in B$; so it lies in $A \cap B$. By the subspace
test, $A \cap B$ is a subspace.
-/
Introduction "
**Problem Sheet 4, Question 5.** Subspaces are subsets and so we naturally consider how
'is a subspace' interacts with the usual set operations. Let $A, B$ be subspaces of a vector
space $V$.

**(a)** When is $A \\cap B$ a subspace? Always? Sometimes? Never?

The statement below claims your answer for *every* pair $A, B$.
"

namespace LinearAlgebraGame

/-- For all subspaces $A, B$, the intersection $A \cap B$ is a subspace. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (A B : Submodule ℝ V) :
    ∃ W : Submodule ℝ V, (W : Set V) = (A : Set V) ∩ B := by
  Hint "Subspace test: is $\\vec 0$ in both? Is a combination of vectors in both, in both?"
  apply subspace_test
  · use 0
    exact ⟨A.zero_mem, B.zero_mem⟩
  · intro c₁ c₂ x y hx hy
    obtain ⟨hxA, hxB⟩ := hx
    obtain ⟨hyA, hyB⟩ := hy
    Hint (hidden := true) "`constructor`, then
    `exact A.add_mem (A.smul_mem c₁ {hxA}) (A.smul_mem c₂ {hyA})`."
    constructor
    · exact A.add_mem (A.smul_mem c₁ hxA) (A.smul_mem c₂ hyA)
    · exact B.add_mem (B.smul_mem c₁ hxB) (B.smul_mem c₂ hyB)

end LinearAlgebraGame

Conclusion "
**Answer: always.** Mathlib writes this subspace as `A ⊓ B` (\"meet\").
"

DisabledTheorem Submodule.coe_inf Submodule.mem_inf
TheoremTab "Subspaces"
