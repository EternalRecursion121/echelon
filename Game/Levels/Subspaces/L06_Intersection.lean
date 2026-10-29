import Game.Levels.Subspaces.L05_Span

World "Subspaces"
Level 6
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

Decide: `right` claims \"always\" (for every pair $A, B$ of subspaces of $V$, the
intersection is a subspace); `left` claims \"not always\" (sometimes or never).
"

namespace LinearAlgebraGame

/-- Is $A \cap B$ a subspace for all subspaces $A, B$? -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] :
    (¬ ∀ A B : Submodule ℝ V, ∃ W : Submodule ℝ V, (W : Set V) = (A : Set V) ∩ B) ∨
      ∀ A B : Submodule ℝ V, ∃ W : Submodule ℝ V, (W : Set V) = (A : Set V) ∩ B := by
  Hint "Decide first: test the subspace test on $A \\cap B$. Is $\\vec 0$ in it? Is a
  combination of two of its vectors in it?"
  right
  intro A B
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
