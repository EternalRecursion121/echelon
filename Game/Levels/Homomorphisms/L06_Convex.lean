import Game.Levels.Homomorphisms.L05_Segment

World "Homomorphisms"
Level 6
Title "Linear maps preserve convexity"

-- @sheet 5 Q3b
/-! @answer
Let $C$ be convex and take two points of $h(C)$; they are $h(\vec c_1)$ and $h(\vec c_2)$ with
$\vec c_1,\vec c_2\in C$. By part (a) the segment between them is the image of the segment
between $\vec c_1$ and $\vec c_2$, which lies in $C$ by convexity. So every point of the segment
is $h(\vec x)$ for some $\vec x\in C$, i.e. lies in $h(C)$. Hence $h(C)$ is convex.
-/
Introduction "
**Problem Sheet 5, Question 3(b).** A subset of $\\mathbb R^n$ is *convex* if, for any two points
in that set, the line segment joining them lies entirely in that set. Prove that linear maps
from $\\mathbb R^n$ to $\\mathbb R^m$ preserve the property of set convexity.

`IsConvex C` is defined as `∀ u ∈ C, ∀ v ∈ C, seg u v ⊆ C`. Part (a) is in your inventory as
`image_seg`.
"

namespace LinearAlgebraGame

/-- If $C \subseteq \mathbb R^n$ is convex, so is its image $h(C)$. -/
Statement {n m : ℕ} (h : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (C : Set (Fin n → ℝ))
    (hC : IsConvex C) : IsConvex (h '' C) := by
  Hint "Two points of $h(C)$ are $h(\\vec c_1)$, $h(\\vec c_2)$ with $\\vec c_i \\in C$. Use part (a)."
  Hint (hidden := true) "`rintro _ ⟨c₁, hc1, rfl⟩ _ ⟨c₂, hc2, rfl⟩ y hy`"
  rintro _ ⟨c₁, hc1, rfl⟩ _ ⟨c₂, hc2, rfl⟩ y hy
  Hint (hidden := true) "`rw [← image_seg] at {hy}`, then `obtain ⟨x, hx, rfl⟩ := {hy}`."
  rw [← image_seg] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  Hint (hidden := true) "`exact ⟨x, hC c₁ hc1 c₂ hc2 hx, rfl⟩`"
  exact ⟨x, hC c₁ hc1 c₂ hc2 hx, rfl⟩

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 5 Q3(b):** the segment between $h(\\vec c_1)$ and $h(\\vec c_2)$ is the image of
the segment between $\\vec c_1$ and $\\vec c_2$, which lies in $C$; so it lies in $h(C)$.
"

NewTheorem LinearAlgebraGame.image_seg
NewDefinition LinearAlgebraGame.IsConvex
DisabledTactic simp norm_num
TheoremTab "Maps"
