import Game.Levels.Homomorphisms.L01_MapZero

World "Homomorphisms"
Level 2
Title "Subtraction"

-- @sheet 5 Q2
/-! @answer
**Yes.** Using $\vec u - \vec v = \vec u + (-1)\vec v$ and that $h$ preserves addition and scalar
multiplication:
$$h(\vec u - \vec v) = h(\vec u + (-1)\vec v) = h(\vec u) + (-1)h(\vec v) = h(\vec u) - h(\vec v).$$
-/
Introduction "
**Problem Sheet 5, Question 2.** Part of the definition of a linear function is that it
respects addition. Does a linear function respect subtraction?

This is a *decide* level: the goal is `¬ P ∨ P`. Commit with `left` (no) or `right` (yes),
then prove your choice.
"

namespace LinearAlgebraGame

/-- Decide: does $h(\vec u - \vec v) = h(\vec u) - h(\vec v)$ always hold? -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (h : V →ₗ[ℝ] W) :
    (¬ ∀ u v : V, h (u - v) = h u - h v) ∨ ∀ u v : V, h (u - v) = h u - h v := by
  Hint "Decide first. Can subtraction be built from the operations $h$ preserves?"
  right
  intro u v
  Hint "Idea: $\\vec u - \\vec v = \\vec u + (-1)\\cdot\\vec v$."
  Hint (hidden := true) "`rw [sub_eq_add_neg, map_add, ← neg_one_smul ℝ {v}, map_smul, neg_one_smul, ← sub_eq_add_neg]`"
  rw [sub_eq_add_neg, map_add, ← neg_one_smul ℝ v, map_smul, neg_one_smul, ← sub_eq_add_neg]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 5 Q2: yes**, $h(\\vec u - \\vec v) = h(\\vec u) + (-1)h(\\vec v) = h(\\vec u) - h(\\vec v)$.
Mathlib's name for this is `map_sub`, now in your inventory.
"

DisabledTheorem map_sub LinearMap.map_sub
DisabledTactic simp norm_num
TheoremTab "Maps"
