import Game.Levels.Homomorphisms.L11_OntoRank

World "Homomorphisms"
Level 12
Title "Same dimension: one-to-one iff onto"

-- @sheet 6 Q4b
/-! @answer
By Theorem 2.20, $h$ is one-to-one iff $\operatorname{rank}(h) = \dim V$. By part (a), $h$ is
onto iff $\operatorname{rank}(h) = \dim W$. Since $\dim V = \dim W$ these two conditions are the
same, so $h$ is one-to-one if and only if it is onto.
-/
Introduction "
**Problem Sheet 6, Question 4(b).** Suppose $V, W$ have the same dimension. Use part (a) and
Theorem 2.20 of Section Three.II to conclude that $h$ is one-to-one if and only if $h$ is onto.

Part (a) is `onto_iff_rank`; the part of Theorem 2.20 you need is `inj_iff_rank`.
"

namespace LinearAlgebraGame

/-- If $\dim V = \dim W$ then $h$ is one-to-one iff it is onto. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ V] [FiniteDimensional ℝ W] (h : V →ₗ[ℝ] W)
    (hd : Module.finrank ℝ V = Module.finrank ℝ W) :
    Function.Injective h ↔ Function.Surjective h := by
  Hint "Both sides are statements about the rank."
  Hint (hidden := true) "`rw [inj_iff_rank, onto_iff_rank, {hd}]`"
  rw [inj_iff_rank, onto_iff_rank, hd]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q4(b):** one-to-one ⇔ rank $= \\dim V = \\dim W$ ⇔ onto.
"

NewTheorem LinearAlgebraGame.inj_iff_rank LinearAlgebraGame.onto_iff_rank
DisabledTheorem LinearMap.injective_iff_surjective_of_finrank_eq_finrank LinearMap.injective_iff_surjective LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank
DisabledTactic simp norm_num
TheoremTab "Dimension"
