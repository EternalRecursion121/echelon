import Game.Levels.Independence.L01_TrivialRelation

World "Independence"
Level 2
Title "Zero spoils independence"

Introduction "
Any set containing $\\vec 0$ is dependent: $1\\cdot\\vec 0 = \\vec 0$ is a nontrivial
relation. Show this for a pair $\\vec u, \\vec 0$.
"

namespace LinearAlgebraGame

/-- The pair $\vec u, \vec 0$ is linearly dependent. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (u : V) :
    ¬ LinearIndependent ℝ ![u, 0] := by
  Hint "Assume it is independent and feed it the relation $0\\cdot\\vec u + 1\\cdot\\vec 0 = \\vec 0$."
  intro h
  Hint (hidden := true) "`rw [LinearIndependent.pair_iff] at {h}`"
  rw [LinearIndependent.pair_iff] at h
  Hint (hidden := true) "`have h1 := {h} 0 1 (by rw [zero_smul, smul_zero, add_zero])`, then
  `norm_num at h1`."
  have h1 := h 0 1 (by rw [zero_smul, smul_zero, add_zero])
  norm_num at h1

end LinearAlgebraGame

Conclusion "A relation is nontrivial as soon as *one* coefficient is nonzero."

DisabledTactic simp
TheoremTab "Independence"

