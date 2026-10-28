import Game.Levels.Independence.L10_GaussSubset

World "Independence"
Level 11
Title "Subsets of independent sets"

Introduction "
**Lemma Two.II.1.20.** Any subset of a linearly independent set is independent; any superset
of a dependent set is dependent. Prove the first for three vectors: dropping $\\vec w$ keeps
$\\vec u, \\vec v$ independent.
"

namespace LinearAlgebraGame

/-- If $\vec u, \vec v, \vec w$ are independent then so are $\vec u, \vec v$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V)
    (h : LinearIndependent ℝ ![u, v, w]) : LinearIndependent ℝ ![u, v] := by
  Hint "A relation between $\\vec u$ and $\\vec v$ is a relation among all three with
  coefficient $0$ on $\\vec w$."
  rw [linIndep_three_iff] at h
  rw [LinearIndependent.pair_iff]
  intro a b hab
  Hint (hidden := true) "`have h1 := {h} a b 0 (by rw [zero_smul, add_zero]; exact {hab})`"
  have h1 := h a b 0 (by rw [zero_smul, add_zero]; exact hab)
  exact ⟨h1.1, h1.2.1⟩

end LinearAlgebraGame

Conclusion "
The other two cells of Hefferon's table are \"may be either\": a superset of an independent
set, or a subset of a dependent one.
"

TheoremTab "Independence"
