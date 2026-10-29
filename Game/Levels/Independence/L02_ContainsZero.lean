import Game.Levels.Independence.L01_TrivialRelation

World "Independence"
Level 2
Title "Zero spoils independence"

Introduction "
**Independence in Lean.** `LinearIndependent ℝ ![v₀, v₁, …]` says the vectors
$\\vec v_0, \\vec v_1, \\ldots$ satisfy only the trivial linear relation (Lemma 1.5). Lean
speaks of a *family* — a numbered list `![v₀, v₁, …]` — not a set. That takes care of
Hefferon's \"distinct members\": the family `![v, v]` is dependent ($1\\cdot\\vec v - 1\\cdot\\vec v
= \\vec 0$), although the *set* $\\{\\vec v, \\vec v\\}$ is just $\\{\\vec v\\}$.

To use or prove `LinearIndependent`, rewrite it into \"only the trivial relation\" form with
the version that fits the number of vectors:
- `LinearIndependent.pair_iff` (two vectors, unlocked now):
  `LinearIndependent ℝ ![x, y] ↔ ∀ s t, s • x + t • y = 0 → s = 0 ∧ t = 0`;
- `linIndep_three_iff` (three vectors) and `Fintype.linearIndependent_iff` (any finite family),
  unlocked when you first need them.

`¬ LinearIndependent …` (dependent) is a negation: `intro h` assumes independence and asks
for `False`.

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
NewTheorem LinearIndependent.pair_iff

