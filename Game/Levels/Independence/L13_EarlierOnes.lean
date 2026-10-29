import Game.Levels.Independence.L12_PairDependent

World "Independence"
Level 13
Title "Blame an earlier vector (boss)"

Introduction "
**Corollary Two.II.1.19.** $\\{\\vec s_1, \\ldots, \\vec s_n\\}$ is linearly dependent if and
only if some $\\vec s_i$ is a linear combination of $\\vec s_1, \\ldots, \\vec s_{i-1}$
(for $i = 1$ that means $\\vec s_1 = \\vec 0$, the empty combination).

Prove it for three vectors. You have all the pieces: the two-vector case
(`pair_dependent_iff`, level 12), the extension lemma (`extension_lemma`, level 10) and
\"a superset of a dependent set is dependent\" (`indep_pair_of_indep_three`, level 9).
"

namespace LinearAlgebraGame

/-- $\vec u, \vec v, \vec w$ are dependent iff $\vec u = \vec 0$, or $\vec v \in [\{\vec u\}]$, or
$\vec w \in [\{\vec u, \vec v\}]$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V) :
    ¬ LinearIndependent ℝ ![u, v, w] ↔
      u = 0 ∨ v ∈ Submodule.span ℝ {u} ∨ w ∈ Submodule.span ℝ {u, v} := by
  Hint "Are $\\vec u, \\vec v$ independent? Split on that. If they are, the extension lemma
  decides the question; if not, the two-vector case does."
  Hint (hidden := true) "`by_cases huv : LinearIndependent ℝ ![u, v]`"
  by_cases huv : LinearIndependent ℝ ![u, v]
  · Hint (hidden := true) "`rw [extension_lemma u v w {huv}]`"
    rw [extension_lemma u v w huv]
    constructor
    · intro h
      right
      right
      Hint (hidden := true) "`{h}` says it is *not* true that $\\vec w \\notin [\\\{\\vec u, \\vec v\\}]$:
      `by_contra hw`, then `exact {h} hw`."
      by_contra hw
      exact h hw
    · Hint "If $\\vec u = \\vec 0$ or $\\vec v \\in [\\\{\\vec u\\}]$, then `{huv}` is contradicted by
      the two-vector case."
      intro h hw
      rcases h with h | h | h
      · Hint (hidden := true) "`(pair_dependent_iff u v).mpr (Or.inl {h})` says $\\vec u, \\vec v$ are
        dependent: `exact (pair_dependent_iff u v).mpr (Or.inl {h}) {huv}`."
        exact (pair_dependent_iff u v).mpr (Or.inl h) huv
      · exact (pair_dependent_iff u v).mpr (Or.inr h) huv
      · exact hw h
  · Hint "Now $\\vec u, \\vec v$ are dependent, so both sides are true."
    constructor
    · intro _
      Hint (hidden := true) "`rw [pair_dependent_iff] at {huv}`"
      rw [pair_dependent_iff] at huv
      rcases huv with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
    · intro _ hli
      Hint (hidden := true) "`exact {huv} (indep_pair_of_indep_three u v w {hli})`"
      exact huv (indep_pair_of_indep_three u v w hli)

end LinearAlgebraGame

Conclusion "
Read left to right, this is an algorithm: walk along the list and throw away any vector that
lies in the span of the ones kept so far.
"

TheoremTab "Independence"
