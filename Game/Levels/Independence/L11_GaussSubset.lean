import Game.Levels.Independence.L10_Extension

World "Independence"
Level 11
Title "Gauss's method prunes a spanning set"

Introduction "
**Corollary Two.II.1.17.** Every finite set has a linearly independent subset with the same
span. Hefferon's proof is Gauss's method: put the vectors as columns, reduce, and keep the
vectors belonging to leading variables; the others are combinations of them.

Take $S = \\{(1,3,6), (1,1,3), (-1,1,0)\\}$ in $\\mathbb{R}^3$. Gauss's method (on paper)
shows that $(1,3,6)$ is a combination of the other two. Prove that $(1,1,3)$ and $(-1,1,0)$
span the same space as all three, and are independent.

The set `{a, b, c}` *is* `insert a {b, c}`, so Lemma 1.2 (`span_insert_iff`) applies to it
directly.
"

namespace LinearAlgebraGame

/-- $[\{(1,3,6), (1,1,3), (-1,1,0)\}] = [\{(1,1,3), (-1,1,0)\}]$, and the latter pair is
independent. -/
Statement : Submodule.span ℝ {(![1, 3, 6] : Fin 3 → ℝ), ![1, 1, 3], ![-1, 1, 0]} =
      Submodule.span ℝ {(![1, 1, 3] : Fin 3 → ℝ), ![-1, 1, 0]} ∧
    LinearIndependent ℝ ![(![1, 1, 3] : Fin 3 → ℝ), ![-1, 1, 0]] := by
  constructor
  · Hint "By Lemma 1.2 it suffices that $(1,3,6)$ lies in the span of the other two."
    Hint (hidden := true) "`rw [← span_insert_iff, Submodule.mem_span_pair]`"
    rw [← span_insert_iff, Submodule.mem_span_pair]
    Hint (hidden := true) "Gauss's method gives $(1,3,6) = 2\\cdot(1,1,3) + (-1,1,0)$:
    `use 2, 1`, then `ext i`, `fin_cases i <;> simp <;> norm_num`."
    use 2, 1
    ext i
    fin_cases i <;> simp <;> norm_num
  · rw [LinearIndependent.pair_iff]
    intro a b h
    Hint (hidden := true) "Compare the first two coordinates: `congrFun {h} 0`, `congrFun {h} 1`."
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor
    · linarith
    · linarith

end LinearAlgebraGame

Conclusion "
The span of $S$ is a plane, and $\\{(1,1,3), (-1,1,0)\\}$ is a basis of it — the theme of the
next world.
"

TheoremTab "Independence"
