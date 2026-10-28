import Game.Levels.Independence.L09_Extension

World "Independence"
Level 10
Title "Gauss's method prunes a spanning set"

Introduction "
**Corollary Two.II.1.17.** Every finite set has a linearly independent subset with the same
span. Hefferon's proof is Gauss's method: put the vectors as columns, reduce, and keep the
vectors belonging to leading variables; the others are combinations of them.

For $S = \\{(1,1,3), (-1,1,0), (1,3,6)\\}$ in $\\mathbb{R}^3$, reduction shows the third vector
is $2\\cdot(1,1,3) + (-1,1,0)$. Prove that the first two vectors span
the same space as all three, and are independent.

`Set.pair_comm` and `Set.insert_comm` reorder the elements of a set, so that Lemma 1.2's
`insert v S` shape appears.
"

namespace LinearAlgebraGame

/-- $[\{(1,1,3), (-1,1,0), (1,3,6)\}] = [\{(1,1,3), (-1,1,0)\}]$, and the latter pair is
independent. -/
Statement : Submodule.span ℝ {(![1, 1, 3] : Fin 3 → ℝ), ![-1, 1, 0], ![1, 3, 6]} =
      Submodule.span ℝ {(![1, 1, 3] : Fin 3 → ℝ), ![-1, 1, 0]} ∧
    LinearIndependent ℝ ![(![1, 1, 3] : Fin 3 → ℝ), ![-1, 1, 0]] := by
  constructor
  · Hint "Move the third vector to the front, then use Lemma 1.2: it lies in the span of the
    other two."
    Hint (hidden := true) "`rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]` turns the left
    side into `span (insert ![1, 3, 6] \{![1, 1, 3], ![-1, 1, 0]})`. Then
    `rw [← span_insert_iff, Submodule.mem_span_pair]`."
    rw [Set.pair_comm, Set.insert_comm, Set.pair_comm]
    rw [← span_insert_iff, Submodule.mem_span_pair]
    Hint (hidden := true) "`use 1, 2`, then `ext i`, `fin_cases i <;> simp <;> norm_num`."
    use 1, 2
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

NewTheorem Set.pair_comm Set.insert_comm LinearAlgebraGame.span_insert_iff
TheoremTab "Independence"
