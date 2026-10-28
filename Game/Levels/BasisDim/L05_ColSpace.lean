import Game.Levels.BasisDim.L04_Sym3

World "BasisDim"
Level 5
Title "A column space"

-- @sheet 3 Q10
/-! @answer
$(d_1,d_2,d_3)$ is in the set iff it is $x\,\vec c_1 + y\,\vec c_2 + z\,\vec c_3$ for the
columns $\vec c_1 = (3,1,2)$, $\vec c_2 = (2,0,2)$, $\vec c_3 = (4,-1,5)$ of the coefficient
matrix — the set is the **column space**, the span of three vectors, hence a subspace.
Since $\vec c_3 = -\vec c_1 + \tfrac72\vec c_2$, it equals $[\{\vec c_1, \vec c_2\}]$:
$x\vec c_1 + y\vec c_2 + z\vec c_3 = (x - z)\vec c_1 + (y + \tfrac72 z)\vec c_2$, and
conversely $a\vec c_1 + b\vec c_2$ is attained with $(x,y,z) = (a,b,0)$.
$\vec c_1, \vec c_2$ are independent (the second entry forces the coefficient of
$\vec c_1$ to be 0, then the first forces the other to be 0). **Basis:
$\langle (3,1,2), (2,0,2)\rangle$**; equivalently the subspace is the plane
$-d_1 + d_2 + d_3 = 0$.
-/
Introduction "
**Problem Sheet 3, Question 10.** Show that this set of column vectors
$$\\left\\{ (d_1, d_2, d_3) \\mid \\text{there are } x, y, z \\text{ such that }
3x + 2y + 4z = d_1,\\ x - z = d_2,\\ 2x + 2y + 5z = d_3 \\right\\}$$
is a subspace of $\\mathbb R^3$. Find a basis.

The claim to prove: the set **equals** (the underlying set of) the span of
$(3,1,2)$ and $(2,0,2)$ — that makes it a subspace — and these two vectors are independent.
`Submodule.mem_span_pair` describes membership of a span of two vectors.
"

namespace LinearAlgebraGame

/-- The given set equals $[\{(3,1,2), (2,0,2)\}]$, and $\langle (3,1,2), (2,0,2)\rangle$ is
independent. -/
Statement : {d : Fin 3 → ℝ | ∃ x y z : ℝ,
      3 * x + 2 * y + 4 * z = d 0 ∧ x - z = d 1 ∧ 2 * x + 2 * y + 5 * z = d 2} =
    ((Submodule.span ℝ {![3, 1, 2], ![2, 0, 2]} : Submodule ℝ (Fin 3 → ℝ)) : Set (Fin 3 → ℝ)) ∧
    LinearIndependent ℝ ![![(3 : ℝ), 1, 2], ![2, 0, 2]] := by
  Hint "The third column $(4,-1,5)$ is a combination of the first two. Which one?"
  constructor
  · ext d
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, Submodule.mem_span_pair]
    constructor
    · intro h
      obtain ⟨x, y, z, h0, h1, h2⟩ := h
      Hint (hidden := true) "$(4,-1,5) = -(3,1,2) + \\tfrac72 (2,0,2)$, so use
      `refine ⟨{x} - {z}, {y} + 7/2 * {z}, ?_⟩` and check each coordinate."
      refine ⟨x - z, y + 7/2 * z, ?_⟩
      ext i
      fin_cases i <;> simp <;> linarith
    · intro h
      obtain ⟨a, c, hac⟩ := h
      Hint (hidden := true) "Take $x = a$, $y = c$, $z = 0$."
      rw [← hac]
      refine ⟨a, c, 0, ?_, ?_, ?_⟩ <;> simp <;> ring
  · Hint "Independence of two vectors: only the trivial relation."
    Hint (hidden := true) "`rw [LinearIndependent.pair_iff]`"
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith

end LinearAlgebraGame

Conclusion "
The set is the column space of the coefficient matrix, with basis
$\\langle (3,1,2), (2,0,2)\\rangle$.
"

TheoremTab "Basis"
NewTheorem Set.mem_setOf_eq SetLike.mem_coe
