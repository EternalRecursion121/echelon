import Game.Levels.BasisDim.L06_Sym3

World "BasisDim"
Level 7
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

You supply a basis — its size $k$ and the vectors `b : Fin k → (Fin 3 → ℝ)` — and prove that
it is independent and that the set **equals** (the underlying set of) its span. Being a span
makes the set a subspace. Membership of a set-builder set unfolds with `Set.mem_ofPred_eq`,
of `↑W` with `SetLike.mem_coe`.
"

namespace LinearAlgebraGame

/-- The given set is the span of an independent sequence $b_1, \dots, b_k$ (so it is a
subspace, with basis $b$). -/
Statement : ∃ k : ℕ, ∃ b : Fin k → (Fin 3 → ℝ), LinearIndependent ℝ b ∧
    {d : Fin 3 → ℝ | ∃ x y z : ℝ,
      3 * x + 2 * y + 4 * z = d 0 ∧ x - z = d 1 ∧ 2 * x + 2 * y + 5 * z = d 2} =
    (Submodule.span ℝ (Set.range b) : Set (Fin 3 → ℝ)) := by
  Hint "The set is the column space of the coefficient matrix: all combinations of its columns
  $(3,1,2)$, $(2,0,2)$, $(4,-1,5)$. Is one column a combination of the others?"
  Hint (hidden := true) "$(4,-1,5) = -(3,1,2) + \\tfrac72 (2,0,2)$, so
  `use 2, ![![3, 1, 2], ![2, 0, 2]]`."
  use 2, ![![3, 1, 2], ![2, 0, 2]]
  constructor
  · Hint "Independence of two vectors: only the trivial relation."
    Hint (hidden := true) "`rw [LinearIndependent.pair_iff]`"
    rw [LinearIndependent.pair_iff]
    intro s t h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    simp at h0 h1
    constructor <;> linarith
  · Hint "Two sets are equal when they have the same members: `ext d`."
    ext d
    Hint (hidden := true) "`rw [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]`"
    rw [Set.mem_ofPred_eq, SetLike.mem_coe, Submodule.mem_span_range_iff_exists_fun]
    constructor
    · rintro ⟨x, y, z, h0, h1, h2⟩
      Hint "Rewrite $x\\vec c_1 + y\\vec c_2 + z\\vec c_3$ using only your basis vectors."
      Hint (hidden := true) "`refine ⟨![{x} - {z}, {y} + 7/2 * {z}], ?_⟩`, then `ext i`,
      `fin_cases i <;> simp [Fin.sum_univ_two] <;> linarith`."
      refine ⟨![x - z, y + 7/2 * z], ?_⟩
      ext i
      fin_cases i <;> simp [Fin.sum_univ_two] <;> linarith
    · rintro ⟨c, rfl⟩
      Hint (hidden := true) "Take $z = 0$: `refine ⟨c 0, c 1, 0, ?_, ?_, ?_⟩`, then
      `<;> simp [Fin.sum_univ_two] <;> ring` (`<;>` runs the next tactic on every goal)."
      refine ⟨c 0, c 1, 0, ?_, ?_, ?_⟩ <;> simp [Fin.sum_univ_two] <;> ring

end LinearAlgebraGame

Conclusion "
The set is the column space of the coefficient matrix, with basis
$\\langle (3,1,2), (2,0,2)\\rangle$.
"

TheoremTab "Basis"
NewTheorem SetLike.mem_coe
