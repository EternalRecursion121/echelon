import Game.Levels.MatrixOfMap.L06_FindD

World "MatrixOfMap"
Level 7
Title "Mathlib's matrix of a map"

Introduction "
Mathlib's name for $\\mathrm{Rep}_{B,D}(h)$ is `LinearMap.toMatrix B D h`, for bases
`B : Module.Basis (Fin n) ℝ V` and `D : Module.Basis (Fin m) ℝ W`. Its entries are defined by
`LinearMap.toMatrix_apply`: the $(i,j)$ entry is coordinate $i$ of $h(\\vec\\beta_j)$, i.e.
`D.repr (h (B j)) i`.

Check that this agrees with our column-by-column definition. The key fact is that a vector
is the sum of its coordinates times the basis vectors: `Module.Basis.sum_repr`.
"

namespace LinearAlgebraGame

/-- `LinearMap.toMatrix B D h` represents `h` with respect to `B`, `D`. -/
Statement isRep_toMatrix {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] {m n : ℕ} (B : Module.Basis (Fin n) ℝ V) (D : Module.Basis (Fin m) ℝ W)
    (h : V →ₗ[ℝ] W) : IsRep B D h (LinearMap.toMatrix B D h) := by
  Hint "Unfold the goal for one column `j`, then rewrite the entries."
  intro j
  Hint (hidden := true) "`simp only [LinearMap.toMatrix_apply]` turns the entries into
  coordinates; then `rw [D.sum_repr]`."
  simp only [LinearMap.toMatrix_apply]
  rw [D.sum_repr]

end LinearAlgebraGame

Conclusion "
From now on you may use Mathlib's `LinearMap.toMatrix` and our `IsRep` interchangeably.
"

NewTheorem LinearMap.toMatrix_apply
NewDefinition LinearMap.toMatrix
TheoremTab "Matrices"
