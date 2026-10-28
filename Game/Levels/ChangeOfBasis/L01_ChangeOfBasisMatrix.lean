import Game.Metadata
import Game.Ch3b
import Game.Levels.MatrixOfMap.L14_RankCompLeft

World "ChangeOfBasis"
Level 1
Title "The change-of-basis matrix"

Introduction "
Hefferon Definition Three.V.1.1: the **change-of-basis matrix** from $B$ to $D$ is
$\\mathrm{Rep}_{B,D}(\\mathrm{id})$ — the identity map, represented with *different* bases on
the two sides. Multiplying by it converts $B$-coordinates into $D$-coordinates.

The most useful case is $D = \\mathcal E_n$, the standard basis (`stdBasis n`). Then column $j$
of $\\mathrm{Rep}_{B,\\mathcal E_n}(\\mathrm{id})$ is $\\mathrm{Rep}_{\\mathcal E_n}(\\vec\\beta_j) = \\vec\\beta_j$
itself. Prove it: the matrix represents the identity iff its columns are the vectors of $B$.
"

namespace LinearAlgebraGame

/-- $H = \mathrm{Rep}_{B,\mathcal E_n}(\mathrm{id})$ iff column $j$ of $H$ is $\vec\beta_j$. -/
Statement isRep_id_std_iff {n : ℕ} (B : Fin n → (Fin n → ℝ)) (H : Matrix (Fin n) (Fin n) ℝ) :
    IsRep B (stdBasis n) LinearMap.id H ↔ ∀ i j, H i j = B j i := by
  Hint "Component $i$ of $\\sum_l h_\{lj}\\vec e_l$ is $h_\{ij}$."
  constructor
  · intro h i j
    Hint (hidden := true) "Take component `i` of column `j`: `have := congrFun ({h} j) i`, then
    `simp [stdBasis, Pi.single_apply, Finset.sum_apply] at this`."
    have := congrFun (h j) i
    simp [stdBasis, Pi.single_apply, Finset.sum_apply] at this
    rw [this]
  · intro h j
    ext i
    Hint (hidden := true) "`simp [stdBasis, Pi.single_apply, Finset.sum_apply, {h}]`"
    simp [stdBasis, Pi.single_apply, Finset.sum_apply, h]

end LinearAlgebraGame

Conclusion "
$\\mathrm{Rep}_{B,\\mathcal E_n}(\\mathrm{id})$ is just the vectors of $B$ written as columns.
"

NewDefinition LinearAlgebraGame.stdBasis

TheoremTab "Change of basis"
NewTheorem Pi.single_apply
