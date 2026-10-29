import GameServer
import Mathlib
import Game.Lib

/-! # Chapters Four–Five (Hefferon Four.I–II, Five.I–II)

Game-local definitions for the worlds
`Determinant`, `Volume`, `Eigen` and `Diagonalisation`.
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

namespace LinearAlgebraGame

open Matrix Polynomial MeasureTheory

/-! ## Determinants -/

/-- Swap rows `i` and `j` of a square matrix. -/
def swapRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) : Matrix (Fin n) (Fin n) ℝ :=
  M.submatrix (Equiv.swap i j) id

/-- Hefferon's Definition Four.I.2.1: the four conditions on a determinant function. -/
structure DetAxioms {n : ℕ} (d : Matrix (Fin n) (Fin n) ℝ → ℝ) : Prop where
  /-- (1) swapping two rows negates the determinant -/
  swap : ∀ M i j, i ≠ j → d (swapRows M i j) = - d M
  /-- (2) adding a multiple of row `i` to row `j` leaves it unchanged -/
  combo : ∀ M i j (k : ℝ), i ≠ j → d (M.updateRow j (M j + k • M i)) = d M
  /-- (3) multiplying row `i` by `k` multiplies it by `k` -/
  scale : ∀ M i (k : ℝ), d (M.updateRow i (k • M i)) = k * d M
  /-- (4) the identity has determinant one -/
  one : d 1 = 1

theorem swapRows_eq_self {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n}
    (h : M i = M j) : swapRows M i j = M := by
  ext a b
  simp only [swapRows, submatrix_apply, id]
  rcases eq_or_ne a i with rfl | hai
  · rw [Equiv.swap_apply_left, h]
  rcases eq_or_ne a j with rfl | haj
  · rw [Equiv.swap_apply_right, h]
  rw [Equiv.swap_apply_of_ne_of_ne hai haj]

theorem det_swapRows {n : ℕ} (M : Matrix (Fin n) (Fin n) ℝ) {i j : Fin n} (h : i ≠ j) :
    (swapRows M i j).det = - M.det := by
  rw [swapRows, det_permute, Equiv.Perm.sign_swap h]
  simp

/-- Condition (3) aimed at a target matrix: if scaling row `i` of `M` by `k` gives `N`,
then `d N = k * d M`. -/
theorem DetAxioms.scale_eq {n : ℕ} {d : Matrix (Fin n) (Fin n) ℝ → ℝ} (hd : DetAxioms d)
    (M N : Matrix (Fin n) (Fin n) ℝ) (i : Fin n) (k : ℝ) (h : M.updateRow i (k • M i) = N) :
    d N = k * d M := by
  rw [← h]
  exact hd.scale M i k

/-- Condition (2) aimed at a target matrix: if adding `k` times row `i` to row `j ≠ i` of `M`
gives `N`, then `d N = d M`. -/
theorem DetAxioms.combo_eq {n : ℕ} {d : Matrix (Fin n) (Fin n) ℝ → ℝ} (hd : DetAxioms d)
    (M N : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (k : ℝ) (hij : i ≠ j)
    (h : M.updateRow j (M j + k • M i) = N) : d N = d M := by
  rw [← h]
  exact hd.combo M i j k hij

/-- Condition (1) aimed at a target matrix: if swapping rows `i ≠ j` of `M` gives `N`, then
`d N = - d M`. -/
theorem DetAxioms.swap_eq {n : ℕ} {d : Matrix (Fin n) (Fin n) ℝ → ℝ} (hd : DetAxioms d)
    (M N : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hij : i ≠ j) (h : swapRows M i j = N) :
    d N = - d M := by
  rw [← h]
  exact hd.swap M i j hij

/-- The number of inversions of a permutation: pairs `i < j` with `σ j < σ i`. -/
def inversions {n : ℕ} (σ : Equiv.Perm (Fin n)) : ℕ :=
  (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2 ∧ σ p.2 < σ p.1).card

/-! ## Volume -/

/-- Hefferon's Theorem Four.II.1.5, as a black box from measure theory: the image of a
region `s` under `T` has `|det T|` times the area (volume) of `s`. -/
theorem volume_image_matrix {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (s : Set (Fin n → ℝ)) :
    (volume (Matrix.toLin' T '' s)).toReal = |T.det| * (volume s).toReal := by
  rw [MeasureTheory.Measure.addHaar_image_linearMap, LinearMap.det_toLin', ENNReal.toReal_mul,
    ENNReal.toReal_ofReal (abs_nonneg _)]

/-- The signed area of the triangle `PQR` in the plane: half the determinant of the edge
vectors `Q − P`, `R − P`. -/
noncomputable def triArea (P Q R : Fin 2 → ℝ) : ℝ :=
  (1 / 2) * (!![Q 0 - P 0, R 0 - P 0; Q 1 - P 1, R 1 - P 1] : Matrix (Fin 2) (Fin 2) ℝ).det

/-! ## Similarity and eigenvalues -/

/-- `T` and `S` are similar: `S = P T P⁻¹` for some nonsingular `P`. -/
def MatSimilar {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ P : Matrix (Fin n) (Fin n) ℝ, IsUnit P ∧ S = P * T * P⁻¹

/-- `T` is diagonalisable: it is similar to a diagonal matrix. -/
def Diagonalizable {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : Prop :=
  ∃ d : Fin n → ℝ, MatSimilar T (diagonal d)

/-- `μ` is a (real) eigenvalue of `T`: some nonzero `v` has `T v = μ v`. -/
def IsEigenvalue {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) : Prop :=
  ∃ v : Fin n → ℝ, v ≠ 0 ∧ T *ᵥ v = μ • v

theorem mul_inv_of_isUnit {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) :
    P * P⁻¹ = 1 :=
  Matrix.mul_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP)

theorem inv_mul_of_isUnit {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) :
    P⁻¹ * P = 1 :=
  Matrix.nonsing_inv_mul P ((Matrix.isUnit_iff_isUnit_det P).1 hP)

theorem isUnit_inv_of_isUnit {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) :
    IsUnit P⁻¹ :=
  (Matrix.isUnit_nonsing_inv_iff).2 hP

theorem inv_inv_of_isUnit {n : ℕ} {P : Matrix (Fin n) (Fin n) ℝ} (hP : IsUnit P) :
    P⁻¹⁻¹ = P :=
  Matrix.nonsing_inv_nonsing_inv P ((Matrix.isUnit_iff_isUnit_det P).1 hP)

/-- To show similarity it is enough to exhibit `P` together with a left inverse `Q`. -/
theorem matSimilar_of_mul_eq_one {n : ℕ} {T S : Matrix (Fin n) (Fin n) ℝ}
    (P Q : Matrix (Fin n) (Fin n) ℝ) (hQP : Q * P = 1) (h : S = P * T * Q) : MatSimilar T S := by
  refine ⟨P, ?_, ?_⟩
  · exact (Matrix.isUnit_iff_isUnit_det P).2 (Matrix.isUnit_det_of_left_inverse hQP)
  · rw [Matrix.inv_eq_left_inv hQP, h]

/-- Evaluating Hefferon's characteristic polynomial at `μ` gives `|T − μI|`. -/
theorem charpolyH_eval {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) :
    (charpolyH T).eval μ = (T - μ • 1).det := by
  rw [charpolyH, ← Polynomial.coe_evalRingHom, RingHom.map_det]
  congr 1
  ext i j
  by_cases h : i = j <;> simp [h]

/-- Multiplying out two linear factors (Vieta): $(x-a)(x-b) = x^2 - (a+b)x + ab$. -/
theorem X_sub_C_mul_X_sub_C (a b : ℝ) :
    (X - C a) * (X - C b) = X ^ 2 - C (a + b) * X + C (a * b) := by
  rw [C_add, C_mul]
  ring

/-- Membership in the eigenspace of a matrix: $\vec v \in V_\mu \iff T\vec v = \mu\vec v$. -/
theorem mem_eigenspace_toLin' {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (v : Fin n → ℝ) :
    v ∈ Module.End.eigenspace (Matrix.toLin' T) μ ↔ T *ᵥ v = μ • v := by
  rw [Module.End.mem_eigenspace_iff, Matrix.toLin'_apply]

theorem charpolyH_natDegree {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    (charpolyH T).natDegree = n := by
  rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, natDegree_C_mul
    (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)), charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem charpolyH_ne_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : charpolyH T ≠ 0 := by
  rw [charpolyH_eq]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (charpoly_monic T).ne_zero

end LinearAlgebraGame
