import GameServer
import Mathlib
import Game.Lib

/-! # Chapters Four–Five (Hefferon Four.I–II, Five.I–II)

Game-local definitions and all `TheoremDoc` / `DefinitionDoc` entries for the worlds
`Determinant`, `Volume`, `Eigen` and `Diagonalisation`. -/

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
theorem matSimilar_of_mul_eq_one {n : ℕ} {T S P Q : Matrix (Fin n) (Fin n) ℝ}
    (hQP : Q * P = 1) (h : S = P * T * Q) : MatSimilar T S := by
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

theorem charpolyH_natDegree {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    (charpolyH T).natDegree = n := by
  rw [charpolyH_eq, show ((-1 : ℝ[X]) ^ n) = C ((-1) ^ n) by simp, natDegree_C_mul
    (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)), charpoly_natDegree_eq_dim, Fintype.card_fin]

theorem charpolyH_ne_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : charpolyH T ≠ 0 := by
  rw [charpolyH_eq]
  exact mul_ne_zero (pow_ne_zero _ (neg_ne_zero.2 one_ne_zero)) (charpoly_monic T).ne_zero

end LinearAlgebraGame

/-! ## Documentation -/

/-- `Commute.all a b`: in a commutative ring, $ab = ba$. -/
TheoremDoc Commute.all as "all" in "Eigen"

/-- `Equivalence r`: `r` is reflexive, symmetric and transitive (`constructor` splits it). -/
DefinitionDoc Equivalence as "Equivalence"

/-- $\prod_{i<2} f(i) = f(0)f(1)$. -/
TheoremDoc Fin.prod_univ_two as "prod_univ_two" in "Det"

/-- $\sum_{i<4} f(i) = f(0)+f(1)+f(2)+f(3)$. -/
TheoremDoc Fin.sum_univ_four as "sum_univ_four" in "Eigen"

/-- $\sum_{i<2} f(i) = f(0)+f(1)$. -/
TheoremDoc Fin.sum_univ_two as "sum_univ_two" in "Eigen"

/-- `Finset.univ.card = Fintype.card α`. -/
TheoremDoc Finset.card_univ as "card_univ" in "Eigen"

/-- $a\sum_i f(i) = \sum_i a f(i)$. -/
TheoremDoc Finset.mul_sum as "mul_sum" in "Eigen"

/-- Two products over the same set are equal if their factors agree pointwise. -/
TheoremDoc Finset.prod_congr as "prod_congr" in "Eigen"

/-- $\prod_{i\in s}(-f(i)) = (-1)^{|s|}\prod_{i \in s} f(i)$. -/
TheoremDoc Finset.prod_neg as "prod_neg" in "Eigen"

/-- A product of an updated function: replacing $f(i)$ by $b$ gives $b\cdot\prod_{j \ne i} f(j)$. -/
TheoremDoc Finset.prod_update_of_mem as "prod_update_of_mem" in "Eigen"

/-- `s \ {a} = s.erase a`. -/
TheoremDoc Finset.sdiff_singleton_eq_erase as "sdiff_singleton_eq_erase" in "Eigen"

/-- Two sums over the same set are equal if their terms agree pointwise. -/
TheoremDoc Finset.sum_congr as "sum_congr" in "Eigen"

/-- $(\sum_i f(i))\,a = \sum_i f(i)\,a$. -/
TheoremDoc Finset.sum_mul as "sum_mul" in "Eigen"

/-- `Fintype.card (Fin n) = n`. -/
TheoremDoc Fintype.card_fin as "card_fin" in "Eigen"

/-- `IsUnit P`: $P$ is invertible (for a matrix: nonsingular). -/
DefinitionDoc IsUnit as "IsUnit"

/-- A product of invertible elements is invertible. -/
TheoremDoc IsUnit.mul as "mul" in "Eigen"

/-- `DetAxioms d`: Hefferon's four conditions (Def Four.I.2.1) on a function $d$ of square matrices. Fields: `swap` (row swap negates), `combo` ($k\rho_i + \rho_j$ leaves it unchanged), `scale` ($k\rho_i$ multiplies by $k$), `one` ($d(I) = 1$). -/
DefinitionDoc LinearAlgebraGame.DetAxioms as "DetAxioms"

/-- `Diagonalizable T`: $T$ is similar to a diagonal matrix: `∃ d, MatSimilar T (Matrix.diagonal d)`. -/
DefinitionDoc LinearAlgebraGame.Diagonalizable as "Diagonalizable"

/-- `IsEigenvalue T μ`: there is a vector $\vec v \ne \vec 0$ with $T\vec v = \mu\vec v$. -/
DefinitionDoc LinearAlgebraGame.IsEigenvalue as "IsEigenvalue"

/-- `MatSimilar T S`: $S = PTP^{-1}$ for some nonsingular $P$ (`∃ P, IsUnit P ∧ S = P * T * P⁻¹`). -/
DefinitionDoc LinearAlgebraGame.MatSimilar as "MatSimilar"

/-- `Poly n`: polynomials of degree at most $n$, stored as coefficient vectors $(a_0, \dots, a_n)$ (`Fin (n+1) → ℝ`). -/
DefinitionDoc LinearAlgebraGame.Poly as "Poly"

/-- `Poly.deriv`: the linear map $d/dx$ on `Poly n`; the coefficient of $x^i$ in $p'$ is $(i+1)a_{i+1}$. -/
DefinitionDoc LinearAlgebraGame.Poly.deriv as "deriv"

/-- `charpolyH T`: Hefferon's characteristic polynomial $|T - xI|$ (a polynomial in `X`). -/
DefinitionDoc LinearAlgebraGame.charpolyH as "charpolyH"

/-- Bridge to Mathlib: $|T - xI| = (-1)^n\det(xI - T)$, i.e. `charpolyH T = (-1)^n * T.charpoly`. -/
TheoremDoc LinearAlgebraGame.charpolyH_eq as "charpolyH_eq" in "Eigen"

/-- Evaluating $|T - xI|$ at $x = \mu$ gives $|T - \mu I|$: `(charpolyH T).eval μ = (T - μ • 1).det`. -/
TheoremDoc LinearAlgebraGame.charpolyH_eval as "charpolyH_eval" in "Eigen"

/-- $|T - xI|$ has degree exactly $n$. -/
TheoremDoc LinearAlgebraGame.charpolyH_natDegree as "charpolyH_natDegree" in "Eigen"

/-- $|T - xI|$ is not the zero polynomial. -/
TheoremDoc LinearAlgebraGame.charpolyH_ne_zero as "charpolyH_ne_zero" in "Eigen"

/-- Mathlib: swapping two different rows negates `Matrix.det` (from `det_permute` and the sign of a transposition). -/
TheoremDoc LinearAlgebraGame.det_swapRows as "det_swapRows" in "Det"

/-- For nonsingular $P$: $(P^{-1})^{-1} = P$. -/
TheoremDoc LinearAlgebraGame.inv_inv_of_isUnit as "inv_inv_of_isUnit" in "Eigen"

/-- For nonsingular $P$: $P^{-1}P = I$. -/
TheoremDoc LinearAlgebraGame.inv_mul_of_isUnit as "inv_mul_of_isUnit" in "Eigen"

/-- `inversions σ`: the number of pairs $i < j$ with $\sigma(j) < \sigma(i)$. -/
DefinitionDoc LinearAlgebraGame.inversions as "inversions"

/-- If $P$ is nonsingular, so is $P^{-1}$. -/
TheoremDoc LinearAlgebraGame.isUnit_inv_of_isUnit as "isUnit_inv_of_isUnit" in "Eigen"

/-- If $QP = I$ and $S = PTQ$ then `MatSimilar T S` (so $Q = P^{-1}$ need not be computed). -/
TheoremDoc LinearAlgebraGame.matSimilar_of_mul_eq_one as "matSimilar_of_mul_eq_one" in "Eigen"

/-- For nonsingular $P$: $PP^{-1} = I$. -/
TheoremDoc LinearAlgebraGame.mul_inv_of_isUnit as "mul_inv_of_isUnit" in "Eigen"

/-- `swapRows M i j`: the matrix $M$ with rows $i$ and $j$ swapped. -/
DefinitionDoc LinearAlgebraGame.swapRows as "swapRows"

/-- If rows $i$ and $j$ of $M$ are equal, swapping them gives $M$ back. -/
TheoremDoc LinearAlgebraGame.swapRows_eq_self as "swapRows_eq_self" in "Det"

/-- `triArea P Q R`: the signed area $\tfrac12\det(Q - P,\ R - P)$ of the triangle $PQR$ (positive if anticlockwise). -/
DefinitionDoc LinearAlgebraGame.triArea as "triArea"

/-- Hefferon's Theorem Four.II.1.5 (granted from measure theory): the image of a region $s$ under $T$ has area $|\det T|$ times the area of $s$. -/
TheoremDoc LinearAlgebraGame.volume_image_matrix as "volume_image_matrix" in "Det"

/-- $\langle\vec x, \vec y\rangle$ is linearly independent iff $s\vec x + t\vec y = \vec 0$ implies $s = t = 0$. -/
TheoremDoc LinearIndependent.pair_iff as "pair_iff" in "Eigen"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc LinearMap.finrank_eigenspace_le as "finrank_eigenspace_le" in "Eigen"

/-- `Matrix.adjugate A`: Hefferon's adjoint $\operatorname{adj}(A)$, the transpose of the matrix of cofactors. -/
DefinitionDoc Matrix.adjugate as "adjugate"

/-- The $(i,j)$ entry of $\operatorname{adj}(A)$ is the determinant of $A$ with row $j$ replaced by $\vec e_i$. -/
TheoremDoc Matrix.adjugate_apply as "adjugate_apply" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.adjugate_diagonal as "adjugate_diagonal" in "Det"

/-- `Matrix.charpoly A`: Mathlib's characteristic polynomial $\det(xI - A)$ — monic, and equal to Hefferon's $|A - xI|$ times $(-1)^n$. -/
DefinitionDoc Matrix.charpoly as "charpoly"

/-- $\det(xI - A)$ is monic. -/
TheoremDoc Matrix.charpoly_monic as "charpoly_monic" in "Eigen"

/-- $\det(xI - A)$ has degree $n$ (stated with `Fintype.card`). -/
TheoremDoc Matrix.charpoly_natDegree_eq_dim as "charpoly_natDegree_eq_dim" in "Eigen"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.charpoly_units_conj as "charpoly_units_conj" in "Eigen"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.charpoly_units_conj' as "charpoly_units_conj'" in "Eigen"

/-- `Matrix.det M` (or `M.det`): the determinant $|M|$, defined by the permutation expansion. -/
DefinitionDoc Matrix.det as "det"

/-- The determinant of a diagonal matrix is the product of its diagonal entries. -/
TheoremDoc Matrix.det_diagonal as "det_diagonal" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_eq_prod_roots_charpoly as "det_eq_prod_roots_charpoly" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_eq_prod_roots_charpoly_of_splits as "det_eq_prod_roots_charpoly_of_splits" in "Det"

/-- If some column of $A$ is zero then $\det A = 0$. -/
TheoremDoc Matrix.det_eq_zero_of_column_eq_zero as "det_eq_zero_of_column_eq_zero" in "Det"

/-- The $3\times3$ determinant formula (six terms). -/
TheoremDoc Matrix.det_fin_three as "det_fin_three" in "Det"

/-- $\begin{vmatrix} a & b \\ c & d\end{vmatrix} = ad - bc$. -/
TheoremDoc Matrix.det_fin_two_of as "det_fin_two_of" in "Det"

/-- $\det(TS) = \det T\cdot\det S$ (Theorem Four.II.1.4). -/
TheoremDoc Matrix.det_mul as "det_mul" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_mul_comm as "det_mul_comm" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_nonsing_inv as "det_nonsing_inv" in "Det"

/-- $\det I = 1$. -/
TheoremDoc Matrix.det_one as "det_one" in "Det"

/-- $\det T^{\mathsf T} = \det T$ (Theorem Four.I.3.15). -/
TheoremDoc Matrix.det_transpose as "det_transpose" in "Det"

/-- Adding $c$ times row $j$ to row $i \ne j$ leaves the determinant unchanged. -/
TheoremDoc Matrix.det_updateRow_add_smul_self as "det_updateRow_add_smul_self" in "Det"

/-- Multiplying row $i$ by $s$ multiplies the determinant by $s$. -/
TheoremDoc Matrix.det_updateRow_smul as "det_updateRow_smul" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_vandermonde as "det_vandermonde" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_zero_of_column_eq as "det_zero_of_column_eq" in "Det"

/-- `Matrix.diagonal d`: the diagonal matrix with diagonal entries $d_1, \dots, d_n$. -/
DefinitionDoc Matrix.diagonal as "diagonal"

/-- The $(i,i)$ entry of `diagonal d` is $d_i$. -/
TheoremDoc Matrix.diagonal_apply_eq as "diagonal_apply_eq" in "Eigen"

/-- Off-diagonal entries of `diagonal d` are $0$. -/
TheoremDoc Matrix.diagonal_apply_ne as "diagonal_apply_ne" in "Eigen"

/-- `diagonal d = diagonal e ↔ ∀ i, d i = e i`. -/
TheoremDoc Matrix.diagonal_eq_diagonal_iff as "diagonal_eq_diagonal_iff" in "Eigen"

/-- `diagonal d * diagonal e = diagonal (fun i => d i * e i)`. -/
TheoremDoc Matrix.diagonal_mul_diagonal as "diagonal_mul_diagonal" in "Eigen"

/-- `diagonal (c • d) = c • diagonal d`. -/
TheoremDoc Matrix.diagonal_smul as "diagonal_smul" in "Eigen"

/-- Replacing row $i$ of `diagonal d` by $c\,\vec e_i$ gives `diagonal (Function.update d i c)`. -/
TheoremDoc Matrix.diagonal_updateRow_single as "diagonal_updateRow_single" in "Det"

/-- `diagonal (fun _ => 0) = 0`. -/
TheoremDoc Matrix.diagonal_zero as "diagonal_zero" in "Eigen"

/-- $M\vec v = \vec 0$ has a nonzero solution iff $\det M = 0$ (Chapter Three / Lemma Four.I.2.4). -/
TheoremDoc Matrix.exists_mulVec_eq_zero_iff as "exists_mulVec_eq_zero_iff" in "Eigen"

/-- $A(B\vec v) = (AB)\vec v$. -/
TheoremDoc Matrix.mulVec_mulVec as "mulVec_mulVec" in "Eigen"

/-- $A(-\vec v) = -(A\vec v)$. -/
TheoremDoc Matrix.mulVec_neg as "mulVec_neg" in "Eigen"

/-- $M\vec e_j$ is column $j$ of $M$. -/
TheoremDoc Matrix.mulVec_single_one as "mulVec_single_one" in "Eigen"

/-- $A(c\vec v) = c(A\vec v)$. -/
TheoremDoc Matrix.mulVec_smul as "mulVec_smul" in "Eigen"

/-- $A\operatorname{adj}(A) = \det(A)\,I$. -/
TheoremDoc Matrix.mul_adjugate as "mul_adjugate" in "Det"

/-- $(AB)_{ij} = \sum_k A_{ik}B_{kj}$. -/
TheoremDoc Matrix.mul_apply as "mul_apply" in "Eigen"

/-- $(AB)C = A(BC)$. -/
TheoremDoc Matrix.mul_assoc as "mul_assoc" in "Eigen"

/-- $(AB)^{-1} = B^{-1}A^{-1}$. -/
TheoremDoc Matrix.mul_inv_rev as "mul_inv_rev" in "Eigen"

/-- $AI = A$. -/
TheoremDoc Matrix.mul_one as "mul_one" in "Eigen"

/-- $A(cB) = c(AB)$. -/
TheoremDoc Matrix.mul_smul as "mul_smul" in "Eigen"

/-- $A(B - C) = AB - AC$. -/
TheoremDoc Matrix.mul_sub as "mul_sub" in "Eigen"

/-- $A\,0 = 0$. -/
TheoremDoc Matrix.mul_zero as "mul_zero" in "Eigen"

/-- $(-A)\vec v = -(A\vec v)$. -/
TheoremDoc Matrix.neg_mulVec as "neg_mulVec" in "Eigen"

/-- $IA = A$. -/
TheoremDoc Matrix.one_mul as "one_mul" in "Eigen"

/-- $I\vec v = \vec v$. -/
TheoremDoc Matrix.one_mulVec as "one_mulVec" in "Eigen"

/-- A scalar matrix $rI$ commutes with every matrix (when $r$ commutes with everything). -/
TheoremDoc Matrix.scalar_commute as "scalar_commute" in "Eigen"

/-- $(cA)B = c(AB)$. -/
TheoremDoc Matrix.smul_mul as "smul_mul" in "Eigen"

/-- $(cA)\vec v = c(A\vec v)$. -/
TheoremDoc Matrix.smul_mulVec as "smul_mulVec" in "Eigen"

/-- $(A - B)C = AC - BC$. -/
TheoremDoc Matrix.sub_mul as "sub_mul" in "Eigen"

/-- $(A - B)\vec v = A\vec v - B\vec v$. -/
TheoremDoc Matrix.sub_mulVec as "sub_mulVec" in "Eigen"

/-- `Matrix.toLin' T`: the linear map $\vec v \mapsto T\vec v$. -/
DefinitionDoc Matrix.toLin' as "toLin'"

/-- `Matrix.toLin' T v = T *ᵥ v`. -/
TheoremDoc Matrix.toLin'_apply as "toLin'_apply" in "Eigen"

/-- $I^{\mathsf T} = I$. -/
TheoremDoc Matrix.transpose_one as "transpose_one" in "Eigen"

/-- $(cA)^{\mathsf T} = cA^{\mathsf T}$. -/
TheoremDoc Matrix.transpose_smul as "transpose_smul" in "Eigen"

/-- $(A - B)^{\mathsf T} = A^{\mathsf T} - B^{\mathsf T}$. -/
TheoremDoc Matrix.transpose_sub as "transpose_sub" in "Eigen"

/-- Replacing row $i$ of $A$ by row $i$ of $A$ changes nothing. -/
TheoremDoc Matrix.updateRow_eq_self as "updateRow_eq_self" in "Det"

/-- `updateRow` does not change the other rows. -/
TheoremDoc Matrix.updateRow_ne as "updateRow_ne" in "Det"

/-- Row $i$ of `A.updateRow i b` is $b$. -/
TheoremDoc Matrix.updateRow_self as "updateRow_self" in "Det"

/-- $0\,A = 0$. -/
TheoremDoc Matrix.zero_mul as "zero_mul" in "Eigen"

/-- `Module.End.eigenspace f μ`: the eigenspace $V_\mu = \{\vec v : f(\vec v) = \mu\vec v\}$, a subspace. -/
DefinitionDoc Module.End.eigenspace as "eigenspace"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Module.End.eigenvectors_linearIndependent as "eigenvectors_linearIndependent" in "Eigen"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Module.End.eigenvectors_linearIndependent' as "eigenvectors_linearIndependent'" in "Eigen"

/-- $\vec v \in V_\mu \iff f(\vec v) = \mu\vec v$. -/
TheoremDoc Module.End.mem_eigenspace_iff as "mem_eigenspace_iff" in "Eigen"

/-- `Module.finrank ℝ U`: the dimension of $U$. -/
DefinitionDoc Module.finrank as "finrank"

/-- $a \cdot 0 = 0$. -/
TheoremDoc MulZeroClass.mul_zero as "mul_zero" in "Eigen"

/-- $0 \cdot a = 0$. -/
TheoremDoc MulZeroClass.zero_mul as "zero_mul" in "Eigen"

/-- `Pi.single i x j = if j = i then x else 0` (the vector $x\vec e_i$). -/
TheoremDoc Pi.single_apply as "single_apply" in "Eigen"

/-- `C 0 = 0`. -/
TheoremDoc Polynomial.C_0 as "C_0" in "Eigen"

/-- `C (a + b) = C a + C b`. -/
TheoremDoc Polynomial.C_add as "C_add" in "Eigen"

/-- A monic polynomial has leading coefficient $1$. -/
TheoremDoc Polynomial.Monic.coeff_natDegree as "coeff_natDegree" in "Eigen"

/-- $x - a \ne 0$. -/
TheoremDoc Polynomial.X_sub_C_ne_zero as "X_sub_C_ne_zero" in "Eigen"

/-- The coefficients of $a\,p$ are $a$ times those of $p$. -/
TheoremDoc Polynomial.coeff_C_mul as "coeff_C_mul" in "Eigen"

/-- A constant polynomial evaluates to its constant. -/
TheoremDoc Polynomial.eval_C as "eval_C" in "Eigen"

/-- $x$ evaluated at $a$ is $a$. -/
TheoremDoc Polynomial.eval_X as "eval_X" in "Eigen"

/-- Evaluation of a product is the product of evaluations. -/
TheoremDoc Polynomial.eval_prod as "eval_prod" in "Eigen"

/-- Evaluation of a difference is the difference of evaluations. -/
TheoremDoc Polynomial.eval_sub as "eval_sub" in "Eigen"

/-- For $p \ne 0$: $k \le$ `rootMultiplicity a p` iff $(x - a)^k \mid p$. -/
TheoremDoc Polynomial.le_rootMultiplicity_iff as "le_rootMultiplicity_iff" in "Eigen"

/-- `rootMultiplicity a p`: the multiplicity of $a$ as a root of $p$ (the largest $k$ with $(x-a)^k \mid p$). -/
DefinitionDoc Polynomial.rootMultiplicity as "rootMultiplicity"

/-- The multiplicity of $a$ as a root of $x - b$ is $1$ if $a = b$, else $0$. -/
TheoremDoc Polynomial.rootMultiplicity_X_sub_C as "rootMultiplicity_X_sub_C" in "Eigen"

/-- $a$ is a root of $(x - a)^k$ of multiplicity $k$. -/
TheoremDoc Polynomial.rootMultiplicity_X_sub_C_pow as "rootMultiplicity_X_sub_C_pow" in "Eigen"

/-- $a$ is a root of $x - a$ of multiplicity $1$. -/
TheoremDoc Polynomial.rootMultiplicity_X_sub_C_self as "rootMultiplicity_X_sub_C_self" in "Eigen"

/-- For $pq \ne 0$, multiplicities add: $\mathrm{mult}_a(pq) = \mathrm{mult}_a(p) + \mathrm{mult}_a(q)$. -/
TheoremDoc Polynomial.rootMultiplicity_mul as "rootMultiplicity_mul" in "Eigen"

/-- Granted from measure theory: the box between corners $a \le b$ has volume $\prod_i (b_i - a_i)$. -/
TheoremDoc Real.volume_Icc_pi_toReal as "volume_Icc_pi_toReal" in "Det"

/-- $x \in [\{y\}] \iff \exists a,\ a y = x$. -/
TheoremDoc Submodule.mem_span_singleton as "mem_span_singleton" in "Eigen"

/-- `Submodule.span ℝ S`: the span $[S]$ of a set $S$. -/
DefinitionDoc Submodule.span as "span"

/-- $|ab| = |a||b|$. -/
TheoremDoc abs_mul as "abs_mul" in "Det"

/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc conj_pow as "conj_pow" in "Eigen"

/-- For $c \ne 0$: $a = b/c \iff ac = b$. -/
TheoremDoc eq_div_iff as "eq_div_iff" in "Det"

/-- The span of one nonzero vector has dimension $1$. -/
TheoremDoc finrank_span_singleton as "finrank_span_singleton" in "Eigen"

/-- If $c$ is false, `if c then a else b = b`. -/
TheoremDoc if_neg as "if_neg" in "Eigen"

/-- For $a \ne 0$: $a^{-1}a = 1$. -/
TheoremDoc inv_mul_cancel₀ as "inv_mul_cancel₀" in "Eigen"

/-- $1^{-1} = 1$. -/
TheoremDoc inv_one as "inv_one" in "Eigen"

/-- $1$ (in particular $I$) is invertible. -/
TheoremDoc isUnit_one as "isUnit_one" in "Eigen"

/-- If $ab = 1$ then $a \ne 0$. -/
TheoremDoc left_ne_zero_of_mul_eq_one as "left_ne_zero_of_mul_eq_one" in "Det"

/-- A linear map preserves sums: $f(u + v) = f(u) + f(v)$. -/
TheoremDoc map_add as "map_add" in "Eigen"

/-- A ring homomorphism preserves products. -/
TheoremDoc map_mul as "map_mul" in "Eigen"

/-- A ring homomorphism sends $1$ to $1$. -/
TheoremDoc map_one as "map_one" in "Eigen"

/-- A linear map preserves scalar multiples: $f(c v) = c f(v)$. -/
TheoremDoc map_smul as "map_smul" in "Eigen"

/-- A linear map sends $\vec 0$ to $\vec 0$. -/
TheoremDoc map_zero as "map_zero" in "Eigen"

/-- $(ab)c = a(bc)$. -/
TheoremDoc mul_assoc as "mul_assoc" in "Eigen"

/-- $ab = ba$ (real numbers, or any commutative ring). -/
TheoremDoc mul_comm as "mul_comm" in "Eigen"

/-- $ab = 0 \iff a = 0 \lor b = 0$. -/
TheoremDoc mul_eq_zero as "mul_eq_zero" in "Eigen"

/-- If $a \ne 0$ and $b \ne 0$ then $ab \ne 0$. -/
TheoremDoc mul_ne_zero as "mul_ne_zero" in "Eigen"

/-- $a \cdot 1 = a$. -/
TheoremDoc mul_one as "mul_one" in "Eigen"

/-- $a \cdot a = 0 \iff a = 0$. -/
TheoremDoc mul_self_eq_zero as "mul_self_eq_zero" in "Eigen"


/-- $(-r)\cdot v = -(r \cdot v)$. -/
TheoremDoc neg_smul as "neg_smul" in "Eigen"

/-- $-(a - b) = b - a$. -/
TheoremDoc neg_sub as "neg_sub" in "Eigen"

/-- $1 \cdot a = a$. -/
TheoremDoc one_mul as "one_mul" in "Eigen"

/-- For $n \ne 0$: $a^n = 0 \iff a = 0$. -/
TheoremDoc pow_eq_zero_iff as "pow_eq_zero_iff" in "Eigen"

/-- $a^{n+1} = a^n a$. -/
TheoremDoc pow_succ as "pow_succ" in "Eigen"

/-- $a^0 = 1$. -/
TheoremDoc pow_zero as "pow_zero" in "Eigen"

/-- $c\,v = 0 \iff c = 0 \lor v = 0$. -/
TheoremDoc smul_eq_zero as "smul_eq_zero" in "Eigen"

/-- $a(bv) = (ab)v$. -/
TheoremDoc smul_smul as "smul_smul" in "Eigen"

/-- $c\,\vec 0 = \vec 0$. -/
TheoremDoc smul_zero as "smul_zero" in "Eigen"

/-- $a - b = 0 \iff a = b$. -/
TheoremDoc sub_eq_zero as "sub_eq_zero" in "Eigen"

/-- $a - b \ne 0 \iff a \ne b$. -/
TheoremDoc sub_ne_zero as "sub_ne_zero" in "Eigen"

/-- $a - a = 0$. -/
TheoremDoc sub_self as "sub_self" in "Eigen"

/-- $a - 0 = a$. -/
TheoremDoc sub_zero as "sub_zero" in "Eigen"

/-- $0 \le 1$. -/
TheoremDoc zero_le_one as "zero_le_one" in "Det"

/-- $0 \cdot v = \vec 0$. -/
TheoremDoc zero_smul as "zero_smul" in "Eigen"

/-- The dimension of a subspace is at most the dimension of the whole space. -/
TheoremDoc Submodule.finrank_le as "finrank_le" in "Eigen"

/-- $\dim \mathbb R^n = n$: `finrank ℝ (Fin n → ℝ) = n`. -/
TheoremDoc Module.finrank_fin_fun as "finrank_fin_fun" in "Eigen"
