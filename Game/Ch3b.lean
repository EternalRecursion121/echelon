import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Three, part 2: computing maps (Three.III), matrix operations (Three.IV),
change of basis (Three.V), projection (Three.VI)

Game-local definitions, granted bookkeeping lemmas, and every `TheoremDoc` /
`DefinitionDoc` used by the worlds `MatrixOfMap`, `MatrixAlgebra`, `ChangeOfBasis`,
`Projection`. -/

open Matrix

namespace LinearAlgebraGame

/-- Hefferon's Definition Three.III.1.2, column by column: `IsRep B D h H` says that
column `j` of `H` holds the coordinates of `h (B j)` with respect to `D`. -/
def IsRep {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {m n : ℕ} (B : Fin n → V) (D : Fin m → W) (h : V →ₗ[ℝ] W)
    (H : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∀ j, h (B j) = ∑ i, H i j • D i

/-- The standard basis `ℰₙ = ⟨e₁, …, eₙ⟩` of `ℝⁿ`. -/
def stdBasis (n : ℕ) : Fin n → (Fin n → ℝ) := fun i => Pi.single i 1

/-- Upper triangular: every entry strictly below the diagonal is zero. -/
def IsUpperTri {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j, j < i → A i j = 0

/-- Lower triangular: every entry strictly above the diagonal is zero. -/
def IsLowerTri {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ i j, i < j → A i j = 0

/-- Matrix equivalence (Hefferon Def Three.V.2.3): `Ĥ = P H Q` with `P`, `Q` nonsingular. -/
def MatEquiv {m n : ℕ} (H H' : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ (P : Matrix (Fin m) (Fin m) ℝ) (Q : Matrix (Fin n) (Fin n) ℝ),
    IsUnit P.det ∧ IsUnit Q.det ∧ H' = P * H * Q

/-- The `m × n` block matrix with an identity block of size `k` in the top-left corner
and zeros everywhere else. -/
def blockId (m n k : ℕ) : Matrix (Fin m) (Fin n) ℝ :=
  Matrix.of fun i j => if (i : ℕ) = j ∧ (j : ℕ) < k then 1 else 0

/-- Orthogonal projection of `v` into the line spanned by `s` (Hefferon Def Three.VI.1.1):
`proj_[s](v) = (v·s / s·s) • s`. -/
noncomputable def projLine {n : ℕ} (s v : Fin n → ℝ) : Fin n → ℝ := ((v ⬝ᵥ s) / (s ⬝ᵥ s)) • s

/-! ## Granted lemmas -/

theorem stdBasis_apply {n : ℕ} (i l : Fin n) : stdBasis n i l = if l = i then 1 else 0 := by
  simp [stdBasis, Pi.single_apply]

/-- A dot product of a vector with itself is never negative. -/
theorem dot_self_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v :=
  Finset.sum_nonneg fun i _ => mul_self_nonneg (v i)

/-- A square matrix with only the trivial null space has a right inverse
(the dimension count of Chapter Two: one-to-one ⇒ onto). -/
theorem exists_right_inv_of_nonsingular {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ)
    (h : ∀ x, H *ᵥ x = 0 → x = 0) : ∃ G, H * G = 1 := by
  apply mulVec_surjective_iff_exists_right_inverse.mp
  have : Function.Surjective H.mulVecLin := by
    rw [← LinearMap.injective_iff_surjective]
    intro x y hxy
    have := h (x - y) (by rw [mulVec_sub]; exact sub_eq_zero.mpr hxy)
    exact sub_eq_zero.mp this
  exact this

/-- Multiplying by `H` is represented by `H` itself with respect to the standard bases. -/
theorem isRep_mulVecLin {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) :
    IsRep (stdBasis n) (stdBasis m) H.mulVecLin H := by
  intro j
  ext l
  simp [stdBasis, Matrix.mulVec, dotProduct, Pi.single_apply, Finset.sum_apply]

/-- A basis `B` of `ℝⁿ` has a nonsingular change-of-basis matrix `Rep_{B,ℰ}(id)`. -/
theorem exists_cob_from {n : ℕ} (B : Fin n → (Fin n → ℝ)) (hB : LinearIndependent ℝ B) :
    ∃ Q : Matrix (Fin n) (Fin n) ℝ, IsUnit Q.det ∧ IsRep B (stdBasis n) LinearMap.id Q := by
  refine ⟨Matrix.of fun i j => B j i, ?_, ?_⟩
  · rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    exact hB
  · intro j
    ext l
    simp [stdBasis, Pi.single_apply, Finset.sum_apply]

/-- A basis `D` of `ℝᵐ` has a nonsingular change-of-basis matrix `Rep_{ℰ,D}(id)`. -/
theorem exists_cob_to {m : ℕ} (D : Fin m → (Fin m → ℝ)) (hD : LinearIndependent ℝ D) :
    ∃ P : Matrix (Fin m) (Fin m) ℝ, IsUnit P.det ∧ IsRep (stdBasis m) D LinearMap.id P := by
  set M : Matrix (Fin m) (Fin m) ℝ := Matrix.of fun i j => D j i with hM
  have hMu : IsUnit M.det := by
    rw [← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_col_iff_isUnit]
    exact hD
  refine ⟨M⁻¹, (Matrix.isUnit_nonsing_inv_det_iff).mpr hMu, ?_⟩
  intro j
  ext l
  have h1 : (M * M⁻¹) l j = (1 : Matrix (Fin m) (Fin m) ℝ) l j := by
    rw [Matrix.mul_nonsing_inv M hMu]
  rw [Matrix.mul_apply, Matrix.one_apply] at h1
  simp only [LinearMap.id_apply, stdBasis, Pi.single_apply, Finset.sum_apply, Pi.smul_apply,
    smul_eq_mul]
  rw [← h1]
  apply Finset.sum_congr rfl
  intro i _
  simp [hM, mul_comm]

theorem sum_blockId_smul {W : Type*} [AddCommGroup W] [Module ℝ W] {m n k : ℕ}
    (D : Fin m → W) (j : Fin n) : ∑ i, blockId m n k i j • D i =
      if h : (j : ℕ) < k ∧ (j : ℕ) < m then D ⟨j, h.2⟩ else 0 := by
  split_ifs with h
  · rw [Finset.sum_eq_single ⟨j, h.2⟩]
    · simp [blockId, h.1]
    · intro b _ hb
      have : (b : ℕ) ≠ j := fun e => hb (Fin.ext e)
      simp [blockId, this]
    · simp
  · apply Finset.sum_eq_zero
    intro i _
    have : ¬ ((i : ℕ) = j ∧ (j : ℕ) < k) := by
      rintro ⟨e, hk⟩; exact h ⟨hk, e ▸ i.2⟩
    simp [blockId, this]

theorem disjoint_span_of_ker {ι κ : Type*} [Fintype ι] {V W : Type*} [AddCommGroup V]
    [Module ℝ V] [AddCommGroup W] [Module ℝ W] (f : V →ₗ[ℝ] W) (u : ι → V)
    (hu : LinearIndependent ℝ (f ∘ u)) (z : κ → V) (hz : ∀ k, f (z k) = 0) :
    Disjoint (Submodule.span ℝ (Set.range u)) (Submodule.span ℝ (Set.range z)) := by
  rw [Submodule.disjoint_def]
  intro x hx hx'
  obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).mp hx
  have hfx : f (∑ i, c i • u i) = 0 := by
    have : Submodule.span ℝ (Set.range z) ≤ LinearMap.ker f := by
      rw [Submodule.span_le]; rintro _ ⟨k, rfl⟩; exact hz k
    exact this hx'
  rw [map_sum] at hfx
  simp only [map_smul] at hfx
  have hc := Fintype.linearIndependent_iff.mp hu c (by simpa using hfx)
  simp [hc]

/-- **The heart of Theorem Three.V.2.7** (granted): for a matrix `H` of rank `k` there are
bases `B` of `ℝⁿ` and `D` of `ℝᵐ` with respect to which the map `x ↦ H x` is represented by
the block identity: `β₁ ↦ δ₁, …, β_k ↦ δ_k`, and the remaining `β`'s span the null space. -/
theorem exists_bases_blockId {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) :
    ∃ (B : Fin n → (Fin n → ℝ)) (D : Fin m → (Fin m → ℝ)),
      LinearIndependent ℝ B ∧ LinearIndependent ℝ D ∧
      IsRep B D H.mulVecLin (blockId m n H.rank) := by
  classical
  have hkm : H.rank ≤ m := by simpa using H.rank_le_card_height
  obtain ⟨k, hk⟩ : ∃ k, H.rank = k := ⟨_, rfl⟩
  rw [hk] at hkm ⊢
  obtain ⟨f, hf⟩ : ∃ f, H.mulVecLin = f := ⟨_, rfl⟩
  rw [hf]
  have hrange : Module.finrank ℝ (LinearMap.range f) = k := by
    rw [← hk, ← hf]; rfl
  have hrn := LinearMap.finrank_range_add_finrank_ker f
  simp only [Module.finrank_fin_fun, hrange] at hrn
  have hker : Module.finrank ℝ (LinearMap.ker f) = n - k := by omega
  have hkn : k ≤ n := by omega
  obtain ⟨C, hC⟩ := Submodule.exists_isCompl (LinearMap.range f)
  have hCdim : Module.finrank ℝ C = m - k := by
    have := Submodule.finrank_add_eq_of_isCompl hC
    simp at this; omega
  obtain ⟨w⟩ : Nonempty (Module.Basis (Fin k) ℝ (LinearMap.range f)) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ hrange⟩
  obtain ⟨z⟩ : Nonempty (Module.Basis (Fin (n - k)) ℝ (LinearMap.ker f)) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ hker⟩
  obtain ⟨y⟩ : Nonempty (Module.Basis (Fin (m - k)) ℝ C) :=
    ⟨Module.finBasisOfFinrankEq ℝ _ hCdim⟩
  have hpre : ∀ i, ∃ x, f x = (w i : Fin m → ℝ) := fun i => (w i).2
  choose u hu using hpre
  let B' : Fin k ⊕ Fin (n - k) → (Fin n → ℝ) := Sum.elim u (fun l => (z l : Fin n → ℝ))
  let D' : Fin k ⊕ Fin (m - k) → (Fin m → ℝ) :=
    Sum.elim (fun i => (w i : Fin m → ℝ)) (fun l => (y l : Fin m → ℝ))
  have hw : LinearIndependent ℝ (fun i => (w i : Fin m → ℝ)) :=
    w.linearIndependent.map' _ (Submodule.ker_subtype _)
  have hfu : LinearIndependent ℝ (f ∘ u) := by
    have : f ∘ u = fun i => (w i : Fin m → ℝ) := funext hu
    rw [this]; exact hw
  have hB' : LinearIndependent ℝ B' := by
    apply LinearIndependent.sum_type (LinearIndependent.of_comp f hfu)
      (z.linearIndependent.map' _ (Submodule.ker_subtype _))
    exact disjoint_span_of_ker f u hfu _ (fun l => (z l).2)
  have hD' : LinearIndependent ℝ D' := by
    apply LinearIndependent.sum_type hw (y.linearIndependent.map' _ (Submodule.ker_subtype _))
    apply Disjoint.mono _ _ hC.disjoint
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (w i).2
    · rw [Submodule.span_le]; rintro _ ⟨i, rfl⟩; exact (y i).2
  let eN : Fin n ≃ Fin k ⊕ Fin (n - k) :=
    (finCongr (by omega : n = k + (n - k))).trans finSumFinEquiv.symm
  let eM : Fin m ≃ Fin k ⊕ Fin (m - k) :=
    (finCongr (by omega : m = k + (m - k))).trans finSumFinEquiv.symm
  refine ⟨B' ∘ eN, D' ∘ eM, hB'.comp _ eN.injective, hD'.comp _ eM.injective, ?_⟩
  intro j
  rw [sum_blockId_smul]
  by_cases hj : (j : ℕ) < k
  · have hjm : (j : ℕ) < m := by omega
    simp only [hj, hjm, and_self, ↓reduceDIte]
    have e1 : eN j = Sum.inl ⟨j, hj⟩ := by
      simp only [eN, Equiv.trans_apply]
      rw [show (finCongr _ j) = Fin.castAdd (n - k) (⟨j, hj⟩ : Fin k) from Fin.ext rfl]
      exact finSumFinEquiv_symm_apply_castAdd _
    have e2 : eM ⟨j, hjm⟩ = Sum.inl ⟨j, hj⟩ := by
      simp only [eM, Equiv.trans_apply]
      rw [show (finCongr _ (⟨j, hjm⟩ : Fin m)) = Fin.castAdd (m - k) (⟨j, hj⟩ : Fin k)
        from Fin.ext rfl]
      exact finSumFinEquiv_symm_apply_castAdd _
    simp only [Function.comp_apply, e1, e2, B', D', Sum.elim_inl]
    exact hu _
  · have hj' : ¬ ((j : ℕ) < k ∧ (j : ℕ) < m) := fun h => hj h.1
    simp only [hj', ↓reduceDIte]
    have e1 : eN j = Sum.inr ⟨j - k, by omega⟩ := by
      simp only [eN, Equiv.trans_apply]
      rw [show (finCongr _ j) = Fin.natAdd k (⟨j - k, by omega⟩ : Fin (n - k)) from
        Fin.ext (by simp; omega)]
      exact finSumFinEquiv_symm_apply_natAdd _
    simp only [Function.comp_apply, e1, B', Sum.elim_inr]
    exact (z _).2

end LinearAlgebraGame

/-! ## Documentation -/

/-- $\sin^2 x + \cos^2 x = 1$. -/
TheoremDoc Real.sin_sq_add_cos_sq as "sin_sq_add_cos_sq" in "Matrices"
/-- The determinant of a $3\times3$ matrix, written out (rule of Sarrus). -/
TheoremDoc Matrix.det_fin_three as "det_fin_three" in "Matrices"
/-- $(AB)_{ij} = \sum_k A_{ik}B_{kj}$. -/
TheoremDoc Matrix.mul_apply as "mul_apply" in "Matrices"
/-- $\sum_{i<3} f(i) = f(0) + f(1) + f(2)$. -/
TheoremDoc Fin.sum_univ_three as "Fin.sum_univ_three" in "Vectors"
/-- A linear map respects addition: $h(u + v) = h(u) + h(v)$. -/
TheoremDoc map_add as "map_add" in "Maps"
/-- A linear map respects scaling: $h(r\cdot v) = r\cdot h(v)$. -/
TheoremDoc map_smul as "map_smul" in "Maps"
/-- A finite family `v` is linearly independent iff
`∀ g, ∑ i, g i • v i = 0 → ∀ i, g i = 0`. -/
TheoremDoc Fintype.linearIndependent_iff as "linearIndependent_iff" in "Bases"
/-- `(LinearMap.toMatrix B D h) i j = D.repr (h (B j)) i`. -/
TheoremDoc LinearMap.toMatrix_apply as "toMatrix_apply" in "Matrices"
/-- `∑ i, D.repr v i • D i = v`: a vector is the combination of the basis with its
coordinates as coefficients. -/
TheoremDoc Module.Basis.sum_repr as "Basis.sum_repr" in "Bases"
/-- `(g ∘ₗ h) x = g (h x)`. -/
TheoremDoc LinearMap.comp_apply as "comp_apply" in "Maps"
/-- A linear map commutes with finite sums: $h(\sum_i v_i) = \sum_i h(v_i)$. -/
TheoremDoc map_sum as "map_sum" in "Maps"
/-- If two sums have termwise equal summands they are equal:
`(∀ x ∈ s, f x = g x) → s.sum f = s.sum g` (use it as `apply Finset.sum_congr rfl`). -/
TheoremDoc Finset.sum_congr as "Finset.sum_congr" in "Sums"
/-- $r \cdot \sum_i v_i = \sum_i r\cdot v_i$. -/
TheoremDoc Finset.smul_sum as "Finset.smul_sum" in "Sums"
/-- $(\sum_i r_i)\cdot v = \sum_i r_i \cdot v$. -/
TheoremDoc Finset.sum_smul as "Finset.sum_smul" in "Sums"
/-- $\sum_i\sum_j f(i,j) = \sum_j\sum_i f(i,j)$. -/
TheoremDoc Finset.sum_comm as "Finset.sum_comm" in "Sums"
/-- $a \cdot (b \cdot v) = (ab)\cdot v$. -/
TheoremDoc smul_smul as "smul_smul" in "Isomorphisms"
/-- $ab = ba$. -/
TheoremDoc mul_comm as "mul_comm" in "Sums"
/-- `finrank ℝ V = 1 ↔ ∃ v ≠ 0, ∀ w, ∃ c, c • v = w`. -/
TheoremDoc finrank_eq_one_iff' as "finrank_eq_one_iff'" in "Dimension"
/-- Two linear maps are equal if they agree on every vector. -/
TheoremDoc LinearMap.ext as "LinearMap.ext" in "Maps"
/-- Isomorphic spaces have the same dimension: `e.finrank_eq : finrank V = finrank W`. -/
TheoremDoc LinearEquiv.finrank_eq as "LinearEquiv.finrank_eq" in "Dimension"
/-- $\dim \mathcal M_{m\times n} = \#\text{rows}\cdot\#\text{columns}$. -/
TheoremDoc Module.finrank_matrix as "finrank_matrix" in "Dimension"
/-- An independent family has at most $\dim V$ members. -/
TheoremDoc LinearIndependent.fintype_card_le_finrank as "fintype_card_le_finrank" in "Dimension"
/-- A finite family is dependent iff some nontrivial combination is zero:
`¬ LinearIndependent ℝ v ↔ ∃ g, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0`. -/
TheoremDoc Fintype.not_linearIndependent_iff as "not_linearIndependent_iff" in "Bases"
/-- The rank of a diagonal matrix is the number of nonzero diagonal entries. -/
TheoremDoc Matrix.rank_diagonal as "rank_diagonal" in "Matrices"
/-- $\mathrm{diag}(a)\,\mathrm{diag}(b) = \mathrm{diag}(a_ib_i)$. -/
TheoremDoc Matrix.diagonal_mul_diagonal as "diagonal_mul_diagonal" in "Matrices"
/-- The number of elements satisfying `p` is the size of the filtered set. -/
TheoremDoc Fintype.card_subtype as "Fintype.card_subtype" in "Sums"
/-- The size of a filtered set is a sum of 1's and 0's. -/
TheoremDoc Finset.card_filter as "Finset.card_filter" in "Sums"
/-- `range (g ∘ₗ h) = (range h).map g`. -/
TheoremDoc LinearMap.range_comp as "range_comp" in "Maps"
/-- `finrank (U.map g) ≤ finrank U`: a linear image is no bigger. -/
TheoremDoc Submodule.finrank_map_le as "finrank_map_le" in "Dimension"
/-- `range (g ∘ₗ h) ≤ range g`. -/
TheoremDoc LinearMap.range_comp_le_range as "range_comp_le_range" in "Maps"
/-- If `U ≤ W` then `finrank U ≤ finrank W`. -/
TheoremDoc Submodule.finrank_mono as "finrank_mono" in "Dimension"
/-- `IsRep B D h H`: the matrix `H` represents `h` with respect to `B` and `D` (Hefferon Def Three.III.1.2). It unfolds to `∀ j, h (B j) = ∑ i, H i j • D i`: column $j$ of $H$ holds the coordinates of $h(\vec\beta_j)$ with respect to $D$. Prove it with `intro j`. -/
DefinitionDoc LinearAlgebraGame.IsRep as "IsRep (Rep_{B,D})"
/-- `stdBasis n` is the standard basis $\mathcal E_n = \langle\vec e_1,\dots,\vec e_n\rangle$ of $\mathbb R^n$: `stdBasis n i = Pi.single i 1`. Unfold with `simp [stdBasis, Pi.single_apply]`. -/
DefinitionDoc LinearAlgebraGame.stdBasis as "stdBasis (ℰₙ)"
/-- `IsUpperTri A` : `∀ i j, j < i → A i j = 0` (all entries below the diagonal are zero). -/
DefinitionDoc LinearAlgebraGame.IsUpperTri as "IsUpperTri"
/-- `IsLowerTri A` : `∀ i j, i < j → A i j = 0` (all entries above the diagonal are zero). -/
DefinitionDoc LinearAlgebraGame.IsLowerTri as "IsLowerTri"
/-- `MatEquiv H H'` : `∃ P Q, IsUnit P.det ∧ IsUnit Q.det ∧ H' = P * H * Q` — matrix equivalence (Hefferon Def Three.V.2.3). Take it apart with `obtain ⟨P, Q, hP, hQ, h⟩ := …`. -/
DefinitionDoc LinearAlgebraGame.MatEquiv as "MatEquiv"
/-- `blockId m n k` is the $m\times n$ matrix $\begin{pmatrix}I_k&0\\0&0\end{pmatrix}$: entry $(i,j)$ is $1$ if $i = j < k$ and $0$ otherwise. -/
DefinitionDoc LinearAlgebraGame.blockId as "blockId"
/-- `projLine s v` $= \dfrac{\vec v\cdot\vec s}{\vec s\cdot\vec s}\,\vec s$, the orthogonal projection of $\vec v$ into the line spanned by $\vec s$. `rw [projLine]` unfolds it. -/
DefinitionDoc LinearAlgebraGame.projLine as "projLine"
/-- `Aᵀ` is the transpose: `Aᵀ i j = A j i` (`Matrix.transpose_apply`). -/
DefinitionDoc Matrix.transpose as "ᵀ (transpose)"
/-- `LinearMap.toMatrix B D h` is Mathlib's $\mathrm{Rep}_{B,D}(h)$ for bases `B`, `D`; it is a linear isomorphism `(V →ₗ[ℝ] W) ≃ₗ[ℝ] Matrix …`. -/
DefinitionDoc LinearMap.toMatrix as "LinearMap.toMatrix"
/-- `LinearMap.toMatrix'` is $\mathrm{Rep}_{\mathcal E_n,\mathcal E_m}$: the isomorphism between linear maps $\mathbb R^n\to\mathbb R^m$ and $m\times n$ matrices. -/
DefinitionDoc LinearMap.toMatrix' as "LinearMap.toMatrix'"
/-- `Matrix.diagonal d` is the diagonal matrix with diagonal entries `d i`. -/
DefinitionDoc Matrix.diagonal as "Matrix.diagonal"
/-- `A.rank` is the rank of the matrix `A`: the dimension of its column space, i.e. of the range of $\vec x\mapsto A\vec x$. -/
DefinitionDoc Matrix.rank as "Matrix.rank"
/-- `isRep_toMatrix B D h : IsRep B D h (LinearMap.toMatrix B D h)` — Mathlib's matrix of a map is $\mathrm{Rep}_{B,D}(h)$. -/
TheoremDoc LinearAlgebraGame.isRep_toMatrix as "isRep_toMatrix" in "Matrices"
/-- `isRep_comp hH hG : IsRep B D (g ∘ₗ h) (G * H)` from `hH : IsRep B C h H` and `hG : IsRep C D g G` — composition is the matrix product (Thm Three.IV.2.7). -/
TheoremDoc LinearAlgebraGame.isRep_comp as "isRep_comp" in "Matrices"
/-- `transpose_mul' G H : (G * H)ᵀ = Hᵀ * Gᵀ` (Sheet 7 Q7a). -/
TheoremDoc LinearAlgebraGame.transpose_mul' as "transpose_mul'" in "Matrices"
/-- `inv_left_eq_inv_right (hG : G * H = 1) (hG' : H * G' = 1) : G = G'` — a left inverse equals a right inverse (Lemma Three.IV.4.2). -/
TheoremDoc LinearAlgebraGame.inv_left_eq_inv_right as "inv_left_eq_inv_right" in "Matrices"
/-- `inv_transpose' T hT : (Tᵀ)⁻¹ = (T⁻¹)ᵀ` for invertible `T` (Sheet 7 Q7c). -/
TheoremDoc LinearAlgebraGame.inv_transpose' as "inv_transpose'" in "Matrices"
/-- **Granted.** `exists_right_inv_of_nonsingular H h : ∃ G, H * G = 1` when `h : ∀ x, H *ᵥ x = 0 → x = 0`. (For a square matrix, one-to-one implies onto — the dimension count of Chapter Two — and then each $\vec e_j$ has a preimage.) -/
TheoremDoc LinearAlgebraGame.exists_right_inv_of_nonsingular as "exists_right_inv_of_nonsingular" in "Matrices"
/-- `isRep_id_std_iff B H : IsRep B (stdBasis n) LinearMap.id H ↔ ∀ i j, H i j = B j i` — $\mathrm{Rep}_{B,\mathcal E}(\mathrm{id})$ has the vectors of $B$ as columns. -/
TheoremDoc LinearAlgebraGame.isRep_id_std_iff as "isRep_id_std_iff" in "Change of basis"
/-- `isRep_unique hD hH hH' : H = H'` when `D` is linearly independent and both `H`, `H'` represent `h` with respect to `B`, `D`. -/
TheoremDoc LinearAlgebraGame.isRep_unique as "isRep_unique" in "Change of basis"
/-- `rank_eq_of_matEquiv H H' h : H.rank = H'.rank` for `h : MatEquiv H H'`. -/
TheoremDoc LinearAlgebraGame.rank_eq_of_matEquiv as "rank_eq_of_matEquiv" in "Change of basis"
/-- **Granted** (the heart of Thm Three.V.2.7). `exists_bases_blockId H : ∃ B D, LinearIndependent ℝ B ∧ LinearIndependent ℝ D ∧ IsRep B D H.mulVecLin (blockId m n H.rank)` — bases in which $\vec x\mapsto H\vec x$ is the block identity. -/
TheoremDoc LinearAlgebraGame.exists_bases_blockId as "exists_bases_blockId" in "Change of basis"
/-- **Granted.** `exists_cob_from B hB : ∃ Q, IsUnit Q.det ∧ IsRep B (stdBasis n) LinearMap.id Q` for an independent family `B` of $n$ vectors in $\mathbb R^n$ (take the vectors as columns). -/
TheoremDoc LinearAlgebraGame.exists_cob_from as "exists_cob_from" in "Change of basis"
/-- **Granted.** `exists_cob_to D hD : ∃ P, IsUnit P.det ∧ IsRep (stdBasis m) D LinearMap.id P` for an independent family `D` of $m$ vectors in $\mathbb R^m$ (the inverse of the matrix with columns $D$). -/
TheoremDoc LinearAlgebraGame.exists_cob_to as "exists_cob_to" in "Change of basis"
/-- **Granted.** `isRep_mulVecLin H : IsRep (stdBasis n) (stdBasis m) H.mulVecLin H` — with respect to the standard bases, $\vec x\mapsto H\vec x$ is represented by $H$. -/
TheoremDoc LinearAlgebraGame.isRep_mulVecLin as "isRep_mulVecLin" in "Change of basis"
/-- `projLine_orth s v hs : (v - projLine s v) ⬝ᵥ s = 0` for `hs : s ≠ 0`. -/
TheoremDoc LinearAlgebraGame.projLine_orth as "projLine_orth" in "Projection"
/-- **Granted.** `dot_self_nonneg v : 0 ≤ v ⬝ᵥ v`. -/
TheoremDoc LinearAlgebraGame.dot_self_nonneg as "dot_self_nonneg" in "Projection"
/-- `linearIndependent_of_orthogonal v h0 horth : LinearIndependent ℝ v` for nonzero (`h0`), mutually orthogonal (`horth`) vectors (Thm Three.VI.2.2). -/
TheoremDoc LinearAlgebraGame.linearIndependent_of_orthogonal as "linearIndependent_of_orthogonal" in "Projection"
/-- `Pi.single i x j = if j = i then x else 0`. -/
TheoremDoc Pi.single_apply as "Pi.single_apply" in "Vectors"
/-- Component $j$ of a sum of vectors is the sum of the components: `(∑ c ∈ s, g c) j = ∑ c ∈ s, g c j`. -/
TheoremDoc Finset.sum_apply as "Finset.sum_apply" in "Sums"
/-- `congrFun h a : f a = g a` from `h : f = g`; for vectors, `congrFun h i` takes component `i` of a vector equation. -/
TheoremDoc congrFun as "congrFun" in "Vectors"
/-- `congrArg f h : f a = f b` from `h : a = b` — apply the same function to both sides. -/
TheoremDoc congrArg as "congrArg" in "Vectors"
/-- `f ∘ₗ id = f`. -/
TheoremDoc LinearMap.comp_id as "LinearMap.comp_id" in "Maps"
/-- `id ∘ₗ f = f`. -/
TheoremDoc LinearMap.id_comp as "LinearMap.id_comp" in "Maps"
/-- $(a - b)\cdot v = a\cdot v - b\cdot v$. -/
TheoremDoc sub_smul as "sub_smul" in "Vector spaces"
/-- $\sum_i (f_i - g_i) = \sum_i f_i - \sum_i g_i$. -/
TheoremDoc Finset.sum_sub_distrib as "Finset.sum_sub_distrib" in "Sums"
/-- $a - a = 0$. -/
TheoremDoc sub_self as "sub_self" in "Maps"
/-- `Matrix.rank_mul_eq_left_of_isUnit_det A B hA : (B * A).rank = B.rank` when `hA : IsUnit A.det` — multiplying on the right by a nonsingular matrix keeps the rank. -/
TheoremDoc Matrix.rank_mul_eq_left_of_isUnit_det as "rank_mul_eq_left_of_isUnit_det" in "Change of basis"
/-- `Matrix.rank_mul_eq_right_of_isUnit_det A B hA : (A * B).rank = B.rank` when `hA : IsUnit A.det` — multiplying on the left by a nonsingular matrix keeps the rank. -/
TheoremDoc Matrix.rank_mul_eq_right_of_isUnit_det as "rank_mul_eq_right_of_isUnit_det" in "Change of basis"
/-- Mathlib's version of the normal form theorem (square matrices); disabled in the boss. -/
TheoremDoc Matrix.exists_rank_normal_form as "exists_rank_normal_form" in "Change of basis"
/-- If every term is zero, the sum is zero: `(∀ i ∈ s, f i = 0) → ∑ i ∈ s, f i = 0`. -/
TheoremDoc Finset.sum_eq_zero as "Finset.sum_eq_zero" in "Sums"
/-- $0 \cdot a = 0$ (type `zero_mul`). -/
TheoremDoc MulZeroClass.zero_mul as "zero_mul" in "Sums"
/-- $a \cdot 0 = 0$ (type `mul_zero`). -/
TheoremDoc MulZeroClass.mul_zero as "mul_zero" in "Sums"
/-- Mathlib: block-triangular matrices are closed under products. Disabled where it is the exercise. -/
TheoremDoc Matrix.BlockTriangular.mul as "BlockTriangular.mul" in "Matrices"
/-- Mathlib lemma about block triangular matrices; disabled where it would shortcut the exercise. -/
TheoremDoc Matrix.upper_two_blockTriangular as "upper_two_blockTriangular" in "Matrices"
/-- `Aᵀ i j = A j i`. -/
TheoremDoc Matrix.transpose_apply as "transpose_apply" in "Matrices"
/-- Mathlib's $(AB)^{\mathsf T} = B^{\mathsf T}A^{\mathsf T}$ — Sheet 7 Q7a, disabled until you prove it (as `transpose_mul'`). -/
TheoremDoc Matrix.transpose_mul as "Matrix.transpose_mul" in "Matrices"
/-- $(A^{\mathsf T})^{\mathsf T} = A$. -/
TheoremDoc Matrix.transpose_transpose as "transpose_transpose" in "Matrices"
/-- $AI = A$. -/
TheoremDoc Matrix.mul_one as "Matrix.mul_one" in "Matrices"
/-- $IA = A$. -/
TheoremDoc Matrix.one_mul as "Matrix.one_mul" in "Matrices"
/-- $(AB)C = A(BC)$. -/
TheoremDoc Matrix.mul_assoc as "Matrix.mul_assoc" in "Matrices"
/-- Mathlib's general form of Lemma Three.IV.4.2; disabled where it is the exercise. -/
TheoremDoc left_inv_eq_right_inv as "left_inv_eq_right_inv" in "Matrices"
/-- Mathlib: a left inverse is the inverse (groups). Disabled where it is the exercise. -/
TheoremDoc inv_eq_of_mul_eq_one_left as "inv_eq_of_mul_eq_one_left" in "Matrices"
/-- `Matrix.inv_eq_left_inv (h : B * A = 1) : A⁻¹ = B` — a left inverse of a square matrix is its inverse. -/
TheoremDoc Matrix.inv_eq_left_inv as "inv_eq_left_inv" in "Matrices"
/-- `Matrix.inv_eq_right_inv (h : A * B = 1) : A⁻¹ = B`. -/
TheoremDoc Matrix.inv_eq_right_inv as "inv_eq_right_inv" in "Matrices"
/-- `a * b = 1 ↔ b * a = 1` for matrices (one-sided inverses are two-sided). Disabled in the boss, which proves it. -/
TheoremDoc mul_eq_one_comm as "mul_eq_one_comm" in "Matrices"
/-- `Matrix.nonsing_inv_mul A h : A⁻¹ * A = 1` for `h : IsUnit A.det`. -/
TheoremDoc Matrix.nonsing_inv_mul as "nonsing_inv_mul" in "Matrices"
/-- `Matrix.mul_nonsing_inv A h : A * A⁻¹ = 1` for `h : IsUnit A.det`. -/
TheoremDoc Matrix.mul_nonsing_inv as "mul_nonsing_inv" in "Matrices"
/-- $A\cdot 0 = 0$. -/
TheoremDoc Matrix.mul_zero as "Matrix.mul_zero" in "Matrices"
/-- $a^0 = 1$. -/
TheoremDoc pow_zero as "pow_zero" in "Matrices"
/-- $a^{n+1} = a^n a$. -/
TheoremDoc pow_succ as "pow_succ" in "Matrices"
/-- $a^{n+1} = a\,a^n$. -/
TheoremDoc pow_succ' as "pow_succ'" in "Matrices"
/-- Mathlib's $(A^{-1})^n = (A^n)^{-1}$ — Sheet 7 Q5 itself; disabled there. -/
TheoremDoc Matrix.inv_pow' as "inv_pow'" in "Matrices"
/-- $(a^{-1})^n = (a^n)^{-1}$; disabled where it is the exercise. -/
TheoremDoc inv_pow as "inv_pow" in "Matrices"
/-- Integer-power version of `inv_pow`; disabled where it is the exercise. -/
TheoremDoc Matrix.inv_zpow as "inv_zpow" in "Matrices"
/-- $I^{\mathsf T} = I$. -/
TheoremDoc Matrix.transpose_one as "transpose_one" in "Matrices"
/-- Mathlib's $(A^{-1})^{\mathsf T} = (A^{\mathsf T})^{-1}$ — Sheet 7 Q7c; disabled there. -/
TheoremDoc Matrix.transpose_nonsing_inv as "transpose_nonsing_inv" in "Matrices"
/-- $A(B\vec v) = (AB)\vec v$: `A *ᵥ (B *ᵥ v) = (A * B) *ᵥ v`. -/
TheoremDoc Matrix.mulVec_mulVec as "mulVec_mulVec" in "Matrices"
/-- $I\vec v = \vec v$. -/
TheoremDoc Matrix.one_mulVec as "one_mulVec" in "Matrices"
/-- $A(c\vec v) = c\,(A\vec v)$. -/
TheoremDoc Matrix.mulVec_smul as "mulVec_smul" in "Matrices"
/-- $A\vec 0 = \vec 0$. -/
TheoremDoc Matrix.mulVec_zero as "mulVec_zero" in "Matrices"
/-- Mathlib: $\vec x\mapsto A\vec x$ is one-to-one iff $A$ is invertible — the boss itself; disabled there. -/
TheoremDoc Matrix.mulVec_injective_iff_isUnit as "mulVec_injective_iff_isUnit" in "Matrices"
/-- Mathlib: $\vec x\mapsto A\vec x$ is onto iff $A$ has a right inverse; disabled in the boss. -/
TheoremDoc Matrix.mulVec_surjective_iff_exists_right_inverse as "mulVec_surjective_iff_exists_right_inverse" in "Matrices"
/-- `dotProduct_self_eq_zero : v ⬝ᵥ v = 0 ↔ v = 0` (over ℝ). -/
TheoremDoc dotProduct_self_eq_zero as "dotProduct_self_eq_zero" in "Projection"
/-- $(\vec u - \vec v)\cdot\vec w = \vec u\cdot\vec w - \vec v\cdot\vec w$. -/
TheoremDoc sub_dotProduct as "sub_dotProduct" in "Projection"
/-- $(c\vec v)\cdot\vec w = c\,(\vec v\cdot\vec w)$. -/
TheoremDoc smul_dotProduct as "smul_dotProduct" in "Projection"
/-- $\vec v\cdot(c\vec w) = c\,(\vec v\cdot\vec w)$. -/
TheoremDoc dotProduct_smul as "dotProduct_smul" in "Projection"
/-- $(\vec u + \vec v)\cdot\vec w = \vec u\cdot\vec w + \vec v\cdot\vec w$. -/
TheoremDoc add_dotProduct as "add_dotProduct" in "Projection"
/-- $\vec u\cdot(\vec v + \vec w) = \vec u\cdot\vec v + \vec u\cdot\vec w$. -/
TheoremDoc dotProduct_add as "dotProduct_add" in "Projection"
/-- $\vec v\cdot\vec w = \vec w\cdot\vec v$. -/
TheoremDoc dotProduct_comm as "dotProduct_comm" in "Projection"
/-- $(\sum_i \vec u_i)\cdot\vec v = \sum_i \vec u_i\cdot\vec v$. -/
TheoremDoc sum_dotProduct as "sum_dotProduct" in "Projection"
/-- $\vec 0\cdot\vec v = 0$. -/
TheoremDoc zero_dotProduct as "zero_dotProduct" in "Projection"
/-- For real numbers, `a • b = a * b`. -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Sums"
/-- `div_mul_cancel₀ a h : a / b * b = a` for `h : b ≠ 0`. -/
TheoremDoc div_mul_cancel₀ as "div_mul_cancel₀" in "Projection"
/-- If $a \le b$ then $\sqrt a \le \sqrt b$. -/
TheoremDoc Real.sqrt_le_sqrt as "Real.sqrt_le_sqrt" in "Projection"
/-- `Real.sqrt_mul_self (h : 0 ≤ a) : √(a * a) = a`. -/
TheoremDoc Real.sqrt_mul_self as "Real.sqrt_mul_self" in "Projection"
/-- $c\cdot\vec 0 = \vec 0$ (also $c\cdot 0 = 0$ for numbers). -/
TheoremDoc smul_zero as "smul_zero" in "Maps"
/-- $a + (b - a) = b$. -/
TheoremDoc add_sub_cancel as "add_sub_cancel" in "Projection"
/-- `Finset.sum_eq_single i` : if every term other than the $i$-th is zero (and $i$ is in range), the sum equals its $i$-th term. Leaves those two side conditions as goals. -/
TheoremDoc Finset.sum_eq_single as "Finset.sum_eq_single" in "Sums"
/-- $ab = 0 \iff a = 0 \lor b = 0$. -/
TheoremDoc mul_eq_zero as "mul_eq_zero" in "Sums"
/-- Every element lies in `Finset.univ`. -/
TheoremDoc Finset.mem_univ as "Finset.mem_univ" in "Sums"
/-- $a \le b$ and $b \le a$ give $a = b$ (also for subspaces). -/
TheoremDoc le_antisymm as "le_antisymm" in "Subspaces"
/-- `span S ≤ W ↔ S ⊆ W`: a span is inside a subspace iff its generators are. -/
TheoremDoc Submodule.span_le as "span_le" in "Subspaces"
/-- `insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t`; splits `{a, b, …} ⊆ t`. -/
TheoremDoc Set.insert_subset_iff as "insert_subset_iff" in "Subspaces"
/-- `{a} ⊆ t ↔ a ∈ t`. -/
TheoremDoc Set.singleton_subset_iff as "singleton_subset_iff" in "Subspaces"
/-- Every generator lies in the span: `x ∈ S → x ∈ span S`. -/
TheoremDoc Submodule.subset_span as "subset_span" in "Subspaces"
/-- Subspaces are closed under addition. -/
TheoremDoc Submodule.add_mem as "Submodule.add_mem" in "Subspaces"
/-- Subspaces are closed under subtraction. -/
TheoremDoc Submodule.sub_mem as "Submodule.sub_mem" in "Subspaces"
/-- Subspaces are closed under scalar multiplication. -/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "Subspaces"
/-- $\sum_{i<4} f(i) = f(0) + f(1) + f(2) + f(3)$. -/
TheoremDoc Fin.sum_univ_four as "Fin.sum_univ_four" in "Vectors"
/-- $a / 1 = a$. -/
TheoremDoc div_one as "div_one" in "Sums"
/-- $1\cdot\vec v = \vec v$. -/
TheoremDoc one_smul as "one_smul" in "Vector spaces"
/-- $0 / a = 0$. -/
TheoremDoc zero_div as "zero_div" in "Sums"
/-- $0\cdot\vec v = \vec 0$. -/
TheoremDoc zero_smul as "zero_smul" in "Vector spaces"
/-- $a - 0 = a$. -/
TheoremDoc sub_zero as "sub_zero" in "Sums"
/-- $a - b - c = a - c - b$. -/
TheoremDoc sub_right_comm as "sub_right_comm" in "Projection"
/-- Mathlib's Gram–Schmidt orthogonality; disabled in the boss. -/
TheoremDoc InnerProductSpace.gramSchmidt_orthogonal as "gramSchmidt_orthogonal" in "Projection"
/-- Mathlib's Gram–Schmidt span equality; disabled in the boss. -/
TheoremDoc InnerProductSpace.span_gramSchmidt as "span_gramSchmidt" in "Projection"
