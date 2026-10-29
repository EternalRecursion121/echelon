import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Three, part 2: computing maps (Three.III), matrix operations (Three.IV),
change of basis (Three.V), projection (Three.VI)

Game-local definitions and granted bookkeeping lemmas for the worlds `MatrixOfMap`, `MatrixAlgebra`, `ChangeOfBasis`,
`Projection`.
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

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
