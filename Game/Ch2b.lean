import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Two, part 2 (Hefferon Two.III)

Game-local definitions and granted bookkeeping lemmas for the worlds `BasisDim` ("Basis & Dimension") and `Dimension` ("Dimension & Rank").
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

namespace LinearAlgebraGame

open Matrix

/-! ## Game-local definitions -/

/-- `IsBasisOf v W`: the family `v` is a basis of the subspace `W`, i.e. it is linearly
independent and spans `W`. (Hefferon: a basis is a *sequence*; a family `v : ι → V` is a
sequence indexed by `ι`.) -/
def IsBasisOf {ι V : Type*} [AddCommGroup V] [Module ℝ V] (v : ι → V) (W : Submodule ℝ V) :
    Prop :=
  LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = W

/-- Dimension = size of a basis (Hefferon Def 2.5 with Thm 2.4). -/
theorem IsBasisOf.finrank_eq {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    {v : ι → V} {W : Submodule ℝ V} (h : IsBasisOf v W) :
    Module.finrank ℝ W = Fintype.card ι := by
  rw [← h.2, finrank_span_eq_card h.1]

/-- `p.HasDegree d`: the polynomial `p ∈ 𝒫ₙ` has degree exactly `d` — its coefficient of
$x^d$ is nonzero and all higher coefficients vanish. -/
def Poly.HasDegree {n : ℕ} (p : Poly n) (d : Fin (n + 1)) : Prop :=
  p d ≠ 0 ∧ ∀ i, d < i → p i = 0

theorem Poly.evalAt_apply {n : ℕ} (x : ℝ) (p : Poly n) : Poly.evalAt x p = p.eval x := rfl

/-- The subspace of symmetric $n \times n$ matrices: $A^T = A$. -/
def symMat (n : ℕ) : Submodule ℝ (Matrix (Fin n) (Fin n) ℝ) where
  carrier := {A | Aᵀ = A}
  add_mem' := by intro a b ha hb; simp_all [Matrix.transpose_add]
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all [Matrix.transpose_smul]

theorem mem_symMat {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : A ∈ symMat n ↔ Aᵀ = A := Iff.rfl

/-- The augmented matrix $[A \mid b]$: the column $b$ appended after the columns of $A$. -/
def augment {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    Matrix (Fin m) (Fin (n + 1)) ℝ :=
  Matrix.of fun i => Fin.snoc (A i) (b i)

/-- The columns of $[A \mid b]$ are the columns of $A$ followed by $b$. -/
theorem augment_col {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    (augment A b).col = Fin.snoc A.col b := by
  funext j i
  refine Fin.lastCases ?_ (fun k => ?_) j
  · simp only [augment, Matrix.col_apply, Matrix.of_apply, Fin.snoc_last]
  · simp only [augment, Matrix.col_apply, Matrix.of_apply, Fin.snoc_castSucc]

/-- Independence of a concatenated sequence $\langle f, g\rangle$, written out. -/
theorem linearIndependent_sum_elim_iff {ι κ V : Type*} [Fintype ι] [Fintype κ]
    [AddCommGroup V] [Module ℝ V] (f : ι → V) (g : κ → V) :
    LinearIndependent ℝ (Sum.elim f g) ↔
      ∀ (a : ι → ℝ) (b : κ → ℝ), ∑ i, a i • f i + ∑ j, b j • g j = 0 → a = 0 ∧ b = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h a b hab
    have key := h (Sum.elim a b) (by simpa [Fintype.sum_sum_type] using hab)
    exact ⟨funext fun i => key (Sum.inl i), funext fun j => key (Sum.inr j)⟩
  · intro h c hc x
    have hc' : ∑ i, c (Sum.inl i) • f i + ∑ j, c (Sum.inr j) • g j = 0 := by
      simpa [Fintype.sum_sum_type] using hc
    obtain ⟨ha, hb⟩ := h _ _ hc'
    rcases x with i | j
    · exact congrFun ha i
    · exact congrFun hb j

/-- Independence of a concatenated sequence $\langle f, g, h\rangle$, written out. -/
theorem linearIndependent_sum_elim₃_iff {ι κ τ V : Type*} [Fintype ι] [Fintype κ] [Fintype τ]
    [AddCommGroup V] [Module ℝ V] (f : ι → V) (g : κ → V) (h : τ → V) :
    LinearIndependent ℝ (Sum.elim (Sum.elim f g) h) ↔
      ∀ (a : ι → ℝ) (b : κ → ℝ) (c : τ → ℝ),
        ∑ i, a i • f i + ∑ j, b j • g j + ∑ l, c l • h l = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [linearIndependent_sum_elim_iff]
  constructor
  · intro H a b c habc
    have key := H (Sum.elim a b) c (by simpa [Fintype.sum_sum_type] using habc)
    refine ⟨funext fun i => ?_, funext fun j => ?_, key.2⟩
    · exact congrFun key.1 (Sum.inl i)
    · exact congrFun key.1 (Sum.inr j)
  · intro H ab c habc
    have habc' : ∑ i, ab (Sum.inl i) • f i + ∑ j, ab (Sum.inr j) • g j + ∑ l, c l • h l = 0 := by
      simpa [Fintype.sum_sum_type] using habc
    obtain ⟨ha, hb, hc⟩ := H _ _ _ habc'
    refine ⟨funext fun x => ?_, hc⟩
    rcases x with i | j
    · exact congrFun ha i
    · exact congrFun hb j

/-- The span of a concatenated sequence is the sum of the spans. -/
theorem span_range_sum_elim {ι κ V : Type*} [AddCommGroup V] [Module ℝ V] (f : ι → V)
    (g : κ → V) :
    Submodule.span ℝ (Set.range (Sum.elim f g)) =
      Submodule.span ℝ (Set.range f) ⊔ Submodule.span ℝ (Set.range g) := by
  rw [Set.Sum.elim_range, Submodule.span_union]

/-- Sheet 6 Q1(a): $W_1 = \left\{\begin{pmatrix}0&0\\c&d\end{pmatrix}\right\}$, i.e. the
first row is zero. -/
def S6W₁ : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) where
  carrier := {A | A 0 0 = 0 ∧ A 0 1 = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all

/-- Sheet 6 Q1(a): $W_2 = \left\{\begin{pmatrix}0&b\\c&0\end{pmatrix}\right\}$, i.e. the
diagonal is zero. -/
def S6W₂ : Submodule ℝ (Matrix (Fin 2) (Fin 2) ℝ) where
  carrier := {A | A 0 0 = 0 ∧ A 1 1 = 0}
  add_mem' := by intro a b ha hb; simp_all
  zero_mem' := by simp
  smul_mem' := by intro c a ha; simp_all

theorem mem_S6W₁ (A : Matrix (Fin 2) (Fin 2) ℝ) : A ∈ S6W₁ ↔ A 0 0 = 0 ∧ A 0 1 = 0 := Iff.rfl
theorem mem_S6W₂ (A : Matrix (Fin 2) (Fin 2) ℝ) : A ∈ S6W₂ ↔ A 0 0 = 0 ∧ A 1 1 = 0 := Iff.rfl

/-- `coordSpan S`: the span of the standard basis vectors $e_i$, $i \in S$, in $\mathbb R^n$. -/
def coordSpan {n : ℕ} (S : Finset (Fin n)) : Submodule ℝ (Fin n → ℝ) :=
  Submodule.span ℝ ((fun i => Pi.single i (1 : ℝ)) '' (S : Set (Fin n)))

/-- $\dim \operatorname{coordSpan} S = |S|$. -/
theorem finrank_coordSpan {n : ℕ} (S : Finset (Fin n)) :
    Module.finrank ℝ (coordSpan S) = S.card := by
  let f : ↥(S : Set (Fin n)) → Fin n := fun i => i.1
  have hf : Function.Injective f := fun a b h => Subtype.ext h
  have hli := (Pi.basisFun ℝ (Fin n)).linearIndependent.comp f hf
  have hr : (fun i => Pi.single i (1 : ℝ)) '' (S : Set (Fin n)) =
      Set.range ((Pi.basisFun ℝ (Fin n)) ∘ f) := by
    ext v; simp [Pi.basisFun_apply, f]
  rw [coordSpan, hr, finrank_span_eq_card hli]
  simp

/-- $\operatorname{coordSpan} S + \operatorname{coordSpan} T = \operatorname{coordSpan} (S \cup T)$. -/
theorem coordSpan_sup {n : ℕ} (S T : Finset (Fin n)) :
    coordSpan S ⊔ coordSpan T = coordSpan (S ∪ T) := by
  rw [coordSpan, coordSpan, coordSpan, ← Submodule.span_union, Finset.coe_union, Set.image_union]

/-- A one-dimensional subspace is a line: it contains a nonzero `u` of which every member is a
multiple. (Vector form of `finrank_eq_one_iff'`, without subtypes.) -/
theorem exists_line_of_finrank_eq_one {V : Type*} [AddCommGroup V] [Module ℝ V]
    {W : Submodule ℝ V} (h : Module.finrank ℝ W = 1) :
    ∃ u, u ∈ W ∧ u ≠ 0 ∧ ∀ w ∈ W, ∃ c : ℝ, c • u = w := by
  obtain ⟨u, hu0, hu⟩ := finrank_eq_one_iff'.mp h
  refine ⟨u, u.2, fun h0 => hu0 (Subtype.ext h0), fun w hw => ?_⟩
  obtain ⟨c, hc⟩ := hu ⟨w, hw⟩
  exact ⟨c, congrArg Subtype.val hc⟩

/-- A line through `u` has dimension at most 1. -/
theorem finrank_span_singleton_le_one {V : Type*} [AddCommGroup V] [Module ℝ V] (u : V) :
    Module.finrank ℝ (Submodule.span ℝ {u}) ≤ 1 := by
  have := finrank_span_le_card (R := ℝ) ({u} : Set V)
  simpa using this

/-- $A\vec x$ is the combination of the columns of $A$ with coefficients $x_j$. -/
theorem mulVec_eq_sum_col {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (x : Fin n → ℝ) :
    A *ᵥ x = ∑ j, x j • A.col j := by
  ext i
  simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]

/-- $\vec b$ is in the column space of $A$ iff $A\vec x = \vec b$ has a solution. -/
theorem mem_span_cols_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (b : Fin m → ℝ) :
    b ∈ Submodule.span ℝ (Set.range A.col) ↔ ∃ x, A *ᵥ x = b := by
  rw [Submodule.mem_span_range_iff_exists_fun]
  simp only [mulVec_eq_sum_col]

theorem col_neg {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (-A).col j = -A.col j := rfl
theorem col_smul {m n : ℕ} (k : ℝ) (A : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (k • A).col j = k • A.col j := rfl
theorem col_add {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) (j : Fin n) :
    (A + B).col j = A.col j + B.col j := rfl

/-- Every subspace of a finite-dimensional space has a basis indexed by `Fin (finrank S)`. -/
theorem exists_isBasisOf_fin {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (S : Submodule ℝ V) : ∃ b : Fin (Module.finrank ℝ S) → V, IsBasisOf b S := by
  let B := Module.finBasis ℝ S
  refine ⟨fun i => (B i : V), ?_, ?_⟩
  · exact B.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  · have : Set.range (fun i => (B i : V)) = S.subtype '' Set.range B := by
      rw [← Set.range_comp]; rfl
    rw [this, Submodule.span_image, B.span_eq, Submodule.map_subtype_top]

theorem exists_compl_in {V : Type*} [AddCommGroup V] [Module ℝ V]
    (I U : Submodule ℝ V) (h : I ≤ U) : ∃ C : Submodule ℝ V, C ⊓ I = ⊥ ∧ C ⊔ I = U := by
  obtain ⟨C, hC⟩ := exists_isCompl (⟨I, h⟩ : Set.Iic U)
  refine ⟨C.1, ?_, ?_⟩
  · have := congrArg Subtype.val hC.symm.inf_eq_bot
    simpa using this
  · have := congrArg Subtype.val hC.symm.sup_eq_top
    simpa using this

/-- Corollary Two.III.2.12, as used on Sheet 6 Q1: a basis $\beta$ of $U\cap W$ extends to a
basis $\langle\mu,\beta\rangle$ of $U$ and to a basis $\langle\beta,\omega\rangle$ of $W$. -/
theorem exists_bases_inf {V : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (U W : Submodule ℝ V) :
    ∃ (j k p : ℕ) (β : Fin k → V) (μ : Fin j → V) (ω : Fin p → V),
      IsBasisOf β (U ⊓ W) ∧ IsBasisOf (Sum.elim μ β) U ∧ IsBasisOf (Sum.elim β ω) W := by
  obtain ⟨β, hβ⟩ := exists_isBasisOf_fin (U ⊓ W)
  obtain ⟨C, hC1, hC2⟩ := exists_compl_in (U ⊓ W) U inf_le_left
  obtain ⟨D, hD1, hD2⟩ := exists_compl_in (U ⊓ W) W inf_le_right
  obtain ⟨μ, hμ⟩ := exists_isBasisOf_fin C
  obtain ⟨ω, hω⟩ := exists_isBasisOf_fin D
  refine ⟨_, _, _, β, μ, ω, hβ, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩
  · apply hμ.1.sum_type hβ.1
    rw [hμ.2, hβ.2, disjoint_iff, hC1]
  · rw [span_range_sum_elim, hμ.2, hβ.2, hC2]
  · apply hβ.1.sum_type hω.1
    rw [hω.2, hβ.2, disjoint_iff, inf_comm, hD1]
  · rw [span_range_sum_elim, hω.2, hβ.2, sup_comm, hD2]

universe u in
/-- An injective linear map is an isomorphism onto its range, so the range has the same rank. -/
theorem rank_range_of_injective {V W : Type u} [AddCommGroup V] [Module ℝ V] [AddCommGroup W]
    [Module ℝ W] (f : V →ₗ[ℝ] W) (hf : Function.Injective f) :
    Module.rank ℝ (LinearMap.range f) = Module.rank ℝ V :=
  (LinearEquiv.ofInjective f hf).rank_eq.symm

end LinearAlgebraGame
