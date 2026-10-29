import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Two, part 2 (Hefferon Two.III)

Game-local definitions, granted bookkeeping lemmas, and all `TheoremDoc` / `DefinitionDoc`
entries for the worlds `BasisDim` ("Basis & Dimension") and `Dimension` ("Dimension & Rank"). -/

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

/-! ## Documentation -/

/-- `IsBasisOf v W`: the family (sequence) `v` is a basis of the subspace `W` — `LinearIndependent ℝ v ∧ span ℝ (Set.range v) = W`. Use `⊤` for the whole space. -/
DefinitionDoc LinearAlgebraGame.IsBasisOf as "IsBasisOf"
/-- `Poly n` is $\mathcal P_n$: a polynomial $a_0 + a_1x + \dots + a_nx^n$ stored as its coefficient vector `![a₀, …, aₙ]`. -/
DefinitionDoc LinearAlgebraGame.Poly as "Poly"
/-- `p.HasDegree d`: the coefficient of $x^d$ is nonzero and all higher ones vanish. -/
DefinitionDoc LinearAlgebraGame.Poly.HasDegree as "Poly.HasDegree"
/-- `p.eval x = ∑ i, p i * x ^ i`. -/
DefinitionDoc LinearAlgebraGame.Poly.eval as "Poly.eval"
/-- `Poly.evalAt x` is the linear map $p \mapsto p(x)$. -/
DefinitionDoc LinearAlgebraGame.Poly.evalAt as "Poly.evalAt"
/-- Sheet 6 Q1(a): $W_1$, the $2\times2$ matrices with zero first row. -/
DefinitionDoc LinearAlgebraGame.S6W₁ as "S6W₁"
/-- Sheet 6 Q1(a): $W_2$, the $2\times2$ matrices with zero diagonal. -/
DefinitionDoc LinearAlgebraGame.S6W₂ as "S6W₂"
/-- `augment A b` is the augmented matrix $[A \mid b]$. -/
DefinitionDoc LinearAlgebraGame.augment as "augment"
/-- `coordSpan S` is the span of the standard basis vectors $e_i$, $i \in S$. -/
DefinitionDoc LinearAlgebraGame.coordSpan as "coordSpan"
/-- `symMat n`: the subspace of symmetric $n\times n$ matrices ($A^T = A$). -/
DefinitionDoc LinearAlgebraGame.symMat as "symMat"
/-- `IsCompl U W`: $V = U \oplus W$, i.e. `U ⊓ W = ⊥` and `U ⊔ W = ⊤`. -/
DefinitionDoc IsCompl as "IsCompl"
/-- `LinearMap.ker f`: the null space $\{x \mid f(x) = 0\}$. -/
DefinitionDoc LinearMap.ker as "LinearMap.ker"
/-- `LinearMap.mulLeft ℝ a` is the linear map $p \mapsto a p$. -/
DefinitionDoc LinearMap.mulLeft as "LinearMap.mulLeft"
/-- `A.col j` is the $j$-th column of `A`. -/
DefinitionDoc Matrix.col as "Matrix.col"
/-- `A *ᵥ v`: the matrix–vector product. -/
DefinitionDoc Matrix.mulVec as "*ᵥ"
/-- `A.rank`: the rank of `A`, the dimension of its column space. -/
DefinitionDoc Matrix.rank as "Matrix.rank"
/-- `vecMulVec u v` is the matrix $\vec u\,\vec v^{\,T}$ with entries $u_i v_j$. -/
DefinitionDoc Matrix.vecMulVec as "vecMulVec"
/-- `Module.finrank ℝ V`: the dimension of `V` — **0 if `V` is infinite-dimensional**. -/
DefinitionDoc Module.finrank as "Module.finrank"
/-- `Module.rank ℝ V`: the dimension as a cardinal, honest also in infinite dimension. -/
DefinitionDoc Module.rank as "Module.rank"
/-- `Pi.basisFun ℝ S`: the standard basis of `S → ℝ` — the indicator functions $\delta_s$. -/
DefinitionDoc Pi.basisFun as "Pi.basisFun"
/-- `Polynomial ℝ` is $\mathbb R[x]$, all real polynomials. -/
DefinitionDoc Polynomial as "Polynomial"
/-- Theorem 1.12: `IsBasisOf v ⊤ ↔ ∀ x, ∃ c, ∑ i, c i • v i = x ∧ ∀ d, ∑ i, d i • v i = x → d = c` — a basis is exactly a sequence giving every vector unique coordinates. (You proved this.) -/
TheoremDoc LinearAlgebraGame.isBasisOf_top_iff as "isBasisOf_top_iff" in "Basis"
/-- If `h : IsBasisOf v W` then `Module.finrank ℝ W = Fintype.card ι`: the dimension is the number of basis vectors (for `v : Fin k → V` this is `k`). -/
TheoremDoc LinearAlgebraGame.IsBasisOf.finrank_eq as "IsBasisOf.finrank_eq" in "Dimension"
/-- `Poly.evalAt x p = p.eval x`. -/
TheoremDoc LinearAlgebraGame.Poly.evalAt_apply as "Poly.evalAt_apply" in "Basis"
/-- `A ∈ symMat n ↔ Aᵀ = A`. -/
TheoremDoc LinearAlgebraGame.mem_symMat as "mem_symMat" in "Basis"
/-- The columns of `augment A b` are `Fin.snoc A.col b`: the columns of $A$ followed by $b$. -/
TheoremDoc LinearAlgebraGame.augment_col as "augment_col" in "Rank"
/-- `(augment A b).rank = finrank ℝ (span ℝ (insert b (Set.range A.col)))`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.rank_augment as "rank_augment" in "Rank"
/-- Sheet 4 Q10(a): `U ≤ W → finrank ℝ U ≤ finrank ℝ W` (finite-dimensional ambient space). (You proved this.) -/
TheoremDoc LinearAlgebraGame.finrank_le_of_le as "finrank_le_of_le" in "Dimension"
/-- Sheet 4 Q10(b): for `h : U ≤ W`, `finrank ℝ U = finrank ℝ W ↔ U = W`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.eq_iff_finrank_eq_of_le as "eq_iff_finrank_eq_of_le" in "Dimension"
/-- The exchange lemma for three vectors. (You proved this.) -/
TheoremDoc LinearAlgebraGame.exchange_three as "exchange_three" in "Dimension"
/-- Sheet 6 Q1(b): with bases $\langle\beta\rangle$ of $U\cap W$, $\langle\mu,\beta\rangle$ of $U$, $\langle\beta,\omega\rangle$ of $W$, the sequence $\langle\mu,\beta,\omega\rangle$ is a basis of $U+W$. (You proved this.) -/
TheoremDoc LinearAlgebraGame.sum_basis as "sum_basis" in "Sums"
/-- Independence of a concatenation `Sum.elim f g` ↔ `∀ a b, ∑ a i • f i + ∑ b j • g j = 0 → a = 0 ∧ b = 0`. (Bookkeeping, granted.) -/
TheoremDoc LinearAlgebraGame.linearIndependent_sum_elim_iff as "linearIndependent_sum_elim_iff" in "Sums"
/-- Independence of `Sum.elim (Sum.elim f g) h` ↔ only the trivial relation `∑ a f + ∑ b g + ∑ c h = 0`. (Bookkeeping, granted.) -/
TheoremDoc LinearAlgebraGame.linearIndependent_sum_elim₃_iff as "linearIndependent_sum_elim₃_iff" in "Sums"
/-- `span (range (Sum.elim f g)) = span (range f) ⊔ span (range g)`. (Bookkeeping, granted.) -/
TheoremDoc LinearAlgebraGame.span_range_sum_elim as "span_range_sum_elim" in "Sums"
/-- `A ∈ S6W₁ ↔ A 0 0 = 0 ∧ A 0 1 = 0`. -/
TheoremDoc LinearAlgebraGame.mem_S6W₁ as "mem_S6W₁" in "Sums"
/-- `A ∈ S6W₂ ↔ A 0 0 = 0 ∧ A 1 1 = 0`. -/
TheoremDoc LinearAlgebraGame.mem_S6W₂ as "mem_S6W₂" in "Sums"
/-- `finrank ℝ (coordSpan S) = S.card`. -/
TheoremDoc LinearAlgebraGame.finrank_coordSpan as "finrank_coordSpan" in "Sums"
/-- `coordSpan S ⊔ coordSpan T = coordSpan (S ∪ T)`. -/
TheoremDoc LinearAlgebraGame.coordSpan_sup as "coordSpan_sup" in "Sums"
/-- `Set.range (Fin.snoc f x) = insert x (Set.range f)`. -/
TheoremDoc Fin.range_snoc as "Fin.range_snoc" in "Rank"
/-- $\sum_{i<6} f(i) = f(0) + \dots + f(5)$. -/
TheoremDoc Fin.sum_univ_six as "Fin.sum_univ_six" in "Basis"
/-- $\sum_{i<3} f(i) = f(0) + f(1) + f(2)$. -/
TheoremDoc Fin.sum_univ_three as "Fin.sum_univ_three" in "Basis"
/-- `(∅ : Finset α).card = 0`. -/
TheoremDoc Finset.card_empty as "Finset.card_empty" in "Dimension"
/-- `a ≠ b → ({a, b} : Finset α).card = 2`. -/
TheoremDoc Finset.card_pair as "Finset.card_pair" in "Dimension"
/-- `({a} : Finset α).card = 1`. -/
TheoremDoc Finset.card_singleton as "Finset.card_singleton" in "Dimension"
/-- `(∑ i ∈ s, f i) a = ∑ i ∈ s, f i a` for function-valued sums. -/
TheoremDoc Finset.sum_apply as "Finset.sum_apply" in "Basis"
/-- $\sum (f_i - g_i) = \sum f_i - \sum g_i$. -/
TheoremDoc Finset.sum_sub_distrib as "Finset.sum_sub_distrib" in "Basis"
/-- A finset `S`, viewed as a type, has `S.card` elements. -/
TheoremDoc Fintype.card_coe as "Fintype.card_coe" in "Dimension"
/-- `Fintype.card (Fin n) = n`. -/
TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Dimension"
/-- `Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β`. -/
TheoremDoc Fintype.card_sum as "Fintype.card_sum" in "Dimension"
/-- Lemma Two.II.1.5: `LinearIndependent ℝ v ↔ ∀ g, ∑ i, g i • v i = 0 → ∀ i, g i = 0` (only the trivial relation). -/
TheoremDoc Fintype.linearIndependent_iff as "Fintype.linearIndependent_iff" in "Basis"
/-- `¬ LinearIndependent ℝ v ↔ ∃ g, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0` (a nontrivial relation). -/
TheoremDoc Fintype.not_linearIndependent_iff as "Fintype.not_linearIndependent_iff" in "Dimension"
/-- If `h : IsCompl U W` then `U ⊓ W = ⊥`. -/
TheoremDoc IsCompl.inf_eq_bot as "IsCompl.inf_eq_bot" in "Sums"
/-- If `h : IsCompl U W` then `U ⊔ W = ⊤`. -/
TheoremDoc IsCompl.sup_eq_top as "IsCompl.sup_eq_top" in "Sums"
/-- `¬ U ≤ W ↔ ∃ x ∈ U, x ∉ W`. -/
TheoremDoc IsConcreteLE.not_le_iff_exists as "not_le_iff_exists" in "Sums"
/-- An injective linear map `f` gives an isomorphism from its domain onto `LinearMap.range f`. -/
TheoremDoc LinearEquiv.ofInjective as "LinearEquiv.ofInjective" in "Dimension"
/-- Isomorphic spaces have equal `Module.rank`. -/
TheoremDoc LinearEquiv.rank_eq as "LinearEquiv.rank_eq" in "Dimension"
/-- An independent family in a finite-dimensional space has at most `finrank` members. -/
TheoremDoc LinearIndependent.fintype_card_le_finrank as "LinearIndependent.fintype_card_le_finrank" in "Dimension"
/-- `LinearIndependent ℝ ![x, y] ↔ ∀ s t, s • x + t • y = 0 → s = 0 ∧ t = 0`. -/
TheoremDoc LinearIndependent.pair_iff as "LinearIndependent.pair_iff" in "Basis"
/-- An injective linear map `M → M'` gives `finrank M ≤ finrank M'`. -/
TheoremDoc LinearMap.finrank_le_finrank_of_injective as "LinearMap.finrank_le_finrank_of_injective" in "Dimension"
/-- `x ∈ LinearMap.ker f ↔ f x = 0`. -/
TheoremDoc LinearMap.mem_ker as "LinearMap.mem_ker" in "Dimension"
/-- `LinearMap.range f = ⊤ ↔ Function.Surjective f`. -/
TheoremDoc LinearMap.range_eq_top as "LinearMap.range_eq_top" in "Dimension"
/-- `A.col j i = A i j`. -/
TheoremDoc Matrix.col_apply as "Matrix.col_apply" in "Rank"
/-- The range of $\vec x \mapsto A\vec x$ is the span of the columns of $A$. -/
TheoremDoc Matrix.range_mulVecLin as "Matrix.range_mulVecLin" in "Rank"
/-- `A.rank = finrank ℝ (span ℝ (Set.range A.col))`: rank is the dimension of the column space. -/
TheoremDoc Matrix.rank_eq_finrank_span_cols as "rank_eq_finrank_span_cols" in "Rank"
/-- Disabled here. -/
TheoremDoc Matrix.rank_le_card_height as "rank_le_card_height" in "Rank"
/-- An $m\times n$ matrix has rank at most $m$. -/
TheoremDoc Matrix.rank_le_height as "rank_le_height" in "Rank"
/-- An $m\times n$ matrix has rank at most $n$. -/
TheoremDoc Matrix.rank_le_width as "rank_le_width" in "Rank"
/-- Theorem Two.III.3.11 (row rank = column rank): `Aᵀ.rank = A.rank`. -/
TheoremDoc Matrix.rank_transpose as "rank_transpose" in "Rank"
/-- `(0 : Matrix m n ℝ).rank = 0`. -/
TheoremDoc Matrix.rank_zero as "rank_zero" in "Rank"
/-- `vecMulVec u v i j = u i * v j`. -/
TheoremDoc Matrix.vecMulVec_apply as "vecMulVec_apply" in "Rank"
/-- If `b` is a basis of `M` indexed by `ι`, then `finrank ℝ M = Fintype.card ι`. -/
TheoremDoc Module.finrank_eq_card_basis as "Module.finrank_eq_card_basis" in "Dimension"
/-- `finrank ℝ (Fin n → ℝ) = n`. -/
TheoremDoc Module.finrank_fin_fun as "Module.finrank_fin_fun" in "Dimension"
/-- Disabled in Sheet 4 Q7. -/
TheoremDoc Module.finrank_fintype_fun_eq_card as "Module.finrank_fintype_fun_eq_card" in "Dimension"
/-- Disabled in Sheet 4 Q7. -/
TheoremDoc Module.finrank_pi as "Module.finrank_pi" in "Dimension"
/-- `(Finset.Icc a b).card = b + 1 - a`. -/
TheoremDoc Nat.card_Icc as "Nat.card_Icc" in "Dimension"
/-- `(c • f) i = c • f i`. -/
TheoremDoc Pi.smul_apply as "Pi.smul_apply" in "Basis"
/-- `X ∣ p ↔ p.coeff 0 = 0`. -/
TheoremDoc Polynomial.X_dvd_iff as "Polynomial.X_dvd_iff" in "Dimension"
/-- `X ≠ 0`. -/
TheoremDoc Polynomial.X_ne_zero as "Polynomial.X_ne_zero" in "Dimension"
/-- `(∀ x ∈ Set.range f, P x) ↔ ∀ i, P (f i)`. -/
TheoremDoc Set.forall_mem_range as "Set.forall_mem_range" in "Rank"
/-- `a ∈ insert a s`. -/
TheoremDoc Set.mem_insert as "Set.mem_insert" in "Rank"
/-- `a ∈ insert b s ↔ a = b ∨ a ∈ s`. -/
TheoremDoc Set.mem_insert_iff as "Set.mem_insert_iff" in "Sums"
/-- `a ∈ {x | p x}` is `p a`. -/
TheoremDoc Set.mem_setOf_eq as "Set.mem_setOf_eq" in "Basis"
/-- `a ∈ {b} ↔ a = b`. -/
TheoremDoc Set.mem_singleton_iff as "Set.mem_singleton_iff" in "Sums"
/-- The range of a function on an empty type is `∅`. -/
TheoremDoc Set.range_eq_empty as "Set.range_eq_empty" in "Dimension"
/-- `s ⊆ insert a s`. -/
TheoremDoc Set.subset_insert as "Set.subset_insert" in "Rank"
/-- `x ∈ (U : Set V) ↔ x ∈ U`. -/
TheoremDoc SetLike.mem_coe as "SetLike.mem_coe" in "Basis"
/-- `x ∈ U → y ∈ W → x + y ∈ U ⊔ W`. -/
TheoremDoc Submodule.add_mem_sup as "Submodule.add_mem_sup" in "Sums"
/-- Mathlib's Sheet 4 Q10(b). Disabled where you prove it. -/
TheoremDoc Submodule.eq_of_le_of_finrank_eq as "eq_of_le_of_finrank_eq" in "Dimension"
/-- Disabled where you prove Sheet 4 Q10(b). -/
TheoremDoc Submodule.eq_of_le_of_finrank_le as "eq_of_le_of_finrank_le" in "Dimension"
/-- $\dim(U + W) \le \dim U + \dim W$. -/
TheoremDoc Submodule.finrank_add_le_finrank_add_finrank as "finrank_add_le_finrank_add_finrank" in "Sums"
/-- `finrank ℝ U = 0 ↔ U = ⊥`. -/
TheoremDoc Submodule.finrank_eq_zero as "Submodule.finrank_eq_zero" in "Dimension"
/-- `finrank ℝ U ≤ finrank ℝ V` for a subspace `U` of `V`. -/
TheoremDoc Submodule.finrank_le as "Submodule.finrank_le" in "Dimension"
/-- Disabled in Sheet 4 Q10(a). -/
TheoremDoc Submodule.finrank_le_finrank_of_le as "finrank_le_finrank_of_le" in "Dimension"
/-- Disabled in Sheet 4 Q10(b). -/
TheoremDoc Submodule.finrank_lt_finrank_of_lt as "finrank_lt_finrank_of_lt" in "Dimension"
/-- Sheet 4 Q10(a): `U ≤ W → finrank U ≤ finrank W`. You proved it as `finrank_le_of_le`. -/
TheoremDoc Submodule.finrank_mono as "Submodule.finrank_mono" in "Dimension"
/-- The dimension formula: $\dim(U+W) + \dim(U\cap W) = \dim U + \dim W$ (proved by you in Sheet 6 Q1). -/
TheoremDoc Submodule.finrank_sup_add_finrank_inf_eq as "finrank_sup_add_finrank_inf_eq" in "Sums"
/-- Extension lemma (Two.II.1.15), dimension form: `w ∉ U → finrank (U ⊔ span ℝ {w}) = finrank U + 1`. -/
TheoremDoc Submodule.finrank_sup_span_singleton as "finrank_sup_span_singleton" in "Dimension"
/-- For `h : U ≤ W`, the inclusion map `Submodule.inclusion h : U → W` is injective. -/
TheoremDoc Submodule.inclusion_injective as "Submodule.inclusion_injective" in "Dimension"
/-- `x ∈ ⊥ ↔ x = 0`. -/
TheoremDoc Submodule.mem_bot as "Submodule.mem_bot" in "Dimension"
/-- `x ∈ span ℝ {a, b} ↔ ∃ s t, s • a + t • b = x`. -/
TheoremDoc Submodule.mem_span_pair as "Submodule.mem_span_pair" in "Basis"
/-- `x ∈ span ℝ (Set.range v) ↔ ∃ c, ∑ i, c i • v i = x`. -/
TheoremDoc Submodule.mem_span_range_iff_exists_fun as "mem_span_range_iff_exists_fun" in "Basis"
/-- `x ∈ span ℝ {u} ↔ ∃ a, a • u = x`. -/
TheoremDoc Submodule.mem_span_singleton as "Submodule.mem_span_singleton" in "Basis"
/-- `x ∈ U → x ∈ U ⊔ W`. -/
TheoremDoc Submodule.mem_sup_left as "Submodule.mem_sup_left" in "Sums"
/-- `x ∈ W → x ∈ U ⊔ W`. -/
TheoremDoc Submodule.mem_sup_right as "Submodule.mem_sup_right" in "Sums"
/-- Every vector is in `⊤`. -/
TheoremDoc Submodule.mem_top as "Submodule.mem_top" in "Basis"
/-- `x ∈ U → -x ∈ U`. -/
TheoremDoc Submodule.neg_mem as "Submodule.neg_mem" in "Basis"
/-- `x ∈ U → c • x ∈ U`. -/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "Basis"
/-- `span ℝ ∅ = ⊥`. -/
TheoremDoc Submodule.span_empty as "Submodule.span_empty" in "Dimension"
/-- `span ℝ s = ⊥ ↔ ∀ x ∈ s, x = 0`. -/
TheoremDoc Submodule.span_eq_bot as "Submodule.span_eq_bot" in "Dimension"
/-- Lemma Two.II.1.2: `x ∈ span ℝ s → span ℝ (insert x s) = span ℝ s`. -/
TheoremDoc Submodule.span_insert_eq_span as "span_insert_eq_span" in "Rank"
/-- `span ℝ s ≤ U ↔ s ⊆ U`: a span is inside a subspace iff the generators are. -/
TheoremDoc Submodule.span_le as "Submodule.span_le" in "Basis"
/-- `s ⊆ t → span ℝ s ≤ span ℝ t`. -/
TheoremDoc Submodule.span_mono as "Submodule.span_mono" in "Rank"
/-- `span ℝ {x} ≤ U ↔ x ∈ U`. -/
TheoremDoc Submodule.span_singleton_le_iff_mem as "span_singleton_le_iff_mem" in "Dimension"
/-- `x ∈ U → y ∈ U → x - y ∈ U`. -/
TheoremDoc Submodule.sub_mem as "Submodule.sub_mem" in "Sums"
/-- Each element of `s` lies in `span ℝ s`. -/
TheoremDoc Submodule.subset_span as "Submodule.subset_span" in "Basis"
/-- `a + b - a = b`. -/
TheoremDoc add_sub_cancel_left as "add_sub_cancel_left" in "Sums"
/-- `a + b - b = a`. -/
TheoremDoc add_sub_cancel_right as "add_sub_cancel_right" in "Sums"
/-- `U = ⊥ ↔ U ≤ ⊥`. -/
TheoremDoc eq_bot_iff as "eq_bot_iff" in "Dimension"
/-- `a + b = 0 → b = -a`. -/
TheoremDoc eq_neg_of_add_eq_zero_right as "eq_neg_of_add_eq_zero_right" in "Sums"
/-- `U = ⊤ ↔ ⊤ ≤ U`. -/
TheoremDoc eq_top_iff as "eq_top_iff" in "Basis"
/-- `Iff.rfl : P ↔ P` — a statement is equivalent to itself (also when the two sides agree
after unfolding definitions). The tactic `rfl` does the same. -/
TheoremDoc Iff.rfl as "Iff.rfl" in "Basis"
/-- `symm h : b = a` from `h : a = b` (works for any symmetric relation). -/
TheoremDoc symm as "symm" in "Basis"
/-- `finrank ℝ (⊥ : Submodule ℝ V) = 0`. -/
TheoremDoc finrank_bot as "finrank_bot" in "Dimension"
/-- `finrank ℝ V = 1 ↔ ∃ v ≠ 0, ∀ w, ∃ c, c • v = w`: dimension 1 means a line. -/
TheoremDoc finrank_eq_one_iff' as "finrank_eq_one_iff'" in "Rank"
/-- `finrank (span ℝ s) ≤ s.toFinset.card`: a span of $k$ vectors has dimension at most $k$. -/
TheoremDoc finrank_span_le_card as "finrank_span_le_card" in "Rank"
/-- `U ⊓ W = U ↔ U ≤ W`. -/
TheoremDoc inf_eq_left as "inf_eq_left" in "Sums"
/-- `U ⊓ W = W ↔ W ≤ U`. -/
TheoremDoc inf_eq_right as "inf_eq_right" in "Sums"
/-- `U ≤ W → W ≤ U → U = W`. -/
TheoremDoc le_antisymm as "le_antisymm" in "Basis"
/-- `U ≤ U ⊔ W`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Sums"
/-- The empty sequence is linearly independent. -/
TheoremDoc linearIndependent_empty_type as "linearIndependent_empty_type" in "Dimension"
/-- `a * b = 0 ↔ a = 0 ∨ b = 0`. -/
TheoremDoc mul_eq_zero as "mul_eq_zero" in "Dimension"
/-- `a ≠ 0 → a * b = a * c → b = c`. -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Dimension"
/-- `-a = 0 ↔ a = 0`. -/
TheoremDoc neg_eq_zero as "neg_eq_zero" in "Sums"
/-- For scalars, `a • b = a * b`. -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Basis"
/-- `(r - s) • v = r • v - s • v`. -/
TheoremDoc sub_smul as "sub_smul" in "Basis"
/-- `(U ⊔ W) ⊔ X = U ⊔ (W ⊔ X)`. -/
TheoremDoc sup_assoc as "sup_assoc" in "Sums"
/-- `U ⊔ W = U ↔ W ≤ U`. -/
TheoremDoc sup_eq_left as "sup_eq_left" in "Sums"
/-- `U ⊔ W = W ↔ U ≤ W`. -/
TheoremDoc sup_eq_right as "sup_eq_right" in "Sums"
/-- `U ⊔ U = U`. -/
TheoremDoc sup_idem as "sup_idem" in "Sums"
/-- `U ≤ X → W ≤ X → U ⊔ W ≤ X`. -/
TheoremDoc sup_le as "sup_le" in "Dimension"
/-- `U ⊔ W ≤ X ↔ U ≤ X ∧ W ≤ X`. -/
TheoremDoc sup_le_iff as "sup_le_iff" in "Sums"
/-- `0 • v = 0`. -/
TheoremDoc zero_smul as "zero_smul" in "Basis"

/-- Theorem 1.12, ⇒: if `IsBasisOf v ⊤` then every `x` has coefficients `c` with `∑ i, c i • v i = x`, and any other such `d` equals `c`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.rep_unique_of_isBasisOf as "rep_unique_of_isBasisOf" in "Basis"
/-- Sheet 3 Q9: `A.rank = 0 ↔ A = 0`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.rank_eq_zero_iff as "rank_eq_zero_iff" in "Rank"
/-- If `finrank ℝ W = 1` then `∃ u, u ∈ W ∧ u ≠ 0 ∧ ∀ w ∈ W, ∃ c : ℝ, c • u = w`: a one-dimensional subspace is the line through a nonzero `u`. (Granted.) -/
TheoremDoc LinearAlgebraGame.exists_line_of_finrank_eq_one as "exists_line_of_finrank_eq_one" in "Dimension"
/-- `finrank ℝ (span ℝ {u}) ≤ 1`: a line has dimension at most 1. -/
TheoremDoc LinearAlgebraGame.finrank_span_singleton_le_one as "finrank_span_singleton_le_one" in "Dimension"
/-- `A *ᵥ x = ∑ j, x j • A.col j`: $A\vec x$ is the combination of the columns with coefficients $x_j$. -/
TheoremDoc LinearAlgebraGame.mulVec_eq_sum_col as "mulVec_eq_sum_col" in "Rank"
/-- `b ∈ span ℝ (Set.range A.col) ↔ ∃ x, A *ᵥ x = b`: $\vec b$ is in the column space iff $A\vec x = \vec b$ is solvable. -/
TheoremDoc LinearAlgebraGame.mem_span_cols_iff as "mem_span_cols_iff" in "Rank"
/-- `(-A).col j = -A.col j`. -/
TheoremDoc LinearAlgebraGame.col_neg as "col_neg" in "Rank"
/-- `(k • A).col j = k • A.col j`. -/
TheoremDoc LinearAlgebraGame.col_smul as "col_smul" in "Rank"
/-- `(A + B).col j = A.col j + B.col j`. -/
TheoremDoc LinearAlgebraGame.col_add as "col_add" in "Rank"
/-- Sheet 4 Q11: if every column of `D` is in the column space of `C`, then `D.rank ≤ C.rank`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.rank_le_of_cols_mem as "rank_le_of_cols_mem" in "Rank"
/-- Corollary 2.12 (granted): in a finite-dimensional space, there are bases `β` of `U ⊓ W`, `Sum.elim μ β` of `U` and `Sum.elim β ω` of `W` — a basis of the intersection extended to bases of both. -/
TheoremDoc LinearAlgebraGame.exists_bases_inf as "exists_bases_inf" in "Sums"
/-- Sheet 6 Q1(c), the dimension formula: given bases `β` of `U ⊓ W`, `Sum.elim μ β` of `U`, `Sum.elim β ω` of `W`, `finrank (U ⊔ W) = finrank U + finrank W - finrank (U ⊓ W)`. Use with `exists_bases_inf`. (You proved this.) -/
TheoremDoc LinearAlgebraGame.dim_formula as "dim_formula" in "Sums"
/-- `¬ (a ∨ b) ↔ ¬ a ∧ ¬ b`. -/
TheoremDoc not_or as "not_or" in "Sums"
/-- `bot_le : ⊥ ≤ W`: the trivial subspace is inside every subspace. -/
TheoremDoc bot_le as "bot_le" in "Dimension"
/-- `inf_le_left : U ⊓ W ≤ U`. -/
TheoremDoc inf_le_left as "inf_le_left" in "Sums"
/-- `inf_le_right : U ⊓ W ≤ W`. -/
TheoremDoc inf_le_right as "inf_le_right" in "Sums"
/-- Membership of a `Finset` literal: `a ∈ insert b s ↔ a = b ∨ a ∈ s`. -/
TheoremDoc Finset.mem_insert as "Finset.mem_insert" in "Sums"
/-- `a ∈ {b} ↔ a = b` for a `Finset`. -/
TheoremDoc Finset.mem_singleton as "Finset.mem_singleton" in "Sums"
/-- `LinearMap.mulLeft ℝ a p = a * p`. -/
TheoremDoc LinearMap.mulLeft_apply as "LinearMap.mulLeft_apply" in "Dimension"
/-- An injective linear map `f : V →ₗ W` has `Module.rank (range f) = Module.rank V`. -/
TheoremDoc LinearAlgebraGame.rank_range_of_injective as "rank_range_of_injective" in "Dimension"
/-- `LinearMap.range f`: the range space $\{f(v) \mid v \in V\}$, a subspace of the codomain. -/
DefinitionDoc LinearMap.range as "LinearMap.range"
/-- $-(-a) = a$. -/
TheoremDoc neg_neg as "neg_neg" in "Rank"
/-- `trivial : True`. Membership of `Set.univ` (or of `⊤` viewed as a set) is `True` by definition, so `trivial` proves it. -/
TheoremDoc trivial as "trivial" in "Sums"
