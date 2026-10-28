import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Three, part 1: Isomorphisms (Three.I) and Homomorphisms (Three.II)

Game-local definitions and every `TheoremDoc` / `DefinitionDoc` used by the worlds
`Isomorphisms` and `Homomorphisms`. -/

namespace LinearAlgebraGame

/-- The line segment from `u` to `v` (Sheet 5 Q3): `{ t • u + (1 - t) • v | t ∈ [0, 1] }`. -/
def seg {V : Type*} [AddCommGroup V] [Module ℝ V] (u v : V) : Set V :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, x = t • u + (1 - t) • v}

/-- A set is convex if it contains the segment between any two of its points (Sheet 5 Q3b). -/
def IsConvex {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, seg u v ⊆ C

end LinearAlgebraGame

/-! ## Definitions -/

/-- `seg u v` is the line segment $\{\, t\vec u + (1-t)\vec v \mid t\in[0..1] \,\}$.
Membership is by definition: `x ∈ seg u v` *is* `∃ t ∈ Set.Icc 0 1, x = t • u + (1 - t) • v`,
so `obtain ⟨t, ht, rfl⟩ := hx` takes it apart and `exact ⟨t, ht, rfl⟩` builds it. -/
DefinitionDoc LinearAlgebraGame.seg as "seg"

/-- `IsConvex C` means: for all `u ∈ C` and `v ∈ C`, `seg u v ⊆ C`. Unfolded,
`intro u hu v hv x hx` reduces it to showing `x ∈ C` from `hx : x ∈ seg u v`. -/
DefinitionDoc LinearAlgebraGame.IsConvex as "IsConvex"

/-- `V ≃ₗ[ℝ] W` is the type of **isomorphisms** from `V` to `W` (Hefferon Def Three.I.1.3):
linear bijections. For `e : V ≃ₗ[ℝ] W`, `e v` applies it, `e.symm` is the inverse
isomorphism and `e.trans f` is the composite (first `e`, then `f`).
`Nonempty (V ≃ₗ[ℝ] W)` says "$V \cong W$"; build it with `⟨e⟩`, take it apart with
`obtain ⟨e⟩ := h`. -/
DefinitionDoc LinearEquiv as "≃ₗ (isomorphism)"

/-- `LinearEquiv.refl ℝ V : V ≃ₗ[ℝ] V` is the identity isomorphism. -/
DefinitionDoc LinearEquiv.refl as "LinearEquiv.refl"

/-- For `e : V ≃ₗ[ℝ] W`, `e.symm : W ≃ₗ[ℝ] V` is the inverse isomorphism. -/
DefinitionDoc LinearEquiv.symm as "LinearEquiv.symm"

/-- For `e : U ≃ₗ[ℝ] V` and `f : V ≃ₗ[ℝ] W`, `e.trans f : U ≃ₗ[ℝ] W` is the composite. -/
DefinitionDoc LinearEquiv.trans as "LinearEquiv.trans"

/-- For a basis `B : Module.Basis (Fin n) ℝ V`, `B.equivFun : V ≃ₗ[ℝ] (Fin n → ℝ)` is
$\mathrm{Rep}_B$: it sends $\vec v$ to its coordinate vector. -/
DefinitionDoc Module.Basis.equivFun as "Basis.equivFun (Rep_B)"

/-- `Module.finBasis ℝ V` is some basis of a finite-dimensional `V`, indexed by
`Fin (finrank ℝ V)`. -/
DefinitionDoc Module.finBasis as "finBasis"

/-- `Module.finBasisOfFinrankEq ℝ V h`, for `h : finrank ℝ V = n`, is a basis of `V` indexed by
`Fin n`. -/
DefinitionDoc Module.finBasisOfFinrankEq as "finBasisOfFinrankEq"

/-- For bases `B` of `U` and `D` of `W`, `B.prod D` is the basis
$\langle(\vec\beta_1,\vec 0),\dots,(\vec\beta_n,\vec 0),(\vec 0,\vec\delta_1),\dots,(\vec 0,\vec\delta_m)\rangle$
of `U × W`, indexed by `Fin n ⊕ Fin m`. -/
DefinitionDoc Module.Basis.prod as "Basis.prod"

/-- `B.constr ℝ f : V →ₗ[ℝ] W` is the map that **extends `f` linearly** from the basis `B`
(Hefferon Def Three.II.1.10): $c_1\vec\beta_1+\dots+c_n\vec\beta_n \mapsto c_1 f(1)+\dots+c_n f(n)$. -/
DefinitionDoc Module.Basis.constr as "Basis.constr"

/-- `LinearMap.ker h` is the **null space** $\mathscr N(h)$, a subspace of the domain. -/
DefinitionDoc LinearMap.ker as "ker (null space)"

/-- `LinearMap.range h` is the **range space** $\mathscr R(h)$, a subspace of the codomain.
Its dimension `finrank ℝ (LinearMap.range h)` is the rank of `h`. -/
DefinitionDoc LinearMap.range as "range"

/-- `Module.finrank ℝ V` is the dimension of `V` (it is `0` for infinite-dimensional `V`,
so statements about it always assume `[FiniteDimensional ℝ V]`). -/
DefinitionDoc Module.finrank as "finrank (dim)"

/-- For an injective linear `h`, `LinearEquiv.ofInjective h hi : V ≃ₗ[ℝ] LinearMap.range h`
is `h` viewed as an isomorphism onto its range. -/
DefinitionDoc LinearEquiv.ofInjective as "LinearEquiv.ofInjective"

/-- `h.rangeRestrict : V →ₗ[ℝ] LinearMap.range h` is `h` with codomain cut down to its range;
`((h.rangeRestrict v : LinearMap.range h) : W) = h v`. -/
DefinitionDoc LinearMap.rangeRestrict as "rangeRestrict"

/-- `LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ` takes the `i`-th coordinate: `LinearMap.proj i v = v i`. -/
DefinitionDoc LinearMap.proj as "LinearMap.proj"

/-- `IsLinearMap ℝ f` says the plain function `f` preserves `+` and `•`; for `hf : IsLinearMap ℝ f`,
`hf.map_add x y : f (x + y) = f x + f y` and `hf.map_smul c x : f (c • x) = c • f x`. -/
DefinitionDoc IsLinearMap as "IsLinearMap"

/-! ## Theorems: Isomorphisms -/

/-- $r \cdot (s \cdot v) = (rs)\cdot v$ — Hefferon's condition (8). -/
TheoremDoc smul_smul as "smul_smul" in "Isomorphisms"
/-- `inv_mul_cancel₀ h : a⁻¹ * a = 1` for `h : a ≠ 0`. -/
TheoremDoc inv_mul_cancel₀ as "inv_mul_cancel₀" in "Isomorphisms"
/-- `mul_inv_cancel₀ h : a * a⁻¹ = 1` for `h : a ≠ 0`. -/
TheoremDoc mul_inv_cancel₀ as "mul_inv_cancel₀" in "Isomorphisms"

/-- `map_add h u v : h (u + v) = h u + h v` — a linear map preserves addition. -/
TheoremDoc map_add as "map_add" in "Maps"
/-- `map_smul h r v : h (r • v) = r • h v` — a linear map preserves scalar multiplication. -/
TheoremDoc map_smul as "map_smul" in "Maps"

/-- `Finset.sum_add_distrib : ∑ i, (f i + g i) = ∑ i, f i + ∑ i, g i`. -/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "Sums"
/-- `Finset.smul_sum : r • ∑ i, f i = ∑ i, r • f i`. -/
TheoremDoc Finset.smul_sum as "Finset.smul_sum" in "Sums"
/-- `Finset.sum_const_zero : ∑ i, 0 = 0`. -/
TheoremDoc Finset.sum_const_zero as "Finset.sum_const_zero" in "Sums"
/-- `map_sum h f s : h (∑ i ∈ s, f i) = ∑ i ∈ s, h (f i)` — a linear map preserves sums. -/
TheoremDoc map_sum as "map_sum" in "Maps"
/-- `(f + g) i = f i + g i` for coordinate functions (finitely supported functions). -/
TheoremDoc Finsupp.add_apply as "Finsupp.add_apply" in "Sums"
/-- `(r • f) i = r • f i` for coordinate functions (finitely supported functions). -/
TheoremDoc Finsupp.smul_apply as "Finsupp.smul_apply" in "Sums"
/-- `smul_eq_mul : a • b = a * b` for real numbers. -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Sums"
/-- `mul_smul : (a * b) • v = a • (b • v)`. -/
TheoremDoc SemigroupAction.mul_smul as "mul_smul" in "Sums"

/-- `B.repr_sum_self c : B.repr (∑ i, c i • B i) = c` — the coordinates of
$c_1\vec\beta_1+\dots+c_n\vec\beta_n$ with respect to $B$ are $c_1,\dots,c_n$. -/
TheoremDoc Module.Basis.repr_sum_self as "Basis.repr_sum_self" in "Bases"
/-- `B.sum_repr v : ∑ i, B.repr v i • B i = v` — every vector is the combination of the basis
vectors with its coordinates as coefficients. -/
TheoremDoc Module.Basis.sum_repr as "Basis.sum_repr" in "Bases"
/-- `LinearEquiv.injective e : Function.Injective e`; for a basis, `B.repr.injective` says
vectors with the same coordinates are equal. -/
TheoremDoc LinearEquiv.injective as "LinearEquiv.injective" in "Bases"

/-- `e.finrank_eq : finrank ℝ V = finrank ℝ W` for `e : V ≃ₗ[ℝ] W` — isomorphic spaces have
the same dimension. -/
TheoremDoc LinearEquiv.finrank_eq as "LinearEquiv.finrank_eq" in "Dimension"
/-- `Module.finrank_fin_fun ℝ : finrank ℝ (Fin n → ℝ) = n` — $\dim\mathbb R^n = n$. -/
TheoremDoc Module.finrank_fin_fun as "finrank_fin_fun" in "Dimension"
/-- `Module.finrank_eq_card_basis B : finrank ℝ V = Fintype.card ι` for a basis `B` indexed by `ι`
— the dimension is the number of basis vectors. -/
TheoremDoc Module.finrank_eq_card_basis as "finrank_eq_card_basis" in "Dimension"
/-- `Fintype.card_sum : Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β`. -/
TheoremDoc Fintype.card_sum as "Fintype.card_sum" in "Dimension"
/-- `Fintype.card_fin n : Fintype.card (Fin n) = n`. -/
TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Dimension"
/-- Mathlib's $\dim(U\times W)=\dim U+\dim W$. Disabled where it is the question. -/
TheoremDoc Module.finrank_prod as "finrank_prod" in "Dimension"
/-- Mathlib: finite-dimensional spaces are isomorphic iff they have equal dimension.
Disabled where it is the question. -/
TheoremDoc FiniteDimensional.nonempty_linearEquiv_iff_finrank_eq as
  "nonempty_linearEquiv_iff_finrank_eq" in "Dimension"
/-- Mathlib: equal dimension gives an isomorphism. Disabled where it is the question. -/
TheoremDoc FiniteDimensional.nonempty_linearEquiv_of_finrank_eq as
  "nonempty_linearEquiv_of_finrank_eq" in "Dimension"

/-- `LinearMap.coprod_apply : (f.coprod g) (x, y) = f x + g y`. -/
TheoremDoc LinearMap.coprod_apply as "coprod_apply" in "Subspaces"
/-- `Submodule.subtype_apply : U.subtype u = (u : V)` — the inclusion of a subspace. -/
TheoremDoc Submodule.subtype_apply as "subtype_apply" in "Subspaces"
/-- `Submodule.mem_sup : x ∈ U ⊔ W ↔ ∃ y ∈ U, ∃ z ∈ W, y + z = x` — membership in the sum
$U + W$. -/
TheoremDoc Submodule.mem_sup as "mem_sup" in "Subspaces"
/-- `Submodule.mem_top : x ∈ ⊤` — every vector lies in the whole space. -/
TheoremDoc Submodule.mem_top as "mem_top" in "Subspaces"
/-- `Submodule.mem_bot : x ∈ ⊥ ↔ x = 0` — the trivial subspace is $\{\vec 0\}$. -/
TheoremDoc Submodule.mem_bot as "mem_bot" in "Subspaces"
/-- `Submodule.neg_mem U : x ∈ U → -x ∈ U`. -/
TheoremDoc Submodule.neg_mem as "Submodule.neg_mem" in "Subspaces"
/-- `eq_neg_of_add_eq_zero_left : a + b = 0 → a = -b`. -/
TheoremDoc eq_neg_of_add_eq_zero_left as "eq_neg_of_add_eq_zero_left" in "Subspaces"
/-- `injective_iff_map_eq_zero f : Function.Injective f ↔ ∀ a, f a = 0 → a = 0` — a linear map
is one-to-one iff only $\vec 0$ maps to $\vec 0$ (granted here; you prove it in Homomorphisms). -/
TheoremDoc injective_iff_map_eq_zero as "injective_iff_map_eq_zero" in "Maps"
/-- A variant of `injective_iff_map_eq_zero`. -/
TheoremDoc injective_iff_map_eq_zero' as "injective_iff_map_eq_zero'" in "Maps"

/-! ## Theorems: Homomorphisms -/

/-- $0\cdot\vec v=\vec 0$. You proved this in the Axioms world (`zero_smul_eq_zero`). -/
TheoremDoc zero_smul as "zero_smul" in "Maps"
/-- Mathlib's `h 0 = 0`. Disabled where it is the question. -/
TheoremDoc map_zero as "map_zero" in "Maps"
/-- Mathlib's `h 0 = 0`. Disabled where it is the question. -/
TheoremDoc LinearMap.map_zero as "LinearMap.map_zero" in "Maps"
/-- `map_sub h u v : h (u - v) = h u - h v` — you proved this for Sheet 5 Q2. -/
TheoremDoc map_sub as "map_sub" in "Maps"
/-- Mathlib's `h (u - v) = h u - h v`. -/
TheoremDoc LinearMap.map_sub as "LinearMap.map_sub" in "Maps"
/-- `sub_eq_add_neg : a - b = a + -b`. -/
TheoremDoc sub_eq_add_neg as "sub_eq_add_neg" in "Maps"
/-- `neg_one_smul ℝ v : (-1 : ℝ) • v = -v` — you proved this in the Axioms world. -/
TheoremDoc neg_one_smul as "neg_one_smul" in "Maps"
/-- `sub_self a : a - a = 0`. -/
TheoremDoc sub_self as "sub_self" in "Maps"
/-- `sub_eq_zero : a - b = 0 ↔ a = b`. -/
TheoremDoc sub_eq_zero as "sub_eq_zero" in "Maps"
/-- `smul_zero r : r • 0 = 0`. -/
TheoremDoc smul_zero as "smul_zero" in "Maps"
/-- `smul_comm a b v : a • b • v = b • a • v`. -/
TheoremDoc SMulCommClass.smul_comm as "smul_comm" in "Maps"

/-- `B.constr_basis ℝ f i : B.constr ℝ f (B i) = f i` — the linear extension does what it was
told on the basis. -/
TheoremDoc Module.Basis.constr_basis as "Basis.constr_basis" in "Bases"
/-- Mathlib: linear maps agreeing on a basis are equal. Disabled where it is the question. -/
TheoremDoc Module.Basis.ext as "Basis.ext" in "Bases"
/-- Mathlib: a linear map equals the extension of its values on a basis. Disabled where it is
the question. -/
TheoremDoc Module.Basis.constr_eq as "Basis.constr_eq" in "Bases"
/-- `B.linearIndependent : LinearIndependent ℝ B` — a basis is linearly independent. -/
TheoremDoc Module.Basis.linearIndependent as "Basis.linearIndependent" in "Bases"
/-- `Fintype.linearIndependent_iff : LinearIndependent ℝ v ↔ ∀ g, ∑ i, g i • v i = 0 → ∀ i, g i = 0`
— Hefferon's definition of linear independence. -/
TheoremDoc Fintype.linearIndependent_iff as "linearIndependent_iff" in "Bases"
/-- `hv.map' h hker : LinearIndependent ℝ (h ∘ v)` for `hv : LinearIndependent ℝ v` and
`hker : LinearMap.ker h = ⊥` — a one-to-one map keeps independent sets independent. -/
TheoremDoc LinearIndependent.map' as "LinearIndependent.map'" in "Bases"

/-- `LinearMap.mem_ker : v ∈ LinearMap.ker h ↔ h v = 0`. -/
TheoremDoc LinearMap.mem_ker as "mem_ker" in "Maps"
/-- `LinearMap.mem_range : w ∈ LinearMap.range h ↔ ∃ v, h v = w`. -/
TheoremDoc LinearMap.mem_range as "mem_range" in "Maps"
/-- `LinearMap.mem_range_self h v : h v ∈ LinearMap.range h`. -/
TheoremDoc LinearMap.mem_range_self as "mem_range_self" in "Maps"
/-- `LinearMap.ker_eq_bot : LinearMap.ker h = ⊥ ↔ Function.Injective h` — one-to-one iff the
null space is $\{\vec 0\}$ (the Mathlib form of what you proved). -/
TheoremDoc LinearMap.ker_eq_bot as "ker_eq_bot" in "Maps"
/-- `LinearMap.ker_eq_bot' : LinearMap.ker h = ⊥ ↔ ∀ v, h v = 0 → v = 0`. -/
TheoremDoc LinearMap.ker_eq_bot' as "ker_eq_bot'" in "Maps"
/-- `LinearMap.range_eq_top : LinearMap.range h = ⊤ ↔ Function.Surjective h` — onto iff the range
is all of $W$. -/
TheoremDoc LinearMap.range_eq_top as "range_eq_top" in "Maps"

/-- **Rank–nullity** (Hefferon Theorem Three.II.2.14), granted:
`LinearMap.finrank_range_add_finrank_ker h : finrank ℝ (range h) + finrank ℝ (ker h) = finrank ℝ V`
for finite-dimensional `V`. -/
TheoremDoc LinearMap.finrank_range_add_finrank_ker as "rank–nullity" in "Dimension"
/-- `Submodule.finrank_le U : finrank ℝ U ≤ finrank ℝ V` — a subspace has dimension at most
that of the space. -/
TheoremDoc Submodule.finrank_le as "Submodule.finrank_le" in "Dimension"
/-- `Submodule.finrank_eq_zero : finrank ℝ U = 0 ↔ U = ⊥` — only the trivial subspace has
dimension $0$. -/
TheoremDoc Submodule.finrank_eq_zero as "Submodule.finrank_eq_zero" in "Dimension"
/-- `finrank_top ℝ V : finrank ℝ (⊤ : Submodule ℝ V) = finrank ℝ V`. -/
TheoremDoc finrank_top as "finrank_top" in "Dimension"
/-- `Submodule.eq_top_of_finrank_eq : finrank ℝ U = finrank ℝ V → U = ⊤` — a subspace of full
dimension is the whole (finite-dimensional) space. This is Sheet 4 Q10(b). -/
TheoremDoc Submodule.eq_top_of_finrank_eq as "eq_top_of_finrank_eq" in "Dimension"
/-- `finrank_eq_one_iff' : finrank ℝ U = 1 ↔ ∃ v, v ≠ 0 ∧ ∀ w : U, ∃ c, c • v = w` — a
one-dimensional space is spanned by any one nonzero vector of it. -/
TheoremDoc finrank_eq_one_iff' as "finrank_eq_one_iff'" in "Dimension"
/-- `Submodule.coe_smul : ((r • x : U) : V) = r • (x : V)`. -/
TheoremDoc Submodule.coe_smul as "Submodule.coe_smul" in "Subspaces"
/-- `LinearMap.comp_apply : (g ∘ₗ f) v = g (f v)`. -/
TheoremDoc LinearMap.comp_apply as "comp_apply" in "Maps"
/-- `LinearMap.smul_apply : (r • f) v = r • f v`. -/
TheoremDoc LinearMap.smul_apply as "LinearMap.smul_apply" in "Maps"
/-- `e.symm_apply_apply v : e.symm (e v) = v`. -/
TheoremDoc LinearEquiv.symm_apply_apply as "symm_apply_apply" in "Isomorphisms"

/-- Mathlib: Injective ⇔ ker = ⊥ in finite dimension etc. Disabled where it is the question. -/
TheoremDoc LinearMap.finrank_range_of_inj as "finrank_range_of_inj" in "Dimension"
/-- Mathlib: same dimension ⇒ (one-to-one ⇔ onto). Disabled where it is the question. -/
TheoremDoc LinearMap.injective_iff_surjective_of_finrank_eq_finrank as
  "injective_iff_surjective_of_finrank_eq_finrank" in "Dimension"
/-- Mathlib: for an endomorphism, one-to-one ⇔ onto. Disabled where it is the question. -/
TheoremDoc LinearMap.injective_iff_surjective as "injective_iff_surjective" in "Dimension"
/-- Mathlib: same dimension ⇒ (ker = ⊥ ⇔ range = ⊤). Disabled where it is the question. -/
TheoremDoc LinearMap.ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank as
  "ker_eq_bot_iff_range_eq_top_of_finrank_eq_finrank" in "Dimension"

/-! ## Theorems proved in these worlds -/

/-- $\dim V = n \iff V \cong \mathbb R^n$ (Hefferon Theorem Three.I.2.3, specialised). -/
TheoremDoc LinearAlgebraGame.finrank_eq_iff_iso_fin as "finrank_eq_iff_iso_fin" in "Isomorphisms"
/-- `hom_map_zero h : h 0 = 0` — Hefferon Lemma Three.II.1.6. -/
TheoremDoc LinearAlgebraGame.hom_map_zero as "hom_map_zero" in "Maps"
/-- `image_seg h u v : h '' seg u v = seg (h u) (h v)` — Sheet 5 Q3(a). -/
TheoremDoc LinearAlgebraGame.image_seg as "image_seg" in "Maps"
/-- `inj_iff_kernel h : Function.Injective h ↔ ∀ v, h v = 0 → v = 0`. -/
TheoremDoc LinearAlgebraGame.inj_iff_kernel as "inj_iff_kernel" in "Maps"
/-- `inj_iff_rank h : Function.Injective h ↔ finrank ℝ (range h) = finrank ℝ V`
(finite-dimensional `V`) — Theorem 2.20 (1) ⇔ (4). -/
TheoremDoc LinearAlgebraGame.inj_iff_rank as "inj_iff_rank" in "Dimension"
/-- `onto_iff_rank h : Function.Surjective h ↔ finrank ℝ (range h) = finrank ℝ W`
(finite-dimensional `W`) — Sheet 6 Q4(a). -/
TheoremDoc LinearAlgebraGame.onto_iff_rank as "onto_iff_rank" in "Dimension"

/-! ## Axioms-world lemmas re-documented (the Axioms docs are not imported here) -/

/-- $(r+s)\cdot v = r\cdot v + s\cdot v$ — Hefferon's condition (7). -/
TheoremDoc add_smul as "add_smul" in "Axioms"
/-- $v + \vec 0 = v$ — Hefferon's condition (4). -/
TheoremDoc add_zero as "add_zero" in "Axioms"
/-- $\vec 0 + v = v$. -/
TheoremDoc zero_add as "zero_add" in "Axioms"
/-- $1 \cdot v = v$ — Hefferon's condition (10). -/
TheoremDoc one_smul as "one_smul" in "Axioms"
/-- `congrFun h a : f a = g a` for `h : f = g` — equal functions agree at every input
(for vectors: equal vectors have equal coordinates). -/
TheoremDoc congrFun as "congrFun" in "Maps"
