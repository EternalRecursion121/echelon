import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Two, part 1 (Hefferon Two.I–II)

Game-local definitions and all `TheoremDoc` / `DefinitionDoc` entries for the worlds
`Axioms`, `Subspaces`, `Independence` and `FromScratch`. -/

namespace LinearAlgebraGame

/-! ## Game-local definitions -/

/-- Sheet 3 Q1: quadratics $a_0 + a_1x + a_2x^2$ with all three coefficients positive. -/
structure PosQuad where
  a₀ : ℝ
  a₁ : ℝ
  a₂ : ℝ
  pos₀ : 0 < a₀
  pos₁ : 0 < a₁
  pos₂ : 0 < a₂

/-- The usual addition of polynomials, which does stay inside `PosQuad`. -/
def PosQuad.add (p q : PosQuad) : PosQuad :=
  ⟨p.a₀ + q.a₀, p.a₁ + q.a₁, p.a₂ + q.a₂, add_pos p.pos₀ q.pos₀, add_pos p.pos₁ q.pos₁,
    add_pos p.pos₂ q.pos₂⟩

theorem PosQuad.add_a₀ (p q : PosQuad) : (p.add q).a₀ = p.a₀ + q.a₀ := rfl

/-- The positive reals $\mathbb{R}^+$, as a subtype. -/
abbrev PosReal := {x : ℝ // 0 < x}

/-- Independence of three vectors is "only the trivial relation". -/
theorem linIndep_three_iff {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V) :
    LinearIndependent ℝ ![u, v, w] ↔
      ∀ a b c : ℝ, a • u + b • v + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro h a b c habc
    have key := h ![a, b, c] (by simpa [Fin.sum_univ_three] using habc)
    exact ⟨by simpa using key 0, by simpa using key 1, by simpa using key 2⟩
  · intro h g hg i
    have hg' : g 0 • u + g 1 • v + g 2 • w = 0 := by simpa [Fin.sum_univ_three] using hg
    obtain ⟨h0, h1, h2⟩ := h _ _ _ hg'
    fin_cases i <;> assumption

/-! ### From Scratch world: the game's own definitions -/

/-- Hefferon's Definition Two.I.2.1, unpacked: `S` contains `0` and is closed under `+` and `•`. -/
structure IsSubsp {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V) : Prop where
  zero_mem : (0 : V) ∈ S
  add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S
  smul_mem : ∀ (c : ℝ) x, x ∈ S → c • x ∈ S

/-- The span of finitely many vectors: all their linear combinations (Definition Two.I.2.13). -/
def spanOf {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) : Set V :=
  {x | ∃ c : Fin n → ℝ, ∑ i, c i • v i = x}

theorem mem_spanOf {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) (x : V) :
    x ∈ spanOf v ↔ ∃ c : Fin n → ℝ, ∑ i, c i • v i = x := Iff.rfl

/-- Linear independence as "only the trivial relation" (Lemma Two.II.1.5). -/
def LinIndep {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) : Prop :=
  ∀ c : Fin n → ℝ, ∑ i, c i • v i = 0 → ∀ i, c i = 0

/-! ### Granted helpers -/

/-- A subspace and its set of vectors: if `(W : Set V) = S` then membership in `W` is
membership in `S`. -/
theorem mem_iff_of_coe_eq {V : Type*} [AddCommGroup V] [Module ℝ V] {W : Submodule ℝ V}
    {S : Set V} (hW : (W : Set V) = S) {x : V} : x ∈ W ↔ x ∈ S := by
  rw [← hW]; rfl

open Matrix in
/-- Sheet 3 Q3(d)'s "fact", part 1: the solution set of `A x = 0` is infinite exactly when the
null space `LinearMap.ker A.mulVecLin` (the same set, viewed as a vector space) is. -/
theorem solutionSet_infinite_iff {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    Set.Infinite {x : Fin n → ℝ | A *ᵥ x = 0} ↔ Infinite (LinearMap.ker A.mulVecLin) := by
  rw [← Set.infinite_coe_iff]; rfl

open Matrix in
/-- Sheet 3 Q3(d)'s "fact", part 2: a nonzero solution is a nonzero vector of the null space. -/
theorem solution_ne_zero {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) {x : Fin n → ℝ}
    (hx : A *ᵥ x = 0) (hx0 : x ≠ 0) : (⟨x, hx⟩ : LinearMap.ker A.mulVecLin) ≠ 0 := by
  intro h; exact hx0 (congrArg Subtype.val h)

/-- Linear combinations of differentiable functions are differentiable. -/
theorem differentiable_comb {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (c₁ c₂ : ℝ) : Differentiable ℝ (c₁ • f + c₂ • g) :=
  (hf.const_smul c₁).add (hg.const_smul c₂)

/-- Differentiation is linear. -/
theorem deriv_comb {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (c₁ c₂ x : ℝ) : deriv (c₁ • f + c₂ • g) x = c₁ * deriv f x + c₂ * deriv g x := by
  rw [deriv_add ((hf.const_smul c₁) x) ((hg.const_smul c₂) x), deriv_const_smul c₁ (hf x),
    deriv_const_smul c₂ (hg x), smul_eq_mul, smul_eq_mul]

end LinearAlgebraGame

/-! ## Definitions -/

/-- `VectorSpaceAxioms V add smul` says that the set `V` with the operations `add` and
`smul` satisfies Hefferon's ten conditions (Definition Two.I.1.1). Closure (conditions 1
and 6) is automatic, because `add : V → V → V` and `smul : ℝ → V → V` land in `V`. The
other conditions are the fields

* `add_comm : ∀ u v, add u v = add v u` — condition (2)
* `add_assoc : ∀ u v w, add (add u v) w = add u (add v w)` — condition (3)
* `has_zero_neg : ∃ z, (∀ v, add v z = v) ∧ ∀ v, ∃ w, add v w = z` — conditions (4) and (5):
  there is a zero vector `z`, and every `v` has an inverse `w` with `v + w = z`
* `add_smul : ∀ r s v, smul (r + s) v = add (smul r v) (smul s v)` — condition (7)
* `smul_add : ∀ r u v, smul r (add u v) = add (smul r u) (smul r v)` — condition (8)
* `mul_smul : ∀ r s v, smul (r * s) v = smul r (smul s v)` — condition (9)
* `one_smul : ∀ v, smul 1 v = v` — condition (10)

If `h : VectorSpaceAxioms V add smul` then `h.has_zero_neg` is the zero-and-inverse condition,
and so on: `obtain ⟨z, hz, hneg⟩ := h.has_zero_neg` names the zero `z`, `hz : ∀ v, add v z = v`
and `hneg : ∀ v, ∃ w, add v w = z`. To *prove* `VectorSpaceAxioms …`, use `constructor`
(seven goals). -/
DefinitionDoc LinearAlgebraGame.VectorSpaceAxioms as "VectorSpaceAxioms"

/-- `PosQuad` is the set $P$ of Sheet 3 Q1: a record of three reals `a₀ a₁ a₂` with proofs
`pos₀ : 0 < a₀`, `pos₁ : 0 < a₁`, `pos₂ : 0 < a₂`. `PosQuad.add` is the usual addition.
If `p : PosQuad` then `p.a₀` is its constant coefficient and `p.pos₀` says it is positive. -/
DefinitionDoc LinearAlgebraGame.PosQuad as "PosQuad"

/-- `PosReal` is $\mathbb{R}^+ = \{x \in \mathbb{R} \mid x > 0\}$. An element is a pair
`⟨x, hx⟩` of a real `x` and a proof `hx : 0 < x`; `p.1` is the real number. -/
DefinitionDoc LinearAlgebraGame.PosReal as "PosReal"

/-! ## Theorems: Axioms world -/

/-- $(r+s)\cdot v = r\cdot v + s\cdot v$ — Hefferon's condition (7). -/
TheoremDoc add_smul as "add_smul" in "Vector spaces"
/-- $v + \vec 0 = v$ — Hefferon's condition (4). -/
TheoremDoc add_zero as "add_zero" in "Vector spaces"
/-- If $a + b = a + c$ then $b = c$. -/
TheoremDoc add_left_cancel as "add_left_cancel" in "Vector spaces"
/-- Mathlib's version of $0\cdot v = \vec 0$; disabled while you prove it. -/
TheoremDoc zero_smul as "zero_smul" in "Vector spaces"
/-- $(a + b) + c = a + (b + c)$ — Hefferon's condition (3). -/
TheoremDoc add_assoc as "add_assoc" in "Vector spaces"
/-- $\vec 0 + v = v$. -/
TheoremDoc zero_add as "zero_add" in "Vector spaces"
/-- disabled -/
TheoremDoc neg_eq_of_add_eq_zero_right as "neg_eq_of_add_eq_zero_right" in "Vector spaces"
/-- disabled -/
TheoremDoc neg_eq_of_add_eq_zero_left as "neg_eq_of_add_eq_zero_left" in "Vector spaces"
/-- $1 \cdot v = v$ — Hefferon's condition (10). -/
TheoremDoc one_smul as "one_smul" in "Vector spaces"
/-- $-a + a = 0$ (in ℝ, or in any group). -/
TheoremDoc neg_add_cancel as "neg_add_cancel" in "Vector spaces"
/-- Mathlib's $(-1)\cdot v = -v$; disabled while you prove it. -/
TheoremDoc neg_one_smul as "neg_one_smul" in "Vector spaces"

/-- `zero_smul_eq_zero v : (0:ℝ) • v = 0` — Lemma Two.I.1.16 (1), proved in Axioms level 1. -/
TheoremDoc LinearAlgebraGame.zero_smul_eq_zero as "zero_smul_eq_zero" in "Vector spaces"
/-- `neg_one_smul_add v : (-1 : ℝ) • v + v = 0` — Lemma Two.I.1.16 (2). -/
TheoremDoc LinearAlgebraGame.neg_one_smul_add as "neg_one_smul_add" in "Vector spaces"

/-- `smul_smul r s v : r • (s • v) = (r * s) • v` — Hefferon's condition (9), read right to left. -/
TheoremDoc smul_smul as "smul_smul" in "Vector spaces"
/-- `smul_zero r : r • 0 = 0` — a scalar times the zero vector is the zero vector
(Lemma Two.I.1.16 (3)). -/
TheoremDoc smul_zero as "smul_zero" in "Vector spaces"
/-- `inv_mul_cancel₀ (h : r ≠ 0) : r⁻¹ * r = 1`. -/
TheoremDoc inv_mul_cancel₀ as "inv_mul_cancel₀" in "Vector spaces"
/-- `sub_smul r s v : (r - s) • v = r • v - s • v`. -/
TheoremDoc sub_smul as "sub_smul" in "Vector spaces"
/-- `sub_self a : a - a = 0`. -/
TheoremDoc sub_self as "sub_self" in "Vector spaces"
/-- disabled: this is Sheet 3 Q3(a) -/
TheoremDoc smul_eq_zero as "smul_eq_zero" in "Vector spaces"
/-- disabled: this is Sheet 3 Q3(a) -/
TheoremDoc smul_eq_zero_iff_left as "smul_eq_zero_iff_left" in "Vector spaces"
/-- disabled -/
TheoremDoc smul_eq_zero_iff_right as "smul_eq_zero_iff_right" in "Vector spaces"
/-- disabled -/
TheoremDoc smul_ne_zero_iff as "smul_ne_zero_iff" in "Vector spaces"
/-- disabled: this is Sheet 3 Q3(b) -/
TheoremDoc smul_left_injective as "smul_left_injective" in "Vector spaces"
/-- disabled -/
TheoremDoc smul_right_injective as "smul_right_injective" in "Vector spaces"
/-- disabled: this is Sheet 3 Q3(b) -/
TheoremDoc smul_left_inj as "smul_left_inj" in "Vector spaces"
/-- disabled -/
TheoremDoc smul_right_inj as "smul_right_inj" in "Vector spaces"

/-- `smul_eq_zero_iff_of_ne v hv r : r • v = 0 ↔ r = 0` when `hv : v ≠ 0` (Sheet 3 Q3(a)). -/
TheoremDoc LinearAlgebraGame.smul_eq_zero_iff_of_ne as "smul_eq_zero_iff_of_ne" in "Vector spaces"
/-- `smul_cancel_iff v hv r₁ r₂ : r₁ • v = r₂ • v ↔ r₁ = r₂` when `hv : v ≠ 0`
(Sheet 3 Q3(b)). -/
TheoremDoc LinearAlgebraGame.smul_cancel_iff as "smul_cancel_iff" in "Vector spaces"
/-- `infinite_of_ne_zero v hv : Infinite V` when `hv : v ≠ 0` — a nontrivial vector space is
infinite (Sheet 3 Q3(c)). -/
TheoremDoc LinearAlgebraGame.infinite_of_ne_zero as "infinite_of_ne_zero" in "Vector spaces"

/-- `Infinite.of_injective f hf : Infinite β` when `f : α → β` is injective and `α` is
infinite (here: `α = ℝ`). -/
TheoremDoc Infinite.of_injective as "Infinite.of_injective" in "Vector spaces"
/-- `Set.infinite_coe_iff : Infinite S ↔ S.Infinite` — "the set `S`, viewed as a type, is
infinite" and "`S` is an infinite set" say the same thing. -/
TheoremDoc Set.infinite_coe_iff as "Set.infinite_coe_iff" in "Vector spaces"
/-- `solutionSet_infinite_iff A : Set.Infinite {x | A *ᵥ x = 0} ↔ Infinite (LinearMap.ker A.mulVecLin)`
— the solution set is infinite iff the null space (the same set, as a vector space) is.
Granted (Sheet 3 Q3(d)'s "fact"). -/
TheoremDoc LinearAlgebraGame.solutionSet_infinite_iff as "solutionSet_infinite_iff" in "Vector spaces"
/-- `solution_ne_zero A hx hx0 : (⟨x, hx⟩ : LinearMap.ker A.mulVecLin) ≠ 0` for a solution
`hx : A *ᵥ x = 0` with `hx0 : x ≠ 0` — a nonzero solution is a nonzero vector of the null space.
Granted. -/
TheoremDoc LinearAlgebraGame.solution_ne_zero as "solution_ne_zero" in "Vector spaces"
/-- `Matrix.mulVec_zero A : A *ᵥ 0 = 0`. -/
TheoremDoc Matrix.mulVec_zero as "mulVec_zero" in "Vector spaces"

/-- `PosQuad.add_a₀ p q : (p.add q).a₀ = p.a₀ + q.a₀` — sums are added coefficientwise. -/
TheoremDoc LinearAlgebraGame.PosQuad.add_a₀ as "PosQuad.add_a₀" in "Vector spaces"
/-- `irrational_sqrt_two : Irrational √2`. -/
TheoremDoc irrational_sqrt_two as "irrational_sqrt_two" in "Vector spaces"
/-- `Irrational.ne_rat h q : x ≠ q` for `h : Irrational x` and a rational `q`. -/
TheoremDoc Irrational.ne_rat as "Irrational.ne_rat" in "Vector spaces"
/-- `Rat.cast_one : ((1 : ℚ) : ℝ) = 1`. -/
TheoremDoc Rat.cast_one as "Rat.cast_one" in "Vector spaces"
/-- `mul_one a : a * 1 = a`. -/
TheoremDoc mul_one as "mul_one" in "Vector spaces"
/-- `Pi.add_apply f g x : (f + g) x = f x + g x` — functions are added pointwise. -/
TheoremDoc Pi.add_apply as "Pi.add_apply" in "Vector spaces"
/-- `Pi.smul_apply r f x : (r • f) x = r • f x` — functions are scaled pointwise. -/
TheoremDoc Pi.smul_apply as "Pi.smul_apply" in "Vector spaces"
/-- `Pi.zero_apply x : (0 : ℝ → ℝ) x = 0` — the zero function. -/
TheoremDoc Pi.zero_apply as "Pi.zero_apply" in "Vector spaces"
/-- `Pi.neg_apply f x : (-f) x = -f x`. -/
TheoremDoc Pi.neg_apply as "Pi.neg_apply" in "Vector spaces"
/-- `smul_eq_mul a b : a • b = a * b` for real numbers. -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Vector spaces"
/-- `mul_add a b c : a * (b + c) = a * b + a * c`. -/
TheoremDoc mul_add as "mul_add" in "Vector spaces"

/-! ## Theorems: Subspaces world -/

/-- `subspace_test S hne h : ∃ W : Submodule ℝ V, (W : Set V) = S` — Lemma Two.I.2.9: a
nonempty set `S` closed under pairwise combinations (`h : ∀ c₁ c₂ s₁ s₂, s₁ ∈ S → s₂ ∈ S →
c₁ • s₁ + c₂ • s₂ ∈ S`) is a subspace. Use it with `apply subspace_test`. -/
TheoremDoc LinearAlgebraGame.subspace_test as "subspace_test" in "Subspaces"
/-- `span_smallest v`: the span of the vectors `v i` contains each of them, and is contained
in every subspace that contains them all (Lemma Two.I.2.15). -/
TheoremDoc LinearAlgebraGame.span_smallest as "span_smallest" in "Subspaces"
/-- `mem_iff_of_coe_eq hW : x ∈ W ↔ x ∈ S` when `hW : (W : Set V) = S`.

A subspace `W` and its *set of vectors* `(W : Set V)` (displayed `↑W`) look alike but are
different objects, so `rw [hW]` cannot rewrite `x ∈ W`. This lemma moves membership across:
`rw [mem_iff_of_coe_eq hW] at h` turns `h : x ∈ W` into `h : x ∈ S`, and
`rw [mem_iff_of_coe_eq hW]` does the same to the goal. -/
TheoremDoc LinearAlgebraGame.mem_iff_of_coe_eq as "mem_iff_of_coe_eq" in "Subspaces"
/-- `differentiable_comb hf hg c₁ c₂ : Differentiable ℝ (c₁ • f + c₂ • g)` for differentiable
`f`, `g`. -/
TheoremDoc LinearAlgebraGame.differentiable_comb as "differentiable_comb" in "Subspaces"
/-- `deriv_comb hf hg c₁ c₂ x : deriv (c₁ • f + c₂ • g) x = c₁ * deriv f x + c₂ * deriv g x`
for differentiable `f`, `g` — differentiation is linear. -/
TheoremDoc LinearAlgebraGame.deriv_comb as "deriv_comb" in "Subspaces"
/-- `Set.mem_ofPred_eq : (a ∈ {x | p x}) = p a` — unfold membership in a set-builder set. -/
TheoremDoc Set.mem_ofPred_eq as "Set.mem_ofPred_eq" in "Subspaces"
/-- `W.zero_mem : 0 ∈ W` — every subspace contains the zero vector. -/
TheoremDoc Submodule.zero_mem as "Submodule.zero_mem" in "Subspaces"
/-- `W.add_mem hx hy : x + y ∈ W` for `hx : x ∈ W`, `hy : y ∈ W`. -/
TheoremDoc Submodule.add_mem as "Submodule.add_mem" in "Subspaces"
/-- `W.smul_mem c hx : c • x ∈ W` for `hx : x ∈ W`. -/
TheoremDoc Submodule.smul_mem as "Submodule.smul_mem" in "Subspaces"
/-- `W.sub_mem hx hy : x - y ∈ W` for `hx : x ∈ W`, `hy : y ∈ W`. -/
TheoremDoc Submodule.sub_mem as "Submodule.sub_mem" in "Subspaces"
/-- `Submodule.sum_mem W h : ∑ i ∈ s, f i ∈ W` if `h : ∀ i ∈ s, f i ∈ W`. -/
TheoremDoc Submodule.sum_mem as "Submodule.sum_mem" in "Subspaces"
/-- `Submodule.subset_span : S ⊆ span ℝ S` — every vector of `S` is in its span. -/
TheoremDoc Submodule.subset_span as "Submodule.subset_span" in "Subspaces"
/-- `Set.mem_range_self i : f i ∈ Set.range f`. -/
TheoremDoc Set.mem_range_self as "Set.mem_range_self" in "Subspaces"
/-- `Submodule.mem_span_range_iff_exists_fun ℝ : x ∈ span ℝ (Set.range v) ↔ ∃ c, ∑ i, c i • v i = x`
— the span of finitely many vectors is the set of their linear combinations
(Definition Two.I.2.13). -/
TheoremDoc Submodule.mem_span_range_iff_exists_fun as "mem_span_range_iff_exists_fun" in "Subspaces"
/-- `Submodule.span_le : span ℝ S ≤ W ↔ S ⊆ W` — the span is the smallest subspace containing
`S` (Lemma Two.I.2.15, proved in Subspaces level 6). -/
TheoremDoc Submodule.span_le as "Submodule.span_le" in "Subspaces"
/-- `Matrix.mulVec_add A x y : A *ᵥ (x + y) = A *ᵥ x + A *ᵥ y`. -/
TheoremDoc Matrix.mulVec_add as "mulVec_add" in "Subspaces"
/-- `Matrix.mulVec_smul A c x : A *ᵥ (c • x) = c • (A *ᵥ x)`. -/
TheoremDoc Matrix.mulVec_smul as "mulVec_smul" in "Subspaces"
/-- `Matrix.one_mulVec x : 1 *ᵥ x = x` — the identity matrix fixes every vector. -/
TheoremDoc Matrix.one_mulVec as "one_mulVec" in "Subspaces"
/-- `neg_zero : -0 = 0`. -/
TheoremDoc neg_zero as "neg_zero" in "Subspaces"
/-- `mul_zero a : a * 0 = 0`. -/
TheoremDoc MulZeroClass.mul_zero as "mul_zero" in "Subspaces"
/-- `Pi.zero_def : (0 : ℝ → ℝ) = fun _ => 0`. -/
TheoremDoc Pi.zero_def as "Pi.zero_def" in "Subspaces"
/-- `differentiable_const c : Differentiable ℝ (fun _ => c)` — constants are differentiable. -/
TheoremDoc differentiable_const as "differentiable_const" in "Subspaces"
/-- `hf.add hg : Differentiable ℝ (f + g)` for differentiable `f`, `g`. -/
TheoremDoc Differentiable.add as "Differentiable.add" in "Subspaces"
/-- `hf.const_smul c : Differentiable ℝ (c • f)` for differentiable `f`. -/
TheoremDoc Differentiable.const_smul as "Differentiable.const_smul" in "Subspaces"
/-- `deriv_add hf hg : deriv (f + g) x = deriv f x + deriv g x`, where
`hf : DifferentiableAt ℝ f x` and `hg : DifferentiableAt ℝ g x` (get these from
`Differentiable` hypotheses by applying them to `x`). -/
TheoremDoc deriv_add as "deriv_add" in "Subspaces"
/-- `deriv_const_smul c hf : deriv (c • f) x = c • deriv f x`, where
`hf : DifferentiableAt ℝ f x`. -/
TheoremDoc deriv_const_smul as "deriv_const_smul" in "Subspaces"
/-- `deriv_const x c : deriv (fun _ => c) x = 0`. -/
TheoremDoc deriv_const as "deriv_const" in "Subspaces"
/-- disabled -/
TheoremDoc Submodule.coe_inf as "Submodule.coe_inf" in "Subspaces"
/-- disabled -/
TheoremDoc Submodule.mem_inf as "Submodule.mem_inf" in "Subspaces"
/-- `union_subspace_of_subset A B h : ∃ W : Submodule ℝ V, (W : Set V) = A ∪ B` when
`h : (A : Set V) ⊆ B ∨ (B : Set V) ⊆ A` — nested subspaces have a subspace as union
(Subspaces level 9). -/
TheoremDoc LinearAlgebraGame.union_subspace_of_subset as "union_subspace_of_subset" in "Subspaces"
/-- `Set.not_subset : ¬ s ⊆ t ↔ ∃ a ∈ s, a ∉ t`. -/
TheoremDoc Set.not_subset as "Set.not_subset" in "Subspaces"
/-- `add_sub_cancel_left a b : a + b - a = b`. -/
TheoremDoc add_sub_cancel_left as "add_sub_cancel_left" in "Subspaces"
/-- `add_sub_cancel_right a b : a + b - b = a`. -/
TheoremDoc add_sub_cancel_right as "add_sub_cancel_right" in "Subspaces"
/-- `Set.union_eq_self_of_subset_left (h : s ⊆ t) : s ∪ t = t`. -/
TheoremDoc Set.union_eq_self_of_subset_left as "Set.union_eq_self_of_subset_left" in "Subspaces"
/-- `Set.union_eq_self_of_subset_right (h : t ⊆ s) : s ∪ t = s`. -/
TheoremDoc Set.union_eq_self_of_subset_right as "Set.union_eq_self_of_subset_right" in "Subspaces"

/-! ## Theorems: Independence world -/

/-- `isolate_of_relation u v w a b c h ha : u = (-b / a) • v + (-c / a) • w` — a vector with a
nonzero coefficient in a relation is a combination of the others (Lemma Two.II.1.5). -/
TheoremDoc LinearAlgebraGame.isolate_of_relation as "isolate_of_relation" in "Independence"
/-- `Fintype.linearIndependent_iff : LinearIndependent ℝ v ↔ ∀ g, ∑ i, g i • v i = 0 → ∀ i, g i = 0`
— Lemma Two.II.1.5 for a finite family: only the trivial relation. -/
TheoremDoc Fintype.linearIndependent_iff as "Fintype.linearIndependent_iff" in "Independence"
/-- `Fintype.not_linearIndependent_iff : ¬ LinearIndependent ℝ v ↔ ∃ g, ∑ i, g i • v i = 0 ∧ ∃ i, g i ≠ 0`
— dependent means some nontrivial relation. -/
TheoremDoc Fintype.not_linearIndependent_iff as "Fintype.not_linearIndependent_iff" in "Independence"
/-- `LinearIndependent.pair_iff : LinearIndependent ℝ ![x, y] ↔ ∀ s t, s • x + t • y = 0 → s = 0 ∧ t = 0`. -/
TheoremDoc LinearIndependent.pair_iff as "LinearIndependent.pair_iff" in "Independence"
/-- `linIndep_three_iff u v w : LinearIndependent ℝ ![u, v, w] ↔
∀ a b c, a • u + b • v + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0`. -/
TheoremDoc LinearAlgebraGame.linIndep_three_iff as "linIndep_three_iff" in "Independence"
/-- `linearIndependent_iff'`: `LinearIndependent ℝ v ↔ ∀ (s : Finset ι) (g : ι → ℝ),
∑ i ∈ s, g i • v i = 0 → ∀ i ∈ s, g i = 0` — for families with infinitely many members,
relations involve only finitely many of them. -/
TheoremDoc linearIndependent_iff' as "linearIndependent_iff'" in "Independence"
/-- `Fin.sum_univ_four f : ∑ i : Fin 4, f i = f 0 + f 1 + f 2 + f 3`. -/
TheoremDoc Fin.sum_univ_four as "Fin.sum_univ_four" in "Independence"
/-- `one_pos : 0 < 1`. -/
TheoremDoc one_pos as "one_pos" in "Independence"
/-- `two_pos : 0 < 2`. -/
TheoremDoc two_pos as "two_pos" in "Independence"
/-- `Real.sin_sq_add_cos_sq x : sin x ^ 2 + cos x ^ 2 = 1`. -/
TheoremDoc Real.sin_sq_add_cos_sq as "Real.sin_sq_add_cos_sq" in "Independence"
/-- `span_insert_iff S v : v ∈ span ℝ S ↔ span ℝ (insert v S) = span ℝ S` — Lemma Two.II.1.2. -/
TheoremDoc LinearAlgebraGame.span_insert_iff as "span_insert_iff" in "Independence"
/-- `extension_lemma u w x hli` — for independent `u, w`: `u, w, x` independent iff
`x ∉ span {u, w}` (Lemma Two.II.1.15). -/
TheoremDoc LinearAlgebraGame.extension_lemma as "extension_lemma" in "Independence"
/-- `indep_pair_of_indep_three u v w h : LinearIndependent ℝ ![u, v]` from
`h : LinearIndependent ℝ ![u, v, w]` — a subset of an independent set is independent
(Lemma Two.II.1.20, Independence level 9). -/
TheoremDoc LinearAlgebraGame.indep_pair_of_indep_three as "indep_pair_of_indep_three" in "Independence"
/-- `pair_dependent_iff u v : ¬ LinearIndependent ℝ ![u, v] ↔ u = 0 ∨ v ∈ span ℝ {u}` — two
vectors are dependent iff the first is zero or the second is a multiple of the first
(Independence level 12). -/
TheoremDoc LinearAlgebraGame.pair_dependent_iff as "pair_dependent_iff" in "Independence"
/-- `le_antisymm : a ≤ b → b ≤ a → a = b` — for subspaces: mutual inclusion gives equality. -/
TheoremDoc le_antisymm as "le_antisymm" in "Independence"
/-- `Submodule.span_mono : S ⊆ T → span ℝ S ≤ span ℝ T`. -/
TheoremDoc Submodule.span_mono as "Submodule.span_mono" in "Independence"
/-- `Set.subset_insert v S : S ⊆ insert v S`. -/
TheoremDoc Set.subset_insert as "Set.subset_insert" in "Independence"
/-- `Set.mem_insert v S : v ∈ insert v S`. -/
TheoremDoc Set.mem_insert as "Set.mem_insert" in "Independence"
/-- disabled: this is Lemma Two.II.1.2 -/
TheoremDoc Submodule.span_insert_eq_span as "Submodule.span_insert_eq_span" in "Independence"
/-- disabled -/
TheoremDoc Submodule.mem_span_insert as "Submodule.mem_span_insert" in "Independence"
/-- `Submodule.mem_span_pair : z ∈ span ℝ {x, y} ↔ ∃ a b, a • x + b • y = z`. -/
TheoremDoc Submodule.mem_span_pair as "Submodule.mem_span_pair" in "Independence"
/-- `Submodule.mem_span_singleton : x ∈ span ℝ {y} ↔ ∃ a, a • y = x`. -/
TheoremDoc Submodule.mem_span_singleton as "Submodule.mem_span_singleton" in "Independence"
/-- `Set.pair_comm a b : {a, b} = {b, a}`. -/
TheoremDoc Set.pair_comm as "Set.pair_comm" in "Independence"
/-- `Set.insert_comm a b s : insert a (insert b s) = insert b (insert a s)`. -/
TheoremDoc Set.insert_comm as "Set.insert_comm" in "Independence"
/-- `smul_eq_zero : r • v = 0 ↔ r = 0 ∨ v = 0` (you proved the key case in the Ten Conditions
world, Sheet 3 Q3(a)). -/
TheoremDoc smul_eq_zero as "smul_eq_zero" in "Independence"
/-- `Finset.smul_sum : r • ∑ i ∈ s, f i = ∑ i ∈ s, r • f i` — a scalar times a sum is the sum
of the scaled terms. -/
TheoremDoc Finset.smul_sum as "Finset.smul_sum" in "Independence"
/-- `Finset.sum_apply x s f : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x` — sums of functions are
evaluated pointwise. -/
TheoremDoc Finset.sum_apply as "Finset.sum_apply" in "Independence"

/-! ## From Scratch world -/

/-- `IsSubsp S` (the game's own definition): `S` contains `0` and is closed under addition
and scalar multiplication. Its three fields: `h.zero_mem : 0 ∈ S`,
`h.add_mem : ∀ x y, x ∈ S → y ∈ S → x + y ∈ S`, `h.smul_mem : ∀ c x, x ∈ S → c • x ∈ S`.
To prove `IsSubsp S`, use `constructor`. -/
DefinitionDoc LinearAlgebraGame.IsSubsp as "IsSubsp"
/-- `spanOf v` (the game's own definition) is the set of all combinations `∑ i, c i • v i`.
`mem_spanOf` unfolds membership. -/
DefinitionDoc LinearAlgebraGame.spanOf as "spanOf"
/-- `LinIndep v` (the game's own definition): `∀ c, ∑ i, c i • v i = 0 → ∀ i, c i = 0`.
It is a `∀`, so `intro c h i` starts a proof. -/
DefinitionDoc LinearAlgebraGame.LinIndep as "LinIndep"
/-- `mem_spanOf v x : x ∈ spanOf v ↔ ∃ c, ∑ i, c i • v i = x`. -/
TheoremDoc LinearAlgebraGame.mem_spanOf as "mem_spanOf" in "From Scratch"
/-- `add_comm a b : a + b = b + a` — Hefferon's condition (2). -/
TheoremDoc add_comm as "add_comm" in "Vector spaces"
/-- `smul_add r u v : r • (u + v) = r • u + r • v` — Hefferon's condition (8). -/
TheoremDoc smul_add as "smul_add" in "Vector spaces"
/-- `add_neg_cancel a : a + -a = 0`. -/
TheoremDoc add_neg_cancel as "add_neg_cancel" in "Vector spaces"
/-- `Finset.sum_add_distrib : ∑ i ∈ s, (f i + g i) = ∑ i ∈ s, f i + ∑ i ∈ s, g i`. -/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "From Scratch"
/-- `Fin.sum_univ_two f : ∑ i : Fin 2, f i = f 0 + f 1`. -/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "From Scratch"
/-- `axioms_of_module V : VectorSpaceAxioms V (· + ·) (· • ·)` — every Mathlib real
vector space satisfies the ten conditions (From Scratch level 1). -/
TheoremDoc LinearAlgebraGame.axioms_of_module as "axioms_of_module" in "From Scratch"
/-- `scratch_subspace_test S : IsSubsp S ↔ S.Nonempty ∧ ∀ c₁ c₂ s₁ s₂, s₁ ∈ S → s₂ ∈ S →
c₁ • s₁ + c₂ • s₂ ∈ S` — Hefferon's subspace test for the game's own `IsSubsp`
(From Scratch level 2). -/
TheoremDoc LinearAlgebraGame.scratch_subspace_test as "scratch_subspace_test" in "From Scratch"
/-- `scratch_subspace_iff S : IsSubsp S ↔ ∃ W : Submodule ℝ V, (W : Set V) = S` — the game's
subspaces are exactly Mathlib's `Submodule`s. -/
TheoremDoc LinearAlgebraGame.scratch_subspace_iff as "scratch_subspace_iff" in "From Scratch"

/-! ## Logic helpers -/

/-- `congrArg f h : f a = f b` from `h : a = b` — apply the same function to both sides of an
equation (e.g. take a coordinate of an equation between vectors). -/
TheoremDoc congrArg as "congrArg" in "Vector spaces"
/-- `congrFun h x : f x = g x` from `h : f = g` — evaluate an equation between functions (or
vectors) at a point. -/
TheoremDoc congrFun as "congrFun" in "Independence"
