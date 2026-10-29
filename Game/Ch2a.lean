import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Two, part 1 (Hefferon Two.I–II)

Game-local definitions for the worlds
`Axioms`, `Subspaces`, `Independence` and `FromScratch`.
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

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
