import GameServer
import Mathlib
import Game.Lib

/-! # Chapter One (Hefferon One.I–III) and the optional Puzzles

Game-local definitions for the worlds
`RowOps`, `DotProduct`, `Echelon` and `Puzzles`.
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

namespace LinearAlgebraGame

open Matrix

/-! ## Row Ops: counting solutions -/

/-- The system `S` (a condition on vectors `v : Fin n → ℝ`) has no solution. -/
def NoSolution {n : ℕ} (S : (Fin n → ℝ) → Prop) : Prop := ¬ ∃ v, S v

/-- The system `S` has exactly one solution. -/
def UniqueSolution {n : ℕ} (S : (Fin n → ℝ) → Prop) : Prop := ∃! v, S v

/-- The system `S` has infinitely many solutions. -/
def InfinitelyMany {n : ℕ} (S : (Fin n → ℝ) → Prop) : Prop := Set.Infinite {v | S v}

/-- Sheet 2 Q1's three-way answer: no solution, exactly one, or infinitely many. Choose with
`left` (none), `right; left` (unique) or `right; right` (infinitely many). -/
def Classify {n : ℕ} (S : (Fin n → ℝ) → Prop) : Prop :=
  NoSolution S ∨ UniqueSolution S ∨ InfinitelyMany S

/-- A whole line $\{\vec p + t\vec d\}$ ($\vec d \ne \vec 0$) of solutions means infinitely
many solutions. -/
theorem infinitelyMany_of_line {n : ℕ} {S : (Fin n → ℝ) → Prop} (p d : Fin n → ℝ) (i : Fin n)
    (hd : d i ≠ 0) (h : ∀ t : ℝ, S (p + t • d)) : InfinitelyMany S := by
  have hd' : d ≠ 0 := fun h0 => hd (by rw [h0]; rfl)
  refine Set.infinite_of_injective_forall_mem (f := fun t : ℝ => p + t • d) ?_ h
  intro s t hst
  have : (s - t) • d = 0 := by rw [sub_smul]; exact sub_eq_zero.mpr (add_left_cancel hst)
  exact sub_eq_zero.mp ((smul_eq_zero.mp this).resolve_right hd')

/-- Exactly one solution means: some `p` solves `S`, and every solution equals `p`. -/
theorem uniqueSolution_iff {n : ℕ} {S : (Fin n → ℝ) → Prop} :
    UniqueSolution S ↔ ∃ p, S p ∧ ∀ v, S v → v = p := Iff.rfl

/-- `x` is a rational number (the image of some `q : ℚ`). -/
def IsRat (x : ℝ) : Prop := ∃ q : ℚ, (q : ℝ) = x

/-! ## Dot Product: length -/

/-- Hefferon's length $|\vec v| = \sqrt{\vec v\cdot\vec v}$. -/
noncomputable def len {n : ℕ} (v : Fin n → ℝ) : ℝ := Real.sqrt (v ⬝ᵥ v)

theorem dot_self_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ v ⬝ᵥ v := by
  simpa using dotProduct_star_self_nonneg v

theorem len_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ len v := Real.sqrt_nonneg _

theorem len_sq {n : ℕ} (v : Fin n → ℝ) : len v ^ 2 = v ⬝ᵥ v :=
  Real.sq_sqrt (dot_self_nonneg v)

theorem dot_expand {n : ℕ} (u v : Fin n → ℝ) (a b : ℝ) :
    (a • u - b • v) ⬝ᵥ (a • u - b • v) =
      a ^ 2 * (u ⬝ᵥ u) - 2 * a * b * (u ⬝ᵥ v) + b ^ 2 * (v ⬝ᵥ v) := by
  simp only [sub_dotProduct, dotProduct_sub, smul_dotProduct, dotProduct_smul, smul_eq_mul,
    dotProduct_comm v u]
  ring

/-- The all-ones vector $(1, 1, \dots, 1)$ in $\mathbb R^n$ (the diagonal of the unit cube). -/
def ones (n : ℕ) : Fin n → ℝ := fun _ => 1

/-- The unit vector along axis `i`: entry $1$ in position `i`, $0$ elsewhere. -/
def axis {n : ℕ} (i : Fin n) : Fin n → ℝ := Pi.single i 1

/-! ## Echelon -/

/-- `A` and `B` are row equivalent: `B = E * A` where `E` records a sequence of row operations,
and `E` can be undone (`F * E = 1`). -/
def RowEquiv {m n : ℕ} (A B : Matrix (Fin m) (Fin n) ℝ) : Prop :=
  ∃ E F : Matrix (Fin m) (Fin m) ℝ, F * E = 1 ∧ E * A = B

/-- A square matrix is nonsingular when its homogeneous system has only the trivial solution
(Hefferon One.I.2.13). -/
def IsNonsingular {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) : Prop := ∀ v, A *ᵥ v = 0 → v = 0

/-- The elementary matrix for $k\rho_i + \rho_j$ (add $k$ times row $i$ to row $j$). -/
def combo {n : ℕ} (i j : Fin n) (k : ℝ) : Matrix (Fin n) (Fin n) ℝ := 1 + Matrix.single j i k

/-- The elementary matrix for $c\rho_i$ (rescale row $i$ by $c$). -/
def scale {n : ℕ} (i : Fin n) (c : ℝ) : Matrix (Fin n) (Fin n) ℝ :=
  Matrix.diagonal (Function.update 1 i c)

/-- The combination matrices ($i \ne j$) and the rescaling matrices ($c \ne 0$). -/
def NoSwapOps {n : ℕ} : Set (Matrix (Fin n) (Fin n) ℝ) :=
  {E | (∃ i j k, i ≠ j ∧ E = combo i j k) ∨ (∃ i c, c ≠ 0 ∧ E = scale i c)}

theorem rowEquiv_of_det {m n : ℕ} {A B : Matrix (Fin m) (Fin n) ℝ} (E : Matrix (Fin m) (Fin m) ℝ)
    (hE : E.det ≠ 0) (h : E * A = B) : RowEquiv A B :=
  ⟨E, E⁻¹, Matrix.nonsing_inv_mul E (isUnit_iff_ne_zero.mpr hE), h⟩

/-- Every nonzero $(p, q)$ is the first column of some $2\times2$ matrix with nonzero
determinant. -/
theorem exists_firstCol {p q : ℝ} (h : p ≠ 0 ∨ q ≠ 0) :
    ∃ E : Matrix (Fin 2) (Fin 2) ℝ, E.det ≠ 0 ∧ E 0 0 = p ∧ E 1 0 = q := by
  rcases h with hp | hq
  · exact ⟨!![p, 0; q, 1], by simp [det_fin_two, hp], rfl, rfl⟩
  · exact ⟨!![p, 1; q, 0], by simp [det_fin_two, hq], rfl, rfl⟩

/-! ## Puzzles -/

/-- One meeting of two differently coloured arbuzoids; a state is (red, green, blue). -/
inductive Meet : ℤ × ℤ × ℤ → ℤ × ℤ × ℤ → Prop
  | rg (r g b : ℤ) : 0 < r → 0 < g → Meet (r, g, b) (r - 1, g - 1, b + 2)
  | rb (r g b : ℤ) : 0 < r → 0 < b → Meet (r, g, b) (r - 1, g + 2, b - 1)
  | gb (r g b : ℤ) : 0 < g → 0 < b → Meet (r, g, b) (r + 2, g - 1, b - 1)

/-- `t` can be reached from `s` by a finite sequence of meetings. -/
def Reachable (s t : ℤ × ℤ × ℤ) : Prop := Relation.ReflTransGen Meet s t

/-- Subscriber `i`'s reading list as a 0/1 vector in $\mathbb R^n$ (one entry per book). -/
def bookVec {n k : ℕ} (reads : Fin k → Finset (Fin n)) (i : Fin k) : Fin n → ℝ :=
  fun b => if b ∈ reads i then 1 else 0

/-- $n+1$ vectors in $\mathbb R^n$ satisfy a nontrivial linear relation. -/
theorem exists_relation {n : ℕ} (v : Fin (n + 1) → Fin n → ℝ) :
    ∃ c : Fin (n + 1) → ℝ, c ≠ 0 ∧ ∑ i, c i • v i = 0 := by
  have h : ¬ LinearIndependent ℝ v := by
    intro hli
    have := hli.fintype_card_le_finrank
    simp at this
  rw [Fintype.not_linearIndependent_iff] at h
  obtain ⟨c, hc, i, hi⟩ := h
  exact ⟨c, fun h0 => hi (by rw [h0]; rfl), hc⟩

/-- The sign split: if $\sum_i c_i\vec v_i = \vec 0$ for the reading vectors, the subscribers with
$c_i > 0$ read exactly the same books as those with $c_i < 0$. -/
theorem balance {n k : ℕ} (reads : Fin k → Finset (Fin n)) (c : Fin k → ℝ)
    (hrel : ∑ i, c i • bookVec reads i = 0) :
    (Finset.univ.filter (fun i => 0 < c i)).biUnion reads =
      (Finset.univ.filter (fun i => c i < 0)).biUnion reads := by
  ext b
  have h := congrFun hrel b
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, bookVec] at h
  have split : ∀ i, c i * (if b ∈ reads i then (1:ℝ) else 0) =
      (if 0 < c i then c i * (if b ∈ reads i then 1 else 0) else 0) -
      (if c i < 0 then -c i * (if b ∈ reads i then 1 else 0) else 0) := by
    intro i; split_ifs <;> linarith
  rw [Finset.sum_congr rfl (fun i _ => split i), Finset.sum_sub_distrib, ← Finset.sum_filter,
    ← Finset.sum_filter, sub_eq_zero] at h
  have pos : ∀ (p : Fin k → Prop) [DecidablePred p] (f : Fin k → ℝ), (∀ i, p i → 0 < f i) →
      (b ∈ (Finset.univ.filter p).biUnion reads ↔
        0 < ∑ i ∈ Finset.univ.filter p, f i * (if b ∈ reads i then 1 else 0)) := by
    intro p _ f hf
    rw [Finset.sum_pos_iff_of_nonneg]
    · simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨i, hi, hb⟩; exact ⟨i, hi, by simp [hb, hf i hi]⟩
      · rintro ⟨i, hi, hb⟩; refine ⟨i, hi, ?_⟩; by_contra hn; simp [hn] at hb
    · intro i hi
      simp only [Finset.mem_filter] at hi
      have := hf i hi.2
      split_ifs <;> simp; linarith
  rw [pos _ c (fun i h => h), pos _ (fun i => -c i) (fun i h => by linarith), h]

end LinearAlgebraGame
