import GameServer
import Mathlib
import Game.Lib

/-! # Chapter One (Hefferon One.I–III) and the optional Puzzles

Game-local definitions and all `TheoremDoc` / `DefinitionDoc` entries for the worlds
`RowOps`, `DotProduct`, `Echelon` and `Puzzles`. -/

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

/-! ## Definition docs -/

/-- `NoSolution S`: the system `S` has no solution, i.e. `¬ ∃ v, S v`. -/
DefinitionDoc LinearAlgebraGame.NoSolution as "NoSolution"
/-- `UniqueSolution S`: exactly one solution, `∃! v, S v`. Prove it with
`rw [uniqueSolution_iff]`, then `use` the solution, check it, and show every solution equals it. -/
DefinitionDoc LinearAlgebraGame.UniqueSolution as "UniqueSolution"
/-- `InfinitelyMany S`: the solution set of `S` is infinite. Prove it with
`infinitelyMany_of_line`. -/
DefinitionDoc LinearAlgebraGame.InfinitelyMany as "InfinitelyMany"
/-- `Classify S` is `NoSolution S ∨ UniqueSolution S ∨ InfinitelyMany S`: `left` picks
"none", `right; left` "unique", `right; right` "infinitely many". -/
DefinitionDoc LinearAlgebraGame.Classify as "Classify"
/-- `ones n` $= (1, 1, \dots, 1) \in \mathbb R^n$; `ones n i = 1` for every `i`
(`rw [ones]` or `norm_num [ones]` unfolds it). -/
DefinitionDoc LinearAlgebraGame.ones as "ones"
/-- `axis i` $= \vec e_i$: entry $1$ in position `i`, $0$ elsewhere. It is `Pi.single i 1`
(`rw [axis]` unfolds it). -/
DefinitionDoc LinearAlgebraGame.axis as "axis"
/-- Mathlib's echelon form: each row's leading entry is strictly to the right of the leading
entries of the rows above it, and zero rows come last. -/
DefinitionDoc Matrix.IsRowEchelon as "IsRowEchelon"
/-- `IsRat x`: the real number `x` is rational, `∃ q : ℚ, (q : ℝ) = x`. -/
DefinitionDoc LinearAlgebraGame.IsRat as "IsRat"
/-- `len v` $= |\vec v| = \sqrt{\vec v\cdot\vec v}$. `rw [len]` unfolds it. -/
DefinitionDoc LinearAlgebraGame.len as "len"
/-- `RowEquiv A B`: there are `E F` with `F * E = 1` and `E * A = B` — `B` comes from `A` by
row operations (recorded as the reversible matrix `E`). -/
DefinitionDoc LinearAlgebraGame.RowEquiv as "RowEquiv"
/-- `IsNonsingular A`: `∀ v, A *ᵥ v = 0 → v = 0` (only for square `A`). -/
DefinitionDoc LinearAlgebraGame.IsNonsingular as "IsNonsingular"
/-- `combo i j k`: the elementary matrix of $k\rho_i + \rho_j$. -/
DefinitionDoc LinearAlgebraGame.combo as "combo"
/-- `scale i c`: the elementary matrix of $c\rho_i$. -/
DefinitionDoc LinearAlgebraGame.scale as "scale"
/-- `NoSwapOps`: the elementary matrices for combinations and nonzero rescalings (no swaps). -/
DefinitionDoc LinearAlgebraGame.NoSwapOps as "NoSwapOps"
/-- Mathlib's reduced echelon form: echelon, leading entries `1`, zeros above each leading
entry. A *leading entry* `IsLeadingEntry A i c` is the first nonzero entry of row `i`. -/
DefinitionDoc Matrix.IsReducedRowEchelon as "IsReducedRowEchelon"
/-- `Meet s t`: one meeting of two differently coloured arbuzoids turns state `s` into `t`. -/
DefinitionDoc LinearAlgebraGame.Meet as "Meet"
/-- `Reachable s t`: zero or more meetings lead from `s` to `t`. -/
DefinitionDoc LinearAlgebraGame.Reachable as "Reachable"
/-- `bookVec reads i`: subscriber `i`'s 0/1 reading vector. -/
DefinitionDoc LinearAlgebraGame.bookVec as "bookVec"

/-! ## Theorem docs: Row Ops -/

/-- If `h : f = g` for functions (vectors), then `congrFun h i : f i = g i`. -/
TheoremDoc congrFun as "congrFun" in "Vectors"
/-- $\sum_{i<3} f(i) = f(0) + f(1) + f(2)$. -/
TheoremDoc Fin.sum_univ_three as "Fin.sum_univ_three" in "Vectors"
/-- `infinitelyMany_of_line p d i (hd : d i ≠ 0) (h : ∀ t, S (p + t • d))`: a whole line of
solutions (with direction $\vec d$ nonzero in position `i`) means infinitely many solutions.
Use it as `apply infinitelyMany_of_line p d i` with your `p`, `d` and a position `i`. -/
TheoremDoc LinearAlgebraGame.infinitelyMany_of_line as "infinitelyMany_of_line" in "Systems"
/-- `uniqueSolution_iff : UniqueSolution S ↔ ∃ p, S p ∧ ∀ v, S v → v = p`. After
`rw [uniqueSolution_iff]`, `use` your solution, check it, then show every solution equals it. -/
TheoremDoc LinearAlgebraGame.uniqueSolution_iff as "uniqueSolution_iff" in "Systems"
/-- If `F * E = 1` for $2\times2$ matrices, the first column of `E` is not zero:
`E 0 0 ≠ 0 ∨ E 1 0 ≠ 0`. -/
TheoremDoc LinearAlgebraGame.firstCol_ne_zero as "firstCol_ne_zero" in "Matrices"
/-- `exists_firstCol (h : p ≠ 0 ∨ q ≠ 0) : ∃ E, E.det ≠ 0 ∧ E 0 0 = p ∧ E 1 0 = q` — any
nonzero column is the first column of an invertible matrix. -/
TheoremDoc LinearAlgebraGame.exists_firstCol as "exists_firstCol" in "Matrices"
/-- `eq_div_iff (hc : c ≠ 0) : a = b / c ↔ a * c = b`. -/
TheoremDoc eq_div_iff as "eq_div_iff" in "Systems"
/-- `mul_left_cancel₀ (ha : a ≠ 0) : a * b = a * c → b = c`. -/
TheoremDoc mul_left_cancel₀ as "mul_left_cancel₀" in "Systems"
/-- `mul_right_cancel₀ (hb : b ≠ 0) : a * b = c * b → a = c`. -/
TheoremDoc mul_right_cancel₀ as "mul_right_cancel₀" in "Systems"
/-- $A(\vec x - \vec y) = A\vec x - A\vec y$. -/
TheoremDoc Matrix.mulVec_sub as "mulVec_sub" in "Vectors"
/-- $A(c\,\vec v) = c\,(A\vec v)$. -/
TheoremDoc Matrix.mulVec_smul as "mulVec_smul" in "Vectors"
/-- $A(\vec x + \vec y) = A\vec x + A\vec y$. -/
TheoremDoc Matrix.mulVec_add as "mulVec_add" in "Vectors"

/-! ## Theorem docs: Dot Product -/

/-- $c \cdot \sum_i f(i) = \sum_i c\, f(i)$. -/
TheoremDoc Finset.mul_sum as "Finset.mul_sum" in "Sums"
/-- $\sum_i (f(i) + g(i)) = \sum_i f(i) + \sum_i g(i)$. -/
TheoremDoc Finset.sum_add_distrib as "Finset.sum_add_distrib" in "Sums"
/-- $(\vec u + \vec v)_i = u_i + v_i$. -/
TheoremDoc Pi.add_apply as "Pi.add_apply" in "Vectors"
/-- $(c\,\vec v)_i = c \cdot v_i$ (as `c • v i`). -/
TheoremDoc Pi.smul_apply as "Pi.smul_apply" in "Vectors"
/-- For numbers, `a • b = a * b`. -/
TheoremDoc smul_eq_mul as "smul_eq_mul" in "Vectors"
/-- $\vec u\cdot(\vec v + \vec w) = \vec u\cdot\vec v + \vec u\cdot\vec w$. You proved this
(Sheet 2 Q7). -/
TheoremDoc dotProduct_add as "dotProduct_add" in "Dot"
/-- $(\vec u + \vec v)\cdot\vec w = \vec u\cdot\vec w + \vec v\cdot\vec w$. -/
TheoremDoc add_dotProduct as "add_dotProduct" in "Dot"
/-- $\vec u\cdot(\vec v - \vec w) = \vec u\cdot\vec v - \vec u\cdot\vec w$. -/
TheoremDoc dotProduct_sub as "dotProduct_sub" in "Dot"
/-- $(\vec u - \vec v)\cdot\vec w = \vec u\cdot\vec w - \vec v\cdot\vec w$. -/
TheoremDoc sub_dotProduct as "sub_dotProduct" in "Dot"
/-- $\vec u\cdot(c\,\vec v) = c\,(\vec u\cdot\vec v)$. You proved this (Sheet 2 Q7). -/
TheoremDoc dotProduct_smul as "dotProduct_smul" in "Dot"
/-- $(c\,\vec u)\cdot\vec v = c\,(\vec u\cdot\vec v)$. -/
TheoremDoc smul_dotProduct as "smul_dotProduct" in "Dot"
/-- $\vec u\cdot\vec v = \vec v\cdot\vec u$. -/
TheoremDoc dotProduct_comm as "dotProduct_comm" in "Dot"
/-- $\vec v\cdot\vec 0 = 0$. -/
TheoremDoc dotProduct_zero as "dotProduct_zero" in "Dot"
/-- $\vec 0\cdot\vec v = 0$. -/
TheoremDoc zero_dotProduct as "zero_dotProduct" in "Dot"
/-- $\vec v\cdot\vec v = 0 \iff \vec v = \vec 0$. -/
TheoremDoc dotProduct_self_eq_zero as "dotProduct_self_eq_zero" in "Dot"
/-- $\vec v \cdot e_i = v_i$ when $e_i$ is `Pi.single i 1` (in general `v i * x`). -/
TheoremDoc dotProduct_single as "dotProduct_single" in "Dot"
/-- `Pi.single i x i = x`. -/
TheoremDoc Pi.single_eq_same as "Pi.single_eq_same" in "Dot"
/-- $0 \le \vec v\cdot\vec v$. -/
TheoremDoc LinearAlgebraGame.dot_self_nonneg as "dot_self_nonneg" in "Dot"
/-- $0 \le |\vec v|$. -/
TheoremDoc LinearAlgebraGame.len_nonneg as "len_nonneg" in "Dot"
/-- $|\vec v|^2 = \vec v\cdot\vec v$. -/
TheoremDoc LinearAlgebraGame.len_sq as "len_sq" in "Dot"
/-- $(a\vec u - b\vec v)\cdot(a\vec u - b\vec v) = a^2(\vec u\cdot\vec u) - 2ab(\vec u\cdot\vec v)
+ b^2(\vec v\cdot\vec v)$ — bilinearity bookkeeping, granted. -/
TheoremDoc LinearAlgebraGame.dot_expand as "dot_expand" in "Dot"
/-- $\sqrt{x y} = \sqrt x\sqrt y$ for $x \ge 0$: `Real.sqrt_mul (hx : 0 ≤ x) y`. -/
TheoremDoc Real.sqrt_mul as "Real.sqrt_mul" in "Dot"
/-- If $x^2 \le y$ then $|x| \le \sqrt y$. -/
TheoremDoc Real.abs_le_sqrt as "Real.abs_le_sqrt" in "Dot"
/-- $\sqrt 0 = 0$. -/
TheoremDoc Real.sqrt_zero as "Real.sqrt_zero" in "Dot"
/-- $\sqrt 1 = 1$. -/
TheoremDoc Real.sqrt_one as "Real.sqrt_one" in "Dot"
/-- $a \le |a|$. -/
TheoremDoc le_abs_self as "le_abs_self" in "Dot"
/-- $a \cdot 1 = a$. -/
TheoremDoc mul_one as "mul_one" in "Dot"
/-- `a ≤ b ∨ …`: from `h : a ≤ b`, `h.eq_or_lt : a = b ∨ a < b`. -/
TheoremDoc LE.le.eq_or_lt as "LE.le.eq_or_lt" in "Dot"
/-- $\sum_{i<0} f(i) = 0$. -/
TheoremDoc Finset.sum_range_zero as "Finset.sum_range_zero" in "Sums"
/-- $\sum_{i<n+1} f(i) = \sum_{i<n} f(i) + f(n)$. -/
TheoremDoc Finset.sum_range_succ as "Finset.sum_range_succ" in "Sums"
/-- Disabled: Mathlib's Cauchy–Schwarz for sums. -/
TheoremDoc Finset.sum_mul_sq_le_sq_mul_sq as "Finset.sum_mul_sq_le_sq_mul_sq" in "Dot"
/-- Disabled: Mathlib's Cauchy–Schwarz for sums. -/
TheoremDoc Finset.inner_mul_le_norm_mul_norm as "Finset.inner_mul_le_norm_mul_norm" in "Dot"

/-! ## Theorem docs: Echelon -/

/-- $(M N)\vec v = M(N\vec v)$, as `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`. -/
TheoremDoc Matrix.mulVec_mulVec as "mulVec_mulVec" in "Matrices"
/-- $A\vec 0 = \vec 0$. -/
TheoremDoc Matrix.mulVec_zero as "mulVec_zero" in "Matrices"
/-- $(MN)_{ij} = \sum_k M_{ik}N_{kj}$. -/
TheoremDoc Matrix.mul_apply as "mul_apply" in "Matrices"
/-- $A \cdot 0 = 0$ for matrices. -/
TheoremDoc Matrix.mul_zero as "Matrix.mul_zero" in "Matrices"
/-- $A \cdot 1 = A$ for matrices. -/
TheoremDoc Matrix.mul_one as "Matrix.mul_one" in "Matrices"
/-- $\det(MN) = \det M \det N$. -/
TheoremDoc Matrix.det_mul as "det_mul" in "Matrices"
/-- $\det 1 = 1$. -/
TheoremDoc Matrix.det_one as "det_one" in "Matrices"
/-- $\det A = A_{00}A_{11} - A_{01}A_{10}$ for $2\times 2$ matrices. -/
TheoremDoc Matrix.det_fin_two as "det_fin_two" in "Matrices"
/-- If $\det E \ne 0$ and $E A = B$ then `RowEquiv A B` ($E$ is undone by $E^{-1}$). -/
TheoremDoc LinearAlgebraGame.rowEquiv_of_det as "rowEquiv_of_det" in "Matrices"
/-- $\forall x \in \text{Fin}(n+1),\ P(x)$ iff $P(0)$ and $P$ holds at every successor. -/
TheoremDoc Fin.forall_fin_succ as "Fin.forall_fin_succ" in "Matrices"
/-- `IsLeadingEntry A i c`: column `c` holds the first nonzero entry of row `i`. -/
TheoremDoc Matrix.IsLeadingEntry as "IsLeadingEntry" in "Matrices"
/-- In a reduced echelon matrix, entries above a leading entry are `0`. -/
TheoremDoc Matrix.IsReducedRowEchelon.eq_zero as "IsReducedRowEchelon.eq_zero" in "Matrices"
/-- `¬ (a ∧ b) ↔ ¬ a ∨ ¬ b`. -/
TheoremDoc not_and_or as "not_and_or" in "Logic"
/-- Products of members of a submonoid are members. -/
TheoremDoc Submonoid.mul_mem as "Submonoid.mul_mem" in "Matrices"
/-- Every generator lies in the generated submonoid. -/
TheoremDoc Submonoid.subset_closure as "Submonoid.subset_closure" in "Matrices"

/-! ## Theorem docs: Puzzles -/

/-- $n+1$ vectors in $\mathbb R^n$ satisfy a nontrivial relation $\sum c_i \vec v_i = \vec 0$,
$\vec c \ne \vec 0$ (granted: more unknowns than equations, Sheet 1 Q2's true cousin). -/
TheoremDoc LinearAlgebraGame.exists_relation as "exists_relation" in "Puzzles"
/-- The sign split (granted): positive-coefficient subscribers read the same books as
negative-coefficient ones. -/
TheoremDoc LinearAlgebraGame.balance as "balance" in "Puzzles"
/-- `(s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty`. -/
TheoremDoc Finset.biUnion_nonempty as "Finset.biUnion_nonempty" in "Puzzles"
/-- `f ≠ g ↔ ∃ a, f a ≠ g a`. -/
TheoremDoc Function.ne_iff as "Function.ne_iff" in "Puzzles"
/-- `Disjoint (s.filter p) (s.filter q)` if no element satisfies both. -/
TheoremDoc Finset.disjoint_filter as "Finset.disjoint_filter" in "Puzzles"
/-- From `h : a ≠ b`, `h.lt_or_gt : a < b ∨ b < a`. -/
TheoremDoc Ne.lt_or_gt as "Ne.lt_or_gt" in "Puzzles"
/-- $(A + B)C = AC + BC$ for matrices. -/
TheoremDoc Matrix.add_mul as "Matrix.add_mul" in "Matrices"
/-- The entry $(a, b)$ of `single i j c` is `c` if `i = a ∧ j = b`, else `0`. -/
TheoremDoc Matrix.single_apply as "Matrix.single_apply" in "Matrices"
/-- `a ∈ s.filter p ↔ a ∈ s ∧ p a`. -/
TheoremDoc Finset.mem_filter as "Finset.mem_filter" in "Puzzles"
/-- Everything is in `Finset.univ`. -/
TheoremDoc Finset.mem_univ as "Finset.mem_univ" in "Puzzles"
/-- Cauchy–Schwarz: $|\vec u\cdot\vec v| \le |\vec u|\,|\vec v|$ (you proved it). -/
TheoremDoc LinearAlgebraGame.cauchy_schwarz as "cauchy_schwarz" in "Dot"
/-- Triangle inequality: $|\vec u + \vec v| \le |\vec u| + |\vec v|$ (you proved it). -/
TheoremDoc LinearAlgebraGame.len_add_le as "len_add_le" in "Dot"
