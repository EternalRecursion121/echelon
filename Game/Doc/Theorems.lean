import GameServer

/-! # Inventory documentation (all worlds)

Every `TheoremDoc` / `DefinitionDoc` of the game lives here, once. This module is imported by
`Game.Metadata`, so a doc is available in every level, whichever world first unlocks the item.
(`TheoremDoc` does not need the documented constant to exist, so game-local names from the
chapter files `Game/Ch*.lean` are documented here too; their `def`s stay in the chapter files.)
Do not add a second doc for a name: the engine keeps the first one. -/


/-! ## First documented in LeanBasics -/

/-- `Fin n` is the set of positions $\{0, 1, \dots, n-1\}$; a vector in $\mathbb R^n$ is a
function `Fin n → ℝ`, and `Matrix (Fin m) (Fin n) ℝ` is an $m \times n$ real matrix. -/
DefinitionDoc Fin as "Fin"

/-- `u ⬝ᵥ v`: the dot product. -/
DefinitionDoc dotProduct as "⬝ᵥ"
/-- $\sum_{i<2} f(i) = f(0) + f(1)$. -/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "Vectors"
/-- `A *ᵥ v`: the matrix–vector product. -/
DefinitionDoc Matrix.mulVec as "*ᵥ"

/-! ## First documented in Ch1 -/

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
/-- `ones n` $= (1, 1, \dots, 1) \in \mathbb R^n$; `ones n i = 1` for every `i`.

`rw [ones]` only works on an entry `ones n i`; on a bare `ones n` (e.g. inside
`ones n ⬝ᵥ v`) it fails with "Failed to rewrite using equation theorems". There use
`norm_num [ones, dotProduct]` (or `simp [ones]`), which unfolds it everywhere. -/
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
/-- $(M N)\vec v = M(N\vec v)$, as `M *ᵥ (N *ᵥ v) = (M * N) *ᵥ v`. -/
TheoremDoc Matrix.mulVec_mulVec as "mulVec_mulVec" in "Matrices"
/-- $A\vec 0 = \vec 0$. -/
TheoremDoc Matrix.mulVec_zero as "mulVec_zero" in "Matrices"
/-- `Matrix.mul_apply : (M * N) i j = ∑ k, M i k * N k j`, i.e. $(MN)_{ij} = \sum_k M_{ik}N_{kj}$.

Write the full name `Matrix.mul_apply` (also in `simp [Matrix.mul_apply, …]`): a bare
`mul_apply` can mean an unrelated root lemma that is not in your inventory. -/
TheoremDoc Matrix.mul_apply as "Matrix.mul_apply" in "Matrices"
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
/-- `Finset.mem_univ i : i ∈ Finset.univ` — every position is in `Finset.univ`, the finite set
of all positions (the index set of a sum `∑ i, …` over all positions). -/
TheoremDoc Finset.mem_univ as "Finset.mem_univ" in "Sums"
/-- Cauchy–Schwarz: $|\vec u\cdot\vec v| \le |\vec u|\,|\vec v|$ (you proved it). -/
TheoremDoc LinearAlgebraGame.cauchy_schwarz as "cauchy_schwarz" in "Dot"
/-- Triangle inequality: $|\vec u + \vec v| \le |\vec u| + |\vec v|$ (you proved it). -/
TheoremDoc LinearAlgebraGame.len_add_le as "len_add_le" in "Dot"
/-- $ab = ba$: multiplication of numbers commutes. `mul_comm a b : a * b = b * a`; plain `rw [mul_comm]` swaps the first product it finds. -/
TheoremDoc mul_comm as "mul_comm" in "Sums"
/-- `Int.add_mul_emod_self_left a b c : (a + b * c) % b = a % b` — adding a multiple of `b` does not change the remainder mod `b`. -/
TheoremDoc Int.add_mul_emod_self_left as "Int.add_mul_emod_self_left" in "Puzzles"
/-- `refl`: the zero-step case. In `induction hs with | refl => … | tail _ hstep ih => …` on a `Reachable` (a reflexive–transitive closure), `refl` is the case where no meeting has happened yet. -/
TheoremDoc refl as "refl" in "Puzzles"

/-! ## First documented in Ch2a -/

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
/-- `PosQuad.add_a₀ p q : (p.add q).a₀ = p.a₀ + q.a₀` — sums are added coefficientwise. -/
TheoremDoc LinearAlgebraGame.PosQuad.add_a₀ as "PosQuad.add_a₀" in "Vector spaces"
/-- `irrational_sqrt_two : Irrational √2`. -/
TheoremDoc irrational_sqrt_two as "irrational_sqrt_two" in "Vector spaces"
/-- `Irrational.ne_rat h q : x ≠ q` for `h : Irrational x` and a rational `q`. -/
TheoremDoc Irrational.ne_rat as "Irrational.ne_rat" in "Vector spaces"
/-- `Rat.cast_one : ((1 : ℚ) : ℝ) = 1`. -/
TheoremDoc Rat.cast_one as "Rat.cast_one" in "Vector spaces"
/-- `Pi.zero_apply : (0 : X → ℝ) x = 0` — every entry of the zero vector (or value of the zero
function) is `0`. Lean displays an entry of the zero vector as `0 i`. -/
TheoremDoc Pi.zero_apply as "Pi.zero_apply" in "Vectors"
/-- `Pi.neg_apply f x : (-f) x = -f x`. -/
TheoremDoc Pi.neg_apply as "Pi.neg_apply" in "Vector spaces"
/-- `mul_add a b c : a * (b + c) = a * b + a * c`. -/
TheoremDoc mul_add as "mul_add" in "Vector spaces"
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
`S` (Lemma Two.I.2.15, proved in Subspaces level 5). -/
TheoremDoc Submodule.span_le as "Submodule.span_le" in "Subspaces"
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
(Subspaces level 8). -/
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
/-- `Finset.smul_sum : r • ∑ i ∈ s, f i = ∑ i ∈ s, r • f i` — a scalar times a sum is the sum
of the scaled terms. -/
TheoremDoc Finset.smul_sum as "Finset.smul_sum" in "Independence"
/-- `Finset.sum_apply x s f : (∑ i ∈ s, f i) x = ∑ i ∈ s, f i x` — sums of functions are
evaluated pointwise. -/
TheoremDoc Finset.sum_apply as "Finset.sum_apply" in "Independence"
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
/-- `congrArg f h : f a = f b` from `h : a = b` — apply the same function to both sides of an
equation (e.g. take the determinant of both sides: `congrArg det h : det A = det B` from
`h : A = B`). -/
TheoremDoc congrArg as "congrArg" in "Vectors"

/-! ## First documented in Ch2b -/

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
/-- `(∅ : Finset α).card = 0`. -/
TheoremDoc Finset.card_empty as "Finset.card_empty" in "Dimension"
/-- `a ≠ b → ({a, b} : Finset α).card = 2`. -/
TheoremDoc Finset.card_pair as "Finset.card_pair" in "Dimension"
/-- `({a} : Finset α).card = 1`. -/
TheoremDoc Finset.card_singleton as "Finset.card_singleton" in "Dimension"
/-- $\sum (f_i - g_i) = \sum f_i - \sum g_i$. -/
TheoremDoc Finset.sum_sub_distrib as "Finset.sum_sub_distrib" in "Basis"
/-- A finset `S`, viewed as a type, has `S.card` elements. -/
TheoremDoc Fintype.card_coe as "Fintype.card_coe" in "Dimension"
/-- `Fintype.card (Fin n) = n`. -/
TheoremDoc Fintype.card_fin as "Fintype.card_fin" in "Dimension"
/-- `Fintype.card (α ⊕ β) = Fintype.card α + Fintype.card β`. -/
TheoremDoc Fintype.card_sum as "Fintype.card_sum" in "Dimension"
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
/-- `X ∣ p ↔ p.coeff 0 = 0`. -/
TheoremDoc Polynomial.X_dvd_iff as "Polynomial.X_dvd_iff" in "Dimension"
/-- `X ≠ 0`. -/
TheoremDoc Polynomial.X_ne_zero as "Polynomial.X_ne_zero" in "Dimension"
/-- `(∀ x ∈ Set.range f, P x) ↔ ∀ i, P (f i)`. -/
TheoremDoc Set.forall_mem_range as "Set.forall_mem_range" in "Rank"
/-- `a ∈ insert b s ↔ a = b ∨ a ∈ s`. -/
TheoremDoc Set.mem_insert_iff as "Set.mem_insert_iff" in "Sums"
/-- `a ∈ {x | p x}` is `p a`. -/
TheoremDoc Set.mem_setOf_eq as "Set.mem_setOf_eq" in "Basis"
/-- `a ∈ {b} ↔ a = b`. -/
TheoremDoc Set.mem_singleton_iff as "Set.mem_singleton_iff" in "Sums"
/-- The range of a function on an empty type is `∅`. -/
TheoremDoc Set.range_eq_empty as "Set.range_eq_empty" in "Dimension"
/-- `x ∈ (U : Set V) ↔ x ∈ U`. -/
TheoremDoc SetLike.mem_coe as "SetLike.mem_coe" in "Basis"
/-- `x ∈ U → y ∈ W → x + y ∈ U ⊔ W`. -/
TheoremDoc Submodule.add_mem_sup as "Submodule.add_mem_sup" in "Sums"
/-- Nested subspaces of equal finite dimension are equal: for `hle : U ≤ W` and `hd : finrank ℝ U = finrank ℝ W`, `Submodule.eq_of_le_of_finrank_eq hle hd : U = W`. A textbook result (Hefferon Two.III.2); Sheet 4 Q10(b) asks you to prove it, and it is disabled there. -/
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
/-- `U ≤ W → finrank ℝ U ≤ finrank ℝ W` (finite-dimensional ambient space): a subspace is no bigger than the space containing it. Hefferon's result; Sheet 4 Q10(a) asks you to prove it (your `finrank_le_of_le`). Use: `Submodule.finrank_mono hle`. -/
TheoremDoc Submodule.finrank_mono as "Submodule.finrank_mono" in "Dimension"
/-- The dimension formula: $\dim(U+W) + \dim(U\cap W) = \dim U + \dim W$ (proved by you in Sheet 6 Q1). -/
TheoremDoc Submodule.finrank_sup_add_finrank_inf_eq as "finrank_sup_add_finrank_inf_eq" in "Sums"
/-- Extension lemma (Two.II.1.15), dimension form: `w ∉ U → finrank (U ⊔ span ℝ {w}) = finrank U + 1`. -/
TheoremDoc Submodule.finrank_sup_span_singleton as "finrank_sup_span_singleton" in "Dimension"
/-- For `h : U ≤ W`, the inclusion map `Submodule.inclusion h : U → W` is injective. -/
TheoremDoc Submodule.inclusion_injective as "Submodule.inclusion_injective" in "Dimension"
/-- `x ∈ ⊥ ↔ x = 0`. -/
TheoremDoc Submodule.mem_bot as "Submodule.mem_bot" in "Dimension"
/-- `x ∈ U → x ∈ U ⊔ W`. -/
TheoremDoc Submodule.mem_sup_left as "Submodule.mem_sup_left" in "Sums"
/-- `x ∈ W → x ∈ U ⊔ W`. -/
TheoremDoc Submodule.mem_sup_right as "Submodule.mem_sup_right" in "Sums"
/-- Every vector is in `⊤`. -/
TheoremDoc Submodule.mem_top as "Submodule.mem_top" in "Basis"
/-- `x ∈ U → -x ∈ U`. -/
TheoremDoc Submodule.neg_mem as "Submodule.neg_mem" in "Basis"
/-- `span ℝ ∅ = ⊥`. -/
TheoremDoc Submodule.span_empty as "Submodule.span_empty" in "Dimension"
/-- `span ℝ s = ⊥ ↔ ∀ x ∈ s, x = 0`. -/
TheoremDoc Submodule.span_eq_bot as "Submodule.span_eq_bot" in "Dimension"
/-- `span ℝ {x} ≤ U ↔ x ∈ U`. -/
TheoremDoc Submodule.span_singleton_le_iff_mem as "span_singleton_le_iff_mem" in "Dimension"
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
/-- `U ≤ U ⊔ W`. -/
TheoremDoc le_sup_left as "le_sup_left" in "Sums"
/-- The empty sequence is linearly independent. -/
TheoremDoc linearIndependent_empty_type as "linearIndependent_empty_type" in "Dimension"
/-- `a * b = 0 ↔ a = 0 ∨ b = 0`. -/
TheoremDoc mul_eq_zero as "mul_eq_zero" in "Dimension"
/-- `-a = 0 ↔ a = 0`. -/
TheoremDoc neg_eq_zero as "neg_eq_zero" in "Sums"
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

/-! ## First documented in Ch3a -/

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
/-- `mul_inv_cancel₀ h : a * a⁻¹ = 1` for `h : a ≠ 0`. -/
TheoremDoc mul_inv_cancel₀ as "mul_inv_cancel₀" in "Isomorphisms"
/-- `map_add h u v : h (u + v) = h u + h v` — a linear map preserves addition. -/
TheoremDoc map_add as "map_add" in "Maps"
/-- `map_smul h r v : h (r • v) = r • h v` — a linear map preserves scalar multiplication. -/
TheoremDoc map_smul as "map_smul" in "Maps"
/-- `Finset.sum_const_zero : ∑ i, 0 = 0`. -/
TheoremDoc Finset.sum_const_zero as "Finset.sum_const_zero" in "Sums"
/-- `map_sum h f s : h (∑ i ∈ s, f i) = ∑ i ∈ s, h (f i)` — a linear map preserves sums. -/
TheoremDoc map_sum as "map_sum" in "Maps"
/-- `(f + g) i = f i + g i` for coordinate functions (finitely supported functions). -/
TheoremDoc Finsupp.add_apply as "Finsupp.add_apply" in "Sums"
/-- `(r • f) i = r • f i` for coordinate functions (finitely supported functions). -/
TheoremDoc Finsupp.smul_apply as "Finsupp.smul_apply" in "Sums"
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
/-- `eq_neg_of_add_eq_zero_left : a + b = 0 → a = -b`. -/
TheoremDoc eq_neg_of_add_eq_zero_left as "eq_neg_of_add_eq_zero_left" in "Subspaces"
/-- `injective_iff_map_eq_zero f : Function.Injective f ↔ ∀ a, f a = 0 → a = 0` — a linear map
is one-to-one iff only $\vec 0$ maps to $\vec 0$ (granted here; you prove it in Homomorphisms). -/
TheoremDoc injective_iff_map_eq_zero as "injective_iff_map_eq_zero" in "Maps"
/-- A variant of `injective_iff_map_eq_zero`. -/
TheoremDoc injective_iff_map_eq_zero' as "injective_iff_map_eq_zero'" in "Maps"
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
/-- `sub_eq_zero : a - b = 0 ↔ a = b`. -/
TheoremDoc sub_eq_zero as "sub_eq_zero" in "Maps"
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
/-- `hv.map' h hker : LinearIndependent ℝ (h ∘ v)` for `hv : LinearIndependent ℝ v` and
`hker : LinearMap.ker h = ⊥` — a one-to-one map keeps independent sets independent. -/
TheoremDoc LinearIndependent.map' as "LinearIndependent.map'" in "Bases"
/-- `LinearMap.mem_range : w ∈ LinearMap.range h ↔ ∃ v, h v = w`. -/
TheoremDoc LinearMap.mem_range as "mem_range" in "Maps"
/-- `LinearMap.mem_range_self h v : h v ∈ LinearMap.range h`. -/
TheoremDoc LinearMap.mem_range_self as "mem_range_self" in "Maps"
/-- `LinearMap.ker_eq_bot : LinearMap.ker h = ⊥ ↔ Function.Injective h` — one-to-one iff the
null space is $\{\vec 0\}$ (the Mathlib form of what you proved). -/
TheoremDoc LinearMap.ker_eq_bot as "ker_eq_bot" in "Maps"
/-- `LinearMap.ker_eq_bot' : LinearMap.ker h = ⊥ ↔ ∀ v, h v = 0 → v = 0`. -/
TheoremDoc LinearMap.ker_eq_bot' as "ker_eq_bot'" in "Maps"
/-- **Rank–nullity** (Hefferon Theorem Three.II.2.14), granted:
`LinearMap.finrank_range_add_finrank_ker h : finrank ℝ (range h) + finrank ℝ (ker h) = finrank ℝ V`
for finite-dimensional `V`. -/
TheoremDoc LinearMap.finrank_range_add_finrank_ker as "rank–nullity" in "Dimension"
/-- `finrank_top ℝ V : finrank ℝ (⊤ : Submodule ℝ V) = finrank ℝ V`. -/
TheoremDoc finrank_top as "finrank_top" in "Dimension"
/-- `Submodule.eq_top_of_finrank_eq : finrank ℝ U = finrank ℝ V → U = ⊤` — a subspace of full
dimension is the whole (finite-dimensional) space. This is Sheet 4 Q10(b). -/
TheoremDoc Submodule.eq_top_of_finrank_eq as "eq_top_of_finrank_eq" in "Dimension"
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
/-- `(u, w) = 0 ↔ (u : V) = 0 ∧ (w : V) = 0` for `u : U`, `w : W` (subspaces of `V`). -/
TheoremDoc LinearAlgebraGame.pair_eq_zero_iff as "pair_eq_zero_iff" in "Subspaces"
/-- `Module.Basis ι ℝ V`: a basis of the whole space `V` indexed by `ι` — the game's `IsBasisOf B ⊤` — bundled with its coordinate map `B.repr`. `B i` is the `i`-th basis vector. -/
DefinitionDoc Module.Basis as "Module.Basis"
/-- `B.repr v`: the coordinates of `v` in the basis `B`; `B.repr v i` is the `i`-th coordinate, and `∑ i, B.repr v i • B i = v` (`Module.Basis.sum_repr`). -/
DefinitionDoc Module.Basis.repr as "Basis.repr"
/-- `le_top : U ≤ ⊤`: every subspace is inside the whole space. -/
TheoremDoc le_top as "le_top" in "Dimension"
/-- Theorem 2.20 (5) ⇒ (1): if `h` sends a basis `B` to an independent sequence `fun i => h (B i)`, then `h` is one-to-one. (You proved this.) -/
TheoremDoc LinearAlgebraGame.inj_of_indep_images as "inj_of_indep_images" in "Dimension"

/-! ## First documented in Ch3b -/

/-- The determinant of a $3\times3$ matrix, written out (rule of Sarrus). -/
TheoremDoc Matrix.det_fin_three as "det_fin_three" in "Matrices"
/-- `(LinearMap.toMatrix B D h) i j = D.repr (h (B j)) i`. -/
TheoremDoc LinearMap.toMatrix_apply as "toMatrix_apply" in "Matrices"
/-- If two sums have termwise equal summands they are equal:
`(∀ x ∈ s, f x = g x) → s.sum f = s.sum g` (use it as `apply Finset.sum_congr rfl`). -/
TheoremDoc Finset.sum_congr as "Finset.sum_congr" in "Sums"
/-- $(\sum_i r_i)\cdot v = \sum_i r_i \cdot v$. -/
TheoremDoc Finset.sum_smul as "Finset.sum_smul" in "Sums"
/-- $\sum_i\sum_j f(i,j) = \sum_j\sum_i f(i,j)$. -/
TheoremDoc Finset.sum_comm as "Finset.sum_comm" in "Sums"
/-- Two linear maps are equal if they agree on every vector. -/
TheoremDoc LinearMap.ext as "LinearMap.ext" in "Maps"
/-- $\dim \mathcal M_{m\times n} = \#\text{rows}\cdot\#\text{columns}$. -/
TheoremDoc Module.finrank_matrix as "finrank_matrix" in "Dimension"
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
/-- `IsRep B D h H`: the matrix `H` represents `h` with respect to `B` and `D` (Hefferon Def Three.III.1.2). It unfolds to `∀ j, h (B j) = ∑ i, H i j • D i`: column $j$ of $H$ holds the coordinates of $h(\vec\beta_j)$ with respect to $D$. Prove it with `intro j`. A *hypothesis* `hH : IsRep B D h H` is folded: use it at a column, `hH j : h (B j) = ∑ i, H i j • D i`, or `unfold IsRep at hH` first — `rw [hH]` and `simp only [hH]` cannot see inside it (simp only just reports the argument as unused). -/
DefinitionDoc LinearAlgebraGame.IsRep as "IsRep (Rep_{B,D})"
/-- `stdBasis n` is the standard basis $\mathcal E_n = \langle\vec e_1,\dots,\vec e_n\rangle$ of $\mathbb R^n$: `stdBasis n i = Pi.single i 1`. Unfold with `simp [stdBasis, Pi.single_apply]`. Not to be confused with Mathlib's `Matrix.stdBasis` (a basis of the space of *matrices*): in a file with `open Matrix`, Lean may report `Ambiguous term stdBasis` — then write `LinearAlgebraGame.stdBasis`. -/
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
/-- `IsUnit x` says `x` has a two-sided inverse. For a real number, `IsUnit x` means $x \ne 0$; so `IsUnit H.det` says the determinant of $H$ is nonzero, i.e. $H$ is invertible (and then `H⁻¹` really is its inverse: `Matrix.nonsing_inv_mul`, `Matrix.mul_nonsing_inv`). -/
DefinitionDoc IsUnit as "IsUnit"
/-- `LinearMap.toMatrix B D h` is Mathlib's $\mathrm{Rep}_{B,D}(h)$ for bases `B`, `D`; it is a linear isomorphism `(V →ₗ[ℝ] W) ≃ₗ[ℝ] Matrix …`. -/
DefinitionDoc LinearMap.toMatrix as "LinearMap.toMatrix"
/-- `LinearMap.toMatrix'` is $\mathrm{Rep}_{\mathcal E_n,\mathcal E_m}$: the isomorphism between linear maps $\mathbb R^n\to\mathbb R^m$ and $m\times n$ matrices. -/
DefinitionDoc LinearMap.toMatrix' as "LinearMap.toMatrix'"
/-- `Matrix.diagonal d` is the diagonal matrix with diagonal entries `d i`. -/
DefinitionDoc Matrix.diagonal as "Matrix.diagonal"
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
/-- `projLine_mem v hs : projLine s v ∈ W` for `hs : s ∈ W` — a projection onto a vector of a subspace stays in the subspace. -/
TheoremDoc LinearAlgebraGame.projLine_mem as "projLine_mem" in "Projection"
/-- `linearIndependent_of_orthogonal v h0 horth : LinearIndependent ℝ v` for nonzero (`h0`), mutually orthogonal (`horth`) vectors (Thm Three.VI.2.2). -/
TheoremDoc LinearAlgebraGame.linearIndependent_of_orthogonal as "linearIndependent_of_orthogonal" in "Projection"
/-- `Pi.single i x j = if j = i then x else 0`. -/
TheoremDoc Pi.single_apply as "Pi.single_apply" in "Vectors"
/-- `f ∘ₗ id = f`. -/
TheoremDoc LinearMap.comp_id as "LinearMap.comp_id" in "Maps"
/-- `id ∘ₗ f = f`. -/
TheoremDoc LinearMap.id_comp as "LinearMap.id_comp" in "Maps"
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
/-- Mathlib: $\vec x\mapsto A\vec x$ is one-to-one iff $A$ is invertible — the boss itself; disabled there. -/
TheoremDoc Matrix.mulVec_injective_iff_isUnit as "mulVec_injective_iff_isUnit" in "Matrices"
/-- Mathlib: $\vec x\mapsto A\vec x$ is onto iff $A$ has a right inverse; disabled in the boss. -/
TheoremDoc Matrix.mulVec_surjective_iff_exists_right_inverse as "mulVec_surjective_iff_exists_right_inverse" in "Matrices"
/-- $(\sum_i \vec u_i)\cdot\vec v = \sum_i \vec u_i\cdot\vec v$. -/
TheoremDoc sum_dotProduct as "sum_dotProduct" in "Projection"
/-- `div_mul_cancel₀ a h : a / b * b = a` for `h : b ≠ 0`. -/
TheoremDoc div_mul_cancel₀ as "div_mul_cancel₀" in "Projection"
/-- If $a \le b$ then $\sqrt a \le \sqrt b$. -/
TheoremDoc Real.sqrt_le_sqrt as "Real.sqrt_le_sqrt" in "Projection"
/-- `Real.sqrt_mul_self (h : 0 ≤ a) : √(a * a) = a`. -/
TheoremDoc Real.sqrt_mul_self as "Real.sqrt_mul_self" in "Projection"
/-- $a + (b - a) = b$. -/
TheoremDoc add_sub_cancel as "add_sub_cancel" in "Projection"
/-- `Finset.sum_eq_single i` : if every term other than the $i$-th is zero (and $i$ is in range), the sum equals its $i$-th term. Leaves those two side conditions as goals. -/
TheoremDoc Finset.sum_eq_single as "Finset.sum_eq_single" in "Sums"
/-- `insert a s ⊆ t ↔ a ∈ t ∧ s ⊆ t`; splits `{a, b, …} ⊆ t`. -/
TheoremDoc Set.insert_subset_iff as "insert_subset_iff" in "Subspaces"
/-- `{a} ⊆ t ↔ a ∈ t`. -/
TheoremDoc Set.singleton_subset_iff as "singleton_subset_iff" in "Subspaces"
/-- $a / 1 = a$. -/
TheoremDoc div_one as "div_one" in "Sums"
/-- $0 / a = 0$. -/
TheoremDoc zero_div as "zero_div" in "Sums"
/-- $a - 0 = a$. -/
TheoremDoc sub_zero as "sub_zero" in "Sums"
/-- $a - b - c = a - c - b$. -/
TheoremDoc sub_right_comm as "sub_right_comm" in "Projection"
/-- Mathlib's Gram–Schmidt orthogonality; disabled in the boss. -/
TheoremDoc InnerProductSpace.gramSchmidt_orthogonal as "gramSchmidt_orthogonal" in "Projection"
/-- Mathlib's Gram–Schmidt span equality; disabled in the boss. -/
TheoremDoc InnerProductSpace.span_gramSchmidt as "span_gramSchmidt" in "Projection"

/-! ## First documented in Ch45 -/

/-- `Commute.all a b`: in a commutative ring, $ab = ba$. -/
TheoremDoc Commute.all as "all" in "Eigen"
/-- `Equivalence r`: `r` is reflexive, symmetric and transitive (`constructor` splits it). -/
DefinitionDoc Equivalence as "Equivalence"
/-- $\prod_{i<2} f(i) = f(0)f(1)$. -/
TheoremDoc Fin.prod_univ_two as "prod_univ_two" in "Det"
/-- `Finset.univ.card = Fintype.card α`. -/
TheoremDoc Finset.card_univ as "card_univ" in "Eigen"
/-- Two products over the same set are equal if their factors agree pointwise. -/
TheoremDoc Finset.prod_congr as "prod_congr" in "Eigen"
/-- $\prod_{i\in s}(-f(i)) = (-1)^{|s|}\prod_{i \in s} f(i)$. -/
TheoremDoc Finset.prod_neg as "prod_neg" in "Eigen"
/-- A product of an updated function: replacing $f(i)$ by $b$ gives $b\cdot\prod_{j \ne i} f(j)$. -/
TheoremDoc Finset.prod_update_of_mem as "prod_update_of_mem" in "Eigen"
/-- `s \ {a} = s.erase a`. -/
TheoremDoc Finset.sdiff_singleton_eq_erase as "sdiff_singleton_eq_erase" in "Eigen"
/-- $(\sum_i f(i))\,a = \sum_i f(i)\,a$. -/
TheoremDoc Finset.sum_mul as "sum_mul" in "Eigen"
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
/-- `matSimilar_of_mul_eq_one P Q hQP h`: if $QP = I$ and $S = PTQ$ then `MatSimilar T S` (so $Q = P^{-1}$ need not be computed). $P$ and $Q$ are given explicitly. -/
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
/-- $\begin{vmatrix} a & b \\ c & d\end{vmatrix} = ad - bc$. -/
TheoremDoc Matrix.det_fin_two_of as "det_fin_two_of" in "Det"
/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_mul_comm as "det_mul_comm" in "Det"
/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc Matrix.det_nonsing_inv as "det_nonsing_inv" in "Det"
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
/-- The $(i,i)$ entry of `diagonal d` is $d_i$. -/
TheoremDoc Matrix.diagonal_apply_eq as "diagonal_apply_eq" in "Eigen"
/-- Off-diagonal entries of `diagonal d` are $0$. -/
TheoremDoc Matrix.diagonal_apply_ne as "diagonal_apply_ne" in "Eigen"
/-- `diagonal d = diagonal e ↔ ∀ i, d i = e i`. -/
TheoremDoc Matrix.diagonal_eq_diagonal_iff as "diagonal_eq_diagonal_iff" in "Eigen"
/-- `diagonal (c • d) = c • diagonal d`. -/
TheoremDoc Matrix.diagonal_smul as "diagonal_smul" in "Eigen"
/-- Replacing row $i$ of `diagonal d` by $c\,\vec e_i$ gives `diagonal (Function.update d i c)`. -/
TheoremDoc Matrix.diagonal_updateRow_single as "diagonal_updateRow_single" in "Det"
/-- `diagonal (fun _ => 0) = 0`. Note the left side is written `diagonal (fun _ => 0)`, so
`rw [diagonal_zero]` does not fire on `diagonal 0`; use `exact diagonal_zero` to close
`diagonal 0 = 0`, or `rw [← diagonal_zero]` to turn a `0` matrix into a diagonal one. -/
TheoremDoc Matrix.diagonal_zero as "diagonal_zero" in "Eigen"
/-- $M\vec v = \vec 0$ has a nonzero solution iff $\det M = 0$ (Chapter Three / Lemma Four.I.2.4). -/
TheoremDoc Matrix.exists_mulVec_eq_zero_iff as "exists_mulVec_eq_zero_iff" in "Eigen"
/-- $A(-\vec v) = -(A\vec v)$. -/
TheoremDoc Matrix.mulVec_neg as "mulVec_neg" in "Eigen"
/-- $M\vec e_j$ is column $j$ of $M$. -/
TheoremDoc Matrix.mulVec_single_one as "mulVec_single_one" in "Eigen"
/-- $A\operatorname{adj}(A) = \det(A)\,I$. -/
TheoremDoc Matrix.mul_adjugate as "mul_adjugate" in "Det"
/-- $(AB)^{-1} = B^{-1}A^{-1}$. -/
TheoremDoc Matrix.mul_inv_rev as "mul_inv_rev" in "Eigen"
/-- $A(cB) = c(AB)$. -/
TheoremDoc Matrix.mul_smul as "mul_smul" in "Eigen"
/-- $A(B - C) = AB - AC$. -/
TheoremDoc Matrix.mul_sub as "mul_sub" in "Eigen"
/-- $(-A)\vec v = -(A\vec v)$. -/
TheoremDoc Matrix.neg_mulVec as "neg_mulVec" in "Eigen"
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
/-- `Submodule.span ℝ S`: the span $[S]$ of a set $S$. -/
DefinitionDoc Submodule.span as "span"
/-- $|ab| = |a||b|$. -/
TheoremDoc abs_mul as "abs_mul" in "Det"
/-- Mathlib's version of this level's statement; disabled here. -/
TheoremDoc conj_pow as "conj_pow" in "Eigen"
/-- The span of one nonzero vector has dimension $1$. -/
TheoremDoc finrank_span_singleton as "finrank_span_singleton" in "Eigen"
/-- $1^{-1} = 1$. -/
TheoremDoc inv_one as "inv_one" in "Eigen"
/-- $1$ (in particular $I$) is invertible. -/
TheoremDoc isUnit_one as "isUnit_one" in "Eigen"
/-- If $ab = 1$ then $a \ne 0$. -/
TheoremDoc left_ne_zero_of_mul_eq_one as "left_ne_zero_of_mul_eq_one" in "Det"
/-- A ring homomorphism preserves products. -/
TheoremDoc map_mul as "map_mul" in "Eigen"
/-- A ring homomorphism sends $1$ to $1$. -/
TheoremDoc map_one as "map_one" in "Eigen"
/-- $(ab)c = a(bc)$. -/
TheoremDoc mul_assoc as "mul_assoc" in "Eigen"
/-- If $a \ne 0$ and $b \ne 0$ then $ab \ne 0$. -/
TheoremDoc mul_ne_zero as "mul_ne_zero" in "Eigen"
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
/-- $a - b \ne 0 \iff a \ne b$. -/
TheoremDoc sub_ne_zero as "sub_ne_zero" in "Eigen"
/-- $0 \le 1$. -/
TheoremDoc zero_le_one as "zero_le_one" in "Det"
/-- `Ne.symm h : b ≠ a` from `h : a ≠ b`. -/
TheoremDoc Ne.symm as "Ne.symm" in "Det"
/-- `Polynomial.coeff_natDegree : p.coeff p.natDegree = p.leadingCoeff` — the top coefficient is the leading coefficient. -/
TheoremDoc Polynomial.coeff_natDegree as "coeff_natDegree" in "Eigen"
/-- `hd.scale_eq M N i k h`: if `h : M.updateRow i (k • M i) = N` (scale row `i` of `M` by `k`
to get `N`), then `d N = k * d M`. Prove `h` with `entrywise <;> simp`. -/
TheoremDoc LinearAlgebraGame.DetAxioms.scale_eq as "DetAxioms.scale_eq" in "Det"
/-- `hd.combo_eq M N i j k hij h`: if `h : M.updateRow j (M j + k • M i) = N` (add `k` times row
`i` to row `j`), then `d N = d M`. Prove `h` with `entrywise <;> simp`. -/
TheoremDoc LinearAlgebraGame.DetAxioms.combo_eq as "DetAxioms.combo_eq" in "Det"
/-- `hd.swap_eq M N i j hij h`: if `h : swapRows M i j = N`, then `d N = - d M`. Prove `h`
with `entrywise <;> simp [swapRows]`. -/
TheoremDoc LinearAlgebraGame.DetAxioms.swap_eq as "DetAxioms.swap_eq" in "Det"
/-- $(x - a)(x - b) = x^2 - (a+b)x + ab$, with constants written `C a`. -/
TheoremDoc LinearAlgebraGame.X_sub_C_mul_X_sub_C as "X_sub_C_mul_X_sub_C" in "Eigen"
/-- `v ∈ eigenspace (toLin' T) μ ↔ T *ᵥ v = μ • v`. -/
TheoremDoc LinearAlgebraGame.mem_eigenspace_toLin' as "mem_eigenspace_toLin'" in "Eigen"
/-- `Pi.single_eq_of_ne' (h : i ≠ j) x : Pi.single i x j = 0` — the vector $x\vec e_i$ is zero
away from position $i$. (Compare `Pi.single_apply`, which gives the general `if … then … else …`.) -/
TheoremDoc Pi.single_eq_of_ne' as "single_eq_of_ne'" in "Det"
/-- $p(x)q(x)$ evaluated at $a$ is $p(a)q(a)$. -/
TheoremDoc Polynomial.eval_mul as "eval_mul" in "Eigen"
/-- $p(x)^n$ evaluated at $a$ is $p(a)^n$. -/
TheoremDoc Polynomial.eval_pow as "eval_pow" in "Eigen"
/-- The columns of a square matrix $Q$ are linearly independent iff $Q$ is nonsingular:
`LinearIndependent K (fun i => Qᵀ i) ↔ IsUnit Q`. -/
TheoremDoc Matrix.linearIndependent_col_iff_isUnit as "linearIndependent_col_iff_isUnit" in "Eigen"
/-- `C (a - b) = C a - C b`. -/
TheoremDoc Polynomial.C_sub as "C_sub" in "Eigen"
/-- `C (a * b) = C a * C b`. -/
TheoremDoc Polynomial.C_mul as "C_mul" in "Eigen"
