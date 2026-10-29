import Game.Levels.BasisDim.L14_Solvable

World "BasisDim"
Level 15
Title "Functions on a finite set"

-- @sheet 4 Q7
/-! @answer
For a finite set $S$, the functions $\delta_s$ ($s\in S$) with $\delta_s(s) = 1$ and
$\delta_s(t) = 0$ for $t \neq s$ form a basis of $\{f : S \to \mathbb R\}$: every $f$ is
$\sum_{s\in S} f(s)\,\delta_s$ (evaluate at each $t$), and if $\sum c_s\delta_s = 0$ then
evaluating at $t$ gives $c_t = 0$. So the dimension is $|S|$:
**(a) 1, (b) 2, (c) $n$, (d) 0** (for $S = \emptyset$ the space is $\{$the empty function$\}$,
the trivial space, with the empty basis).
-/
Introduction "
**Problem Sheet 4, Question 7.** Where $S$ is a set, the functions $f : S \\to \\mathbb R$ form
a vector space under the natural operations. What is the dimension of the space resulting
for each domain? (a) $S = \\{1\\}$ (b) $S = \\{1, 2\\}$ (c) $S = \\{1, \\dots, n\\}$
(d) $S = \\emptyset$.

The claim states the four dimensions — a number cannot be \"supplied\" more honestly than by
proving it. The work is the reason: find a basis of $S \\to \\mathbb R$ and count it.
Mathlib packages the basis you want as `Pi.basisFun ℝ S` (see Definitions), and
`Module.finrank_eq_card_basis` says the dimension is the number of basis vectors.
Prove the general fact first as a `have`, then the four cases.
"

namespace LinearAlgebraGame

/-- $\dim(S\to\mathbb R)$ is $1, 2, n, 0$ for $S = \{1\}, \{1,2\}, \{1..n\}, \emptyset$. -/
Statement :
    Module.finrank ℝ (({1} : Finset ℕ) → ℝ) = 1 ∧
    Module.finrank ℝ (({1, 2} : Finset ℕ) → ℝ) = 2 ∧
    (∀ n : ℕ, Module.finrank ℝ ((Finset.Icc 1 n : Finset ℕ) → ℝ) = n) ∧
    Module.finrank ℝ ((∅ : Finset ℕ) → ℝ) = 0 := by
  Hint "First prove the general fact: for every finite set $S$, the dimension is $|S|$."
  have key : ∀ S : Finset ℕ, Module.finrank ℝ (S → ℝ) = S.card := by
    intro S
    Hint (hidden := true) "`Fintype.card_coe` says the number of elements of `S` (as a type)
    is `S.card`: `rw [Module.finrank_eq_card_basis (Pi.basisFun ℝ S), Fintype.card_coe]`."
    rw [Module.finrank_eq_card_basis (Pi.basisFun ℝ S), Fintype.card_coe]
  Hint "Now count the four sets."
  Hint (hidden := true) "`Finset.card_singleton`, `Finset.card_pair`, `Nat.card_Icc` and
  `Finset.card_empty` count the four sets."
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [key, Finset.card_singleton]
  · Hint (hidden := true) "`Finset.card_pair` needs `1 ≠ 2`: `rw [key, Finset.card_pair (by omega)]`."
    rw [key, Finset.card_pair (by omega)]
  · intro n
    rw [key, Nat.card_Icc]
    omega
  · rw [key, Finset.card_empty]

end LinearAlgebraGame

Conclusion "
$\\dim = |S|$: **1, 2, $n$, 0**.
"

NewDefinition Pi.basisFun
DisabledTheorem Module.finrank_fintype_fun_eq_card Module.finrank_pi Module.finrank_fin_fun
DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTheorem Fintype.card_coe Finset.card_singleton Finset.card_pair Nat.card_Icc Finset.card_empty Module.finrank_eq_card_basis
