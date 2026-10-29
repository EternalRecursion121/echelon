import Game.Levels.Dimension.L13_Meet

World "Dimension"
Level 14
Title "Eight and eight in ten"

-- @sheet 6 Q1d
/-! @answer
$W_1 \subseteq W_1 + W_2 \subseteq V$, so $8 \le \dim(W_1+W_2) \le 10$. By the dimension formula
$\dim(W_1\cap W_2) = 8 + 8 - \dim(W_1+W_2) \in \{6, 7, 8\}$.
All three occur in $\mathbb R^{10}$: with $e_1,\dots,e_{10}$ the standard basis, take
$W_1 = [e_1,\dots,e_8]$ and $W_2 = [e_3,\dots,e_{10}]$, $[e_2,\dots,e_9]$ or $W_1$ itself; the sums
are spanned by 10, 9, 8 of the $e_i$, giving intersections of dimension **6, 7, 8**.
-/
Introduction "
**Problem Sheet 6, Question 1(d).** Let $W_1$ and $W_2$ be eight-dimensional subspaces of a
ten-dimensional space. List all values possible for $\\dim(W_1 \\cap W_2)$.

You supply the answer: a finite set `S` of numbers (a `Finset ℕ`, written like `{1, 2}`), and
prove that **every** such intersection has dimension in `S`, **and** that every value in `S`
actually occurs (in $\\mathbb R^{10}$). Membership of a `Finset` literal unfolds with
`Finset.mem_insert` and `Finset.mem_singleton`.

Tools: your `dim_formula` with `exists_bases_inf`. For the examples: `coordSpan S` is the span
of the standard basis vectors $e_i$, $i\\in S$; `finrank_coordSpan` says its dimension is $|S|$,
and `coordSpan_sup` says `coordSpan S ⊔ coordSpan T = coordSpan (S ∪ T)`. Counting a concrete
finite set can be done by `decide`.
"

namespace LinearAlgebraGame

/-- The set $S$ of all possible values of $\dim(W_1\cap W_2)$. -/
Statement : ∃ S : Finset ℕ,
    (∀ (V : Type) [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V],
      Module.finrank ℝ V = 10 → ∀ W₁ W₂ : Submodule ℝ V,
        Module.finrank ℝ W₁ = 8 → Module.finrank ℝ W₂ = 8 →
          Module.finrank ℝ ↥(W₁ ⊓ W₂) ∈ S) ∧
    (∀ t ∈ S, ∃ W₁ W₂ : Submodule ℝ (Fin 10 → ℝ),
      Module.finrank ℝ W₁ = 8 ∧ Module.finrank ℝ W₂ = 8 ∧ Module.finrank ℝ ↥(W₁ ⊓ W₂) = t) := by
  Hint "Work out the possible values on paper: how big can $W_1 + W_2$ be? Then `use` your set."
  Hint (hidden := true) "`use \{6, 7, 8}`"
  use {6, 7, 8}
  constructor
  · Hint "$8 \\le \\dim(W_1 + W_2) \\le 10$, then the dimension formula."
    intro V _ _ _ hV W₁ W₂ h1 h2
    Hint (hidden := true) "`obtain ⟨j, k, p, β, μ, ω, hβ, hU, hW⟩ := exists_bases_inf W₁ W₂` and
    `have key := dim_formula W₁ W₂ β μ ω hβ hU hW`."
    obtain ⟨j, k, p, β, μ, ω, hβ, hU, hW⟩ := exists_bases_inf W₁ W₂
    have key := dim_formula W₁ W₂ β μ ω hβ hU hW
    Hint (hidden := true) "Three bounds: `Submodule.finrank_le (W₁ ⊔ W₂)`,
    `finrank_le_of_le _ _ (le_sup_left : W₁ ≤ W₁ ⊔ W₂)` and
    `finrank_le_of_le _ _ (inf_le_left : W₁ ⊓ W₂ ≤ W₁)`."
    have hle := Submodule.finrank_le (W₁ ⊔ W₂)
    have hge := finrank_le_of_le _ _ (le_sup_left : W₁ ≤ W₁ ⊔ W₂)
    have hi := finrank_le_of_le _ _ (inf_le_left : W₁ ⊓ W₂ ≤ W₁)
    rw [h1, h2] at key
    rw [h1] at hge hi
    rw [hV] at hle
    Hint (hidden := true) "`rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]`
    then `omega`."
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton]
    omega
  · Hint "First a formula for coordinate spans: by the dimension formula,
    the intersection of the coordinate spans of $S$ and $T$ has dimension $|S| + |T| - |S \\cup T|$."
    have hc : ∀ S T : Finset (Fin 10), Module.finrank ℝ ↥(coordSpan S ⊓ coordSpan T) =
        S.card + T.card - (S ∪ T).card := by
      intro S T
      obtain ⟨j, k, p, β, μ, ω, hβ, hU, hW⟩ := exists_bases_inf (coordSpan S) (coordSpan T)
      have key := dim_formula _ _ β μ ω hβ hU hW
      have hi := finrank_le_of_le _ _ (inf_le_left : coordSpan S ⊓ coordSpan T ≤ coordSpan S)
      rw [coordSpan_sup, finrank_coordSpan, finrank_coordSpan, finrank_coordSpan] at key
      rw [finrank_coordSpan] at hi
      omega
    intro t ht
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton] at ht
    Hint "Take $W_1 = [e_0, \\dots, e_7]$ and slide $W_2$."
    rcases ht with rfl | rfl | rfl
    · refine ⟨coordSpan {0, 1, 2, 3, 4, 5, 6, 7}, coordSpan {2, 3, 4, 5, 6, 7, 8, 9}, ?_, ?_, ?_⟩
      · rw [finrank_coordSpan]; decide
      · rw [finrank_coordSpan]; decide
      · rw [hc]; decide
    · refine ⟨coordSpan {0, 1, 2, 3, 4, 5, 6, 7}, coordSpan {1, 2, 3, 4, 5, 6, 7, 8}, ?_, ?_, ?_⟩
      · rw [finrank_coordSpan]; decide
      · rw [finrank_coordSpan]; decide
      · rw [hc]; decide
    · refine ⟨coordSpan {0, 1, 2, 3, 4, 5, 6, 7}, coordSpan {0, 1, 2, 3, 4, 5, 6, 7}, ?_, ?_, ?_⟩
      · rw [finrank_coordSpan]; decide
      · rw [finrank_coordSpan]; decide
      · rw [hc]; decide

end LinearAlgebraGame

Conclusion "
**$\\dim(W_1\\cap W_2) \\in \\{6, 7, 8\\}$**, and all three happen.
"

NewDefinition LinearAlgebraGame.coordSpan
NewTheorem LinearAlgebraGame.finrank_coordSpan LinearAlgebraGame.coordSpan_sup le_sup_left inf_le_left Finset.mem_insert Finset.mem_singleton
TheoremTab "Sums"
NewTactic decide
