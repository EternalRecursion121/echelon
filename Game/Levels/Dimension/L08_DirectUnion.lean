import Game.Levels.Dimension.L07_RankOps

World "Dimension"
Level 8
Title "Direct sum and union"

-- @sheet 5 Q1
/-! @answer
**Yes, but only in the trivial way: $W_1\oplus W_2 = V$ and $W_1\cup W_2 = V$ hold exactly when
one of $W_1, W_2$ is $\{\vec 0\}$ and the other is $V$.** These clearly work. Conversely,
first $W_1 \subseteq W_2$ or $W_2 \subseteq W_1$: otherwise pick $\vec a\in W_1\setminus W_2$,
$\vec b \in W_2\setminus W_1$; $\vec a + \vec b \in V = W_1 \cup W_2$, but if it is in $W_1$
then $\vec b = (\vec a+\vec b) - \vec a \in W_1$, and if in $W_2$ then $\vec a\in W_2$ —
contradiction. Say $W_1 \subseteq W_2$. Then $W_1 = W_1\cap W_2 = \{\vec 0\}$ and
$W_2 = W_1 + W_2 = V$. (Symmetrically in the other case.)
-/
Introduction "
**Problem Sheet 5, Question 1.** The example of the $x$-axis and the $y$-axis in
$\\mathbb R^2$ shows that $W_1 \\oplus W_2 = V$ does not imply that $W_1 \\cup W_2 = V$. Can
$W_1 \\oplus W_2 = V$ and $W_1 \\cup W_2 = V$ happen? If so, when?

`IsCompl W₁ W₂` says $V = W_1 \\oplus W_2$: `h.inf_eq_bot` is $W_1 \\cap W_2 = \\{\\vec 0\\}$ and
`h.sup_eq_top` is $W_1 + W_2 = V$. Find the answer on paper first; the claim below states a
precise condition, and you prove it is the right one.

Useful: `IsConcreteLE.not_le_iff_exists` (in the inventory as `not_le_iff_exists`):
`¬ U ≤ W ↔ ∃ x ∈ U, x ∉ W`. Membership of `Set.univ` (everything) is proved by `trivial`.
"

namespace LinearAlgebraGame

/-- If $V = W_1 \oplus W_2$, then $W_1 \cup W_2 = V$ iff $\{W_1, W_2\} = \{\{0\}, V\}$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (W₁ W₂ : Submodule ℝ V)
    (h : IsCompl W₁ W₂) :
    (W₁ : Set V) ∪ W₂ = Set.univ ↔ (W₁ = ⊥ ∧ W₂ = ⊤) ∨ (W₁ = ⊤ ∧ W₂ = ⊥) := by
  constructor
  · intro hu
    Hint "Key step: one of the two subspaces contains the other."
    Hint (hidden := true) "`by_cases h12 : W₁ ≤ W₂`"
    by_cases h12 : W₁ ≤ W₂
    · Hint "Then $W_1 = W_1 \\cap W_2$ and $W_2 = W_1 + W_2$."
      left
      Hint (hidden := true) "`rw [← h.inf_eq_bot, inf_eq_left.mpr {h12}]` and
      `rw [← h.sup_eq_top, sup_eq_right.mpr {h12}]`."
      exact ⟨by rw [← h.inf_eq_bot, inf_eq_left.mpr h12],
        by rw [← h.sup_eq_top, sup_eq_right.mpr h12]⟩
    by_cases h21 : W₂ ≤ W₁
    · right
      exact ⟨by rw [← h.sup_eq_top, sup_eq_left.mpr h21],
        by rw [← h.inf_eq_bot, inf_eq_right.mpr h21]⟩
    Hint "Neither contains the other: pick $a \\in W_1 \\setminus W_2$ and $b \\in W_2 \\setminus W_1$
    and ask where $a + b$ lives."
    Hint (hidden := true) "`obtain ⟨a, haW1, haW2⟩ := IsConcreteLE.not_le_iff_exists.mp h12`
    produces such an element."
    exfalso
    obtain ⟨a, haW1, haW2⟩ := IsConcreteLE.not_le_iff_exists.mp h12
    obtain ⟨b, hbW2, hbW1⟩ := IsConcreteLE.not_le_iff_exists.mp h21
    have hab : a + b ∈ (W₁ : Set V) ∪ W₂ := by
      rw [hu]
      trivial
    rcases hab with h1 | h2
    · apply hbW1
      have := W₁.sub_mem h1 haW1
      rw [add_sub_cancel_left] at this
      exact this
    · apply haW2
      have := W₂.sub_mem h2 hbW2
      rw [add_sub_cancel_right] at this
      exact this
  · Hint "The converse: substitute and check."
    intro hW
    rcases hW with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · ext v; simp
    · ext v; simp

end LinearAlgebraGame

Conclusion "
**Yes, but only trivially:** one summand is $\\{\\vec 0\\}$ and the other is $V$.
"

NewDefinition IsCompl
NewTheorem IsCompl.inf_eq_bot IsCompl.sup_eq_top inf_eq_left inf_eq_right sup_eq_left sup_eq_right IsConcreteLE.not_le_iff_exists trivial
TheoremTab "Sums"
