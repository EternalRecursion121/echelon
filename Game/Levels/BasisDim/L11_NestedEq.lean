import Game.Levels.BasisDim.L10_DimMono

World "BasisDim"
Level 11
Title "Nested subspaces of equal dimension"

-- @sheet 4 Q10b
/-! @answer
If $U = W$ the dimensions are equal. Conversely suppose $U \subseteq W$ and
$\dim U = \dim W$ but $U \ne W$; pick $\vec w \in W$ with $\vec w \notin U$. By the extension
lemma (Lemma Two.II.1.15) a basis of $U$ together with $\vec w$ is still independent, so
$U + [\{\vec w\}]$ has dimension $\dim U + 1$. But $U + [\{\vec w\}] \subseteq W$, so by (a)
$\dim U + 1 \le \dim W = \dim U$, a contradiction. Hence $U = W$.
-/
Introduction "
**Problem Sheet 4, Question 10(b).** Assuming that $U$ and $W$ are finite-dimensional
(and $U \\subseteq W$), prove that equality of dimension holds if and only if $U = W$.

You need this result for Sheet 3 Q11, so it comes early.

Your tools: part (a) `finrank_le_of_le`, and the extension lemma in dimension form,
`Submodule.finrank_sup_span_singleton`: if $\\vec w \\notin U$ then
$\\dim(U + [\\{\\vec w\\}]) = \\dim U + 1$. Lean displays the line $[\\{\\vec w\\}]$,
`Submodule.span ℝ {w}`, in the short notation `ℝ ∙ w`.

**New:** `omega` proves (in)equalities about natural numbers (and integers) that follow from the
hypotheses by adding and comparing — handy for juggling dimensions.
"

namespace LinearAlgebraGame

/-- For $U \subseteq W$ (finite-dimensional): $\dim U = \dim W \iff U = W$. -/
Statement eq_iff_finrank_eq_of_le {V : Type*} [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] (U W : Submodule ℝ V) (h : U ≤ W) :
    Module.finrank ℝ U = Module.finrank ℝ W ↔ U = W := by
  constructor
  · intro hd
    Hint "Show $W \\subseteq U$. Take $\\vec w \\in W$ and suppose $\\vec w \\notin U$:
    adding $\\vec w$ to $U$ makes a subspace of $W$ that is too big."
    apply le_antisymm h
    intro w hw
    by_contra hwU
    Hint (hidden := true) "`have h1 := Submodule.finrank_sup_span_singleton {hwU}`"
    have h1 := Submodule.finrank_sup_span_singleton hwU
    Hint (hidden := true) "Now show that $U$ plus the span of $\\vec w$ lies in $W$: use `sup_le {h}` and
    `(Submodule.span_singleton_le_iff_mem _ _).mpr {hw}`."
    have h2 : U ⊔ Submodule.span ℝ {w} ≤ W :=
      sup_le h ((Submodule.span_singleton_le_iff_mem _ _).mpr hw)
    have h3 := finrank_le_of_le _ _ h2
    Hint (hidden := true) "The numbers no longer add up: `omega`."
    omega
  · Hint "The easy direction."
    intro he
    rw [he]

end LinearAlgebraGame

Conclusion "
Nested subspaces of equal finite dimension are equal. (Mathlib: `Submodule.eq_of_le_of_finrank_eq`.)
"

NewTheorem LinearAlgebraGame.finrank_le_of_le Submodule.finrank_sup_span_singleton sup_le Submodule.span_singleton_le_iff_mem
DisabledTheorem Submodule.eq_of_le_of_finrank_eq Submodule.eq_of_le_of_finrank_le Submodule.finrank_lt_finrank_of_lt Submodule.finrank_mono
DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTactic omega
