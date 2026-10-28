import Game.Levels.Isomorphisms.L05_RepIso

World "Isomorphisms"
Level 6
Title "The dimension of an external direct sum"

-- @sheet 6 Q2a
/-! @answer
$\dim(U \times W) = \dim U + \dim W$. If $\langle\vec\beta_1,\dots,\vec\beta_n\rangle$ is a basis
of $U$ and $\langle\vec\delta_1,\dots,\vec\delta_m\rangle$ a basis of $W$, then
$\langle(\vec\beta_1,\vec 0),\dots,(\vec\beta_n,\vec 0),(\vec 0,\vec\delta_1),\dots,(\vec 0,\vec\delta_m)\rangle$
is a basis of $U\times W$: $(\vec u,\vec w)=(\vec u,\vec 0)+(\vec 0,\vec w)$ shows it spans, and a
relation among these vectors splits into a relation among the $\vec\beta$'s (first component)
and among the $\vec\delta$'s (second component), so all coefficients vanish. It has $n+m$ vectors.
-/
Introduction "
**Problem Sheet 6, Question 2(a).** Let $U$ and $W$ be vector spaces. The set
$U \\times W = \\{(\\vec u, \\vec w)\\}$ with componentwise operations is a vector space, the
*external direct sum* of $U$ and $W$. What is the relationship among $\\dim(U)$, $\\dim(W)$ and
$\\dim(U \\times W)$? *Hint: give a basis for $U \\times W$. You may omit the proof that it is
a basis.*

As the sheet allows, the fact that your sequence is a basis is granted: for bases `B` of $U$
and `D` of $W$, Lean's `B.prod D` is the basis
$\\langle(\\vec\\beta_1,\\vec 0),\\dots,(\\vec 0,\\vec\\delta_1),\\dots\\rangle$, indexed by
`Fin n ⊕ Fin m`. `Module.finBasis ℝ U` is a basis of $U$ with $\\dim U$ vectors.
"

namespace LinearAlgebraGame

/-- $\dim(U\times W) = \dim U + \dim W$. -/
Statement {U W : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup W] [Module ℝ W]
    [FiniteDimensional ℝ U] [FiniteDimensional ℝ W] :
    Module.finrank ℝ (U × W) = Module.finrank ℝ U + Module.finrank ℝ W := by
  Hint "The dimension is the number of vectors in any basis. Which basis of $U \\times W$
  do you know?"
  Hint (hidden := true) "`rw [Module.finrank_eq_card_basis ((Module.finBasis ℝ U).prod (Module.finBasis ℝ W))]`
  turns the left side into the number of indices."
  rw [Module.finrank_eq_card_basis ((Module.finBasis ℝ U).prod (Module.finBasis ℝ W))]
  Hint (hidden := true) "Count: `rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]`."
  rw [Fintype.card_sum, Fintype.card_fin, Fintype.card_fin]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q2(a):** $\\dim(U\\times W) = \\dim U + \\dim W$, with basis the
$\\vec\\beta$'s paired with $\\vec 0$ followed by $\\vec 0$ paired with the $\\vec\\delta$'s.
"

NewDefinition Module.Basis.prod Module.finBasis
DisabledTheorem Module.finrank_prod
DisabledTactic simp norm_num
TheoremTab "Dimension"
