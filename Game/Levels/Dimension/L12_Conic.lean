import Game.Levels.Dimension.L11_EightTen

World "Dimension"
Level 12
Title "Five points on a conic"

-- @sheet 2 Q10
/-! @answer
A conic $ax^2 + by^2 + cxy + dx + ey + f = 0$ passes through $(x_i, y_i)$ iff
$a x_i^2 + b y_i^2 + c x_iy_i + d x_i + e y_i + f = 0$ — a **homogeneous linear** equation in
the six unknowns $a,\dots,f$. Five points give a homogeneous system of 5 equations in 6
unknowns, $M\vec v = \vec 0$ with $M$ the $5\times6$ matrix with rows
$(x_i^2, y_i^2, x_iy_i, x_i, y_i, 1)$. It has more unknowns than equations, so it has a
nontrivial solution (the 6 columns of $M$ are 6 vectors in $\mathbb R^5$, hence dependent, and a
dependence $\sum v_j\,\mathrm{col}_j = \vec 0$ is exactly $M\vec v = \vec 0$ with $\vec v \ne \vec 0$).
That $\vec v = (a,\dots,f)$ is a conic through all five points.
-/
Introduction "
**Problem Sheet 2, Question 10 (optional).** Show that any set of five points from the plane
$\\mathbb R^2$ lie on a common conic section, that is, they all satisfy some equation of the
form $ax^2 + by^2 + cxy + dx + ey + f = 0$ where some of $a, \\dots, f$ are nonzero.

The points are $(x_i, y_i)$, $i = 0,\\dots,4$. The conic through them is a kernel vector of the
given $5 \\times 6$ matrix $M$ whose row $i$ is $(x_i^2, y_i^2, x_iy_i, x_i, y_i, 1)$: row $i$ of
$M\\vec v = \\vec 0$ says the conic with coefficients $\\vec v = (a, b, c, d, e, f)$ passes
through point $i$.

The six columns of $M$ live in $\\mathbb R^5$. `LinearIndependent.fintype_card_le_finrank`
bounds the size of an independent family by the dimension;
`Fintype.not_linearIndependent_iff` turns dependence into a nontrivial relation.
"

namespace LinearAlgebraGame

open Matrix

/-- The $5\times 6$ conic matrix of five points has a nonzero kernel vector. -/
Statement (x y : Fin 5 → ℝ) :
    let M : Matrix (Fin 5) (Fin 6) ℝ :=
      Matrix.of fun i => ![x i ^ 2, y i ^ 2, x i * y i, x i, y i, 1]
    ∃ v : Fin 6 → ℝ, v ≠ 0 ∧ M *ᵥ v = 0 := by
  Hint "Six columns in a 5-dimensional space cannot be independent."
  have hdep : ¬ LinearIndependent ℝ M.col := by
    intro h
    have := h.fintype_card_le_finrank
    rw [Fintype.card_fin, Module.finrank_fin_fun] at this
    omega
  Hint "A dependence among the columns is a nonzero $\\vec v$ with $M\\vec v = 0$."
  rw [Fintype.not_linearIndependent_iff] at hdep
  obtain ⟨g, hg, i, hi⟩ := hdep
  refine ⟨g, ?_, ?_⟩
  · intro h0
    apply hi
    rw [h0]
    exact rfl
  · Hint "$M g$ is the sum of $g_j$ times column $j$: compare coordinates."
    rw [← hg]
    ext r
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]

end LinearAlgebraGame

Conclusion "
More unknowns than equations: five points always lie on a conic.
"

TheoremTab "Dimension"
NewTheorem LinearIndependent.fintype_card_le_finrank
