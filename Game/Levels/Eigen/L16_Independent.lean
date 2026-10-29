import Game.Levels.Eigen.L15_Inverse

World "Eigen"
Level 16
Title "Boss: distinct eigenvalues"

Introduction "
**Theorem Five.II.3.18.** Eigenvectors belonging to distinct eigenvalues are linearly
independent. Hefferon proves it by induction on the number $k$ of eigenvectors: from a
relation $c_1\\vec v_1 + \\cdots + c_k\\vec v_k = \\vec 0$, apply $t$ and subtract $\\lambda_k$ times
the relation; the last vector drops out, and the induction hypothesis kills the rest. Here
you prove the case of **two** eigenvectors — the first step of that induction, and the whole
idea — for any linear map $t\\colon V \\to V$. The next world turns it into a
diagonalisation theorem.

`LinearIndependent.pair_iff` turns independence of $\\langle\\vec v, \\vec w\\rangle$ into:
$c\\vec v + d\\vec w = \\vec 0 \\Rightarrow c = d = 0$.
"

namespace LinearAlgebraGame

/-- If $t\vec v = a\vec v$, $t\vec w = b\vec w$, $\vec v, \vec w \ne \vec 0$ and $a \ne b$, then $\vec v, \vec w$ are linearly independent. -/
Statement linearIndependent_of_eigen {V : Type*} [AddCommGroup V] [Module ℝ V] (t : V →ₗ[ℝ] V) (v w : V) (a b : ℝ)
    (hv : t v = a • v) (hw : t w = b • w) (hv0 : v ≠ 0) (hw0 : w ≠ 0) (hab : a ≠ b) :
    LinearIndependent ℝ ![v, w] := by
  Hint "Suppose $c\\vec v + d\\vec w = \\vec 0$. Apply $t$, subtract $a$ times the original
  relation: the $\\vec v$ terms cancel, leaving $d(b - a)\\vec w = \\vec 0$."
  rw [LinearIndependent.pair_iff]
  intro c d h
  Hint (hidden := true) "`have h1 : t (c • v + d • w) = 0 := by rw [h, map_zero]`, then
  `rw [map_add, map_smul, map_smul, hv, hw] at h1`."
  have h1 : t (c • v + d • w) = 0 := by rw [h, map_zero]
  rw [map_add, map_smul, map_smul, hv, hw] at h1
  Hint (hidden := true) "`have h2 : (d * (b - a)) • w = 0`: write it as
  `(c • a • v + d • b • w) - a • (c • v + d • w)` (by `module`), then use `h1` and `h`."
  have h2 : (d * (b - a)) • w = 0 := by
    calc (d * (b - a)) • w = (c • a • v + d • b • w) - a • (c • v + d • w) := by module
      _ = 0 := by rw [h1, h, smul_zero, sub_zero]
  have hd : d = 0 := by
    Hint (hidden := true) "`smul_eq_zero`, `mul_eq_zero`, `sub_ne_zero`."
    rcases smul_eq_zero.1 h2 with h3 | h3
    · rcases mul_eq_zero.1 h3 with h4 | h4
      · exact h4
      · exfalso
        exact sub_ne_zero.2 (Ne.symm hab) h4
    · exfalso
      exact hw0 h3
  Hint (hidden := true) "Now `c • v = 0`: `rw [hd, zero_smul, add_zero] at h`."
  rw [hd, zero_smul, add_zero] at h
  rcases smul_eq_zero.1 h with hc | hc
  · exact ⟨hc, hd⟩
  · exfalso
    exact hv0 hc

end LinearAlgebraGame

Conclusion "
With induction this gives the full theorem, and hence **Corollary 3.19**: an $n\\times n$
matrix with $n$ distinct eigenvalues is diagonalisable. You will prove the $2\\times2$ case in
the next world.
"

NewTheorem map_zero
DisabledTheorem Module.End.eigenvectors_linearIndependent Module.End.eigenvectors_linearIndependent'
TheoremTab "Eigen"
