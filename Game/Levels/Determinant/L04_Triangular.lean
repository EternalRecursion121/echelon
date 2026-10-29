import Game.Levels.Determinant.L03_Diagonal

World "Determinant"
Level 4
Title "A triangular matrix"

Introduction "
**Lemma Four.I.2.4 (4)**, $2\\times2$ case: the determinant of an upper triangular matrix is
the product of its diagonal,
$d\\begin{pmatrix} a & b \\\\ 0 & c\\end{pmatrix} = ac$.

This is how Hefferon computes determinants: Gauss's method to echelon form, then multiply
the diagonal. (For general $n$ it is the same argument, done by induction; Mathlib calls
the result `Matrix.det_of_upperTriangular`.)

Condition (2) has the same kind of helper:
`hd.combo_eq M N i j k hij h : d N = d M`, where `h` proves that adding $k$ times row `i` to
row `j` of `M` gives `N`.
"

namespace LinearAlgebraGame

/-- $d\begin{pmatrix} a & b \\ 0 & c\end{pmatrix} = ac$ for every determinant function $d$. -/
Statement det_triangular_two (d : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (hd : DetAxioms d) (a b c : ℝ) :
    d !![a, b; 0, c] = a * c := by
  Hint "Idea: if $c = 0$ there is a zero row. Otherwise add $-b/c$ times row $1$
  to row $0$ to clear $b$, and use the diagonal level."
  Hint (hidden := true) "`by_cases hc : c = 0`."
  by_cases hc : c = 0
  · Hint (hidden := true) "`rw [hc, mul_zero]`, then
    `apply det_eq_zero_of_row_zero d hd _ 1` and show row 1 is zero with `ext j; fin_cases j <;> simp`."
    rw [hc, mul_zero]
    apply det_eq_zero_of_row_zero d hd _ 1
    ext j
    fin_cases j <;> simp
  · Hint (hidden := true) "Add $-b/c$ times row `1` to row `0`:
    `have h := hd.combo_eq !![a, b; 0, c] !![a, 0; 0, c] 1 0 (-b / c) (by simp) (by …)`.
    The last `by` proves the matrix identity: `entrywise <;> simp`, then `field_simp` and
    `ring` for the entry that involves $b/c$."
    have h := hd.combo_eq !![a, b; 0, c] !![a, 0; 0, c] 1 0 (-b / c) (by simp)
      (by entrywise <;> simp; field_simp; ring)
    Hint (hidden := true) "`rw [← h, det_diag_two d hd]`."
    rw [← h, det_diag_two d hd]

end LinearAlgebraGame

Conclusion "
Gauss's method brings every matrix to echelon form, and now you know $d$ on those. Next:
turn this into a proof that the four conditions determine $d$ completely.
"

NewTheorem LinearAlgebraGame.det_eq_zero_of_row_zero LinearAlgebraGame.det_diag_two LinearAlgebraGame.DetAxioms.combo_eq
TheoremTab "Det"
