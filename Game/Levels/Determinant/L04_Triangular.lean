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
"

namespace LinearAlgebraGame

/-- $d\begin{pmatrix} a & b \\ 0 & c\end{pmatrix} = ac$ for every determinant function $d$. -/
Statement (d : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (hd : DetAxioms d) (a b c : ℝ) :
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
  · Hint (hidden := true) "`have h := hd.combo !![a, b; 0, c] 1 0 (-b / c) (by simp)`."
    have h := hd.combo !![a, b; 0, c] 1 0 (-b / c) (by simp)
    Hint (hidden := true) "Show the new matrix is `!![a, 0; 0, c]`:
    `have e : … = !![a, 0; 0, c] := by ext i j; fin_cases i <;> fin_cases j <;> simp; field_simp`."
    have e : (!![a, b; 0, c] : Matrix (Fin 2) (Fin 2) ℝ).updateRow 0
        (!![a, b; 0, c] 0 + (-b / c) • !![a, b; 0, c] 1) = !![a, 0; 0, c] := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp
      field_simp
      ring
    Hint (hidden := true) "`rw [e, det_diag_two d hd] at h`, then `rw [← h]`."
    rw [e, det_diag_two d hd] at h
    rw [← h]

end LinearAlgebraGame

Conclusion "
So the four conditions determine $d$ on every matrix Gauss's method can reach — which is
every matrix. That is why a determinant function, *if* it exists, is unique (Lemma 2.7).
"

NewTheorem LinearAlgebraGame.det_eq_zero_of_row_zero LinearAlgebraGame.det_diag_two
TheoremTab "Det"
