import Game.Levels.Determinant.L02_ZeroRow

World "Determinant"
Level 3
Title "A diagonal matrix"

Introduction "
The four conditions already pin down the determinant of a diagonal matrix. We do the
$2\\times 2$ case: $d\\begin{pmatrix} a & 0 \\\\ 0 & c\\end{pmatrix} = ac$.

Start from $I$, scale row $1$ (the second row; Lean counts from $0$) by $c$, then row $0$
by $a$. Each step is condition (3); the last word is condition (4).

You will need to identify matrices like `(1 : Matrix _ _ ℝ).updateRow 1 (c • 1 1)` with
`!![1, 0; 0, c]`. Prove such equalities entry by entry:
`entrywise <;> simp`.
"

namespace LinearAlgebraGame

/-- $d\begin{pmatrix} a & 0 \\ 0 & c\end{pmatrix} = ac$ for every determinant function $d$. -/
Statement det_diag_two (d : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (hd : DetAxioms d) (a c : ℝ) :
    d !![a, 0; 0, c] = a * c := by
  Hint "Idea: d(diag(a, c)) = a · d(diag(1, c)) = a · c · d(I) = ac, using condition (3) twice and then (4)."
  Hint (hidden := true) "`have h1 := hd.scale 1 1 c` and `have h2 := hd.scale !![1, 0; 0, c] 0 a`."
  have h1 := hd.scale 1 1 c
  have h2 := hd.scale !![1, 0; 0, c] 0 a
  Hint (hidden := true) "Now prove the two matrix identities with `have e1 : … = !![1, 0; 0, c]`
  (and `e2` for `!![a, 0; 0, c]`), each by `entrywise <;> simp`."
  have e1 : (1 : Matrix (Fin 2) (Fin 2) ℝ).updateRow 1 (c • (1 : Matrix (Fin 2) (Fin 2) ℝ) 1)
      = !![1, 0; 0, c] := by
    entrywise <;> simp
  have e2 : (!![1, 0; 0, c] : Matrix (Fin 2) (Fin 2) ℝ).updateRow 0 (a • !![1, 0; 0, c] 0)
      = !![a, 0; 0, c] := by
    entrywise <;> simp
  Hint (hidden := true) "Rewrite `e1` and `hd.one` in `h1`, then `e2` and `h1` in `h2`."
  rw [e1, hd.one, mul_one] at h1
  rw [e2, h1] at h2
  exact h2

end LinearAlgebraGame

Conclusion "For $n \\times n$ the same argument gives $d(\\mathrm{diag}(a_1,\\dots,a_n)) = a_1\\cdots a_n$."

TheoremTab "Det"
