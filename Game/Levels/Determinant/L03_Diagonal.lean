import Game.Levels.Determinant.L02_ZeroRow

World "Determinant"
Level 3
Title "A diagonal matrix"

Introduction "
The four conditions already pin down the determinant of a diagonal matrix. We do the
$2\\times 2$ case: $d\\begin{pmatrix} a & 0 \\\\ 0 & c\\end{pmatrix} = ac$.

Start from $I$, scale row $1$ (the second row; Lean counts from $0$) by $c$, then row $0$
by $a$. Each step is condition (3); the last word is condition (4).

**A helper.** `hd.scale M i k` talks about `M.updateRow i (k • M i)`, which is unpleasant to
type. Instead use
`hd.scale_eq M N i k h : d N = k * d M`, where you name the resulting matrix `N` yourself
and `h` proves that scaling row `i` of `M` by `k` really gives `N`. Such matrix equalities
are checked entry by entry: `(by entrywise <;> simp)`.
"

namespace LinearAlgebraGame

/-- $d\begin{pmatrix} a & 0 \\ 0 & c\end{pmatrix} = ac$ for every determinant function $d$. -/
Statement det_diag_two (d : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (hd : DetAxioms d) (a c : ℝ) :
    d !![a, 0; 0, c] = a * c := by
  Hint "Idea: d(diag(a, c)) = a · d(diag(1, c)) = a · c · d(I) = ac, using condition (3) twice and then (4)."
  Hint (hidden := true) "`have h1 := hd.scale_eq 1 !![1, 0; 0, c] 1 c (by entrywise <;> simp)`
  gives `d !![1, 0; 0, c] = c * d 1`."
  have h1 := hd.scale_eq 1 !![1, 0; 0, c] 1 c (by entrywise <;> simp)
  Hint (hidden := true) "Now scale row `0` of `!![1, 0; 0, c]` by `a`:
  `have h2 := hd.scale_eq !![1, 0; 0, c] !![a, 0; 0, c] 0 a (by entrywise <;> simp)`."
  have h2 := hd.scale_eq !![1, 0; 0, c] !![a, 0; 0, c] 0 a (by entrywise <;> simp)
  Hint (hidden := true) "`rw [h2, h1, hd.one, mul_one]`."
  rw [h2, h1, hd.one, mul_one]

end LinearAlgebraGame

Conclusion "For $n \\times n$ the same argument gives $d(\\mathrm{diag}(a_1,\\dots,a_n)) = a_1\\cdots a_n$."

NewTheorem LinearAlgebraGame.DetAxioms.scale_eq
TheoremTab "Det"
