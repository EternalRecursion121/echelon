import Game.Levels.Determinant.L04_Triangular

World "Determinant"
Level 5
Title "Uniqueness"

Introduction "
**Lemma Four.I.2.7** says there is *at most one* function satisfying the four conditions:
Gauss's method reduces any matrix to echelon form, each step changes $d$ in a way the
conditions dictate, and on an echelon form $d$ is the product of the diagonal.

Prove it for $2\\times 2$: **every** determinant function $d$ has
$d\\begin{pmatrix} a & b \\\\ c & e\\end{pmatrix} = ae - bc$.

For a row swap there is a third helper:
`hd.swap_eq M N i j hij h : d N = - d M`, where `h : swapRows M i j = N`
(prove it with `entrywise <;> simp [swapRows]`).
"

namespace LinearAlgebraGame

/-- Every determinant function $d$ on $2\times2$ matrices satisfies
$d\begin{pmatrix} a & b \\ c & e\end{pmatrix} = ae - bc$. -/
Statement (d : Matrix (Fin 2) (Fin 2) ℝ → ℝ) (hd : DetAxioms d) (a b c e : ℝ) :
    d !![a, b; c, e] = a * e - b * c := by
  Hint "Run Gauss's method. If $a \\ne 0$, subtract $c/a$ times row $0$ from row $1$ to reach
  a triangular matrix. If $a = 0$, swap the rows first."
  Hint (hidden := true) "`by_cases ha : a = 0`."
  by_cases ha : a = 0
  · Hint (hidden := true) "Swap the rows:
    `have h := hd.swap_eq !![a, b; c, e] !![c, e; a, b] 0 1 (by simp) (by entrywise <;> simp [swapRows])`."
    have h := hd.swap_eq !![a, b; c, e] !![c, e; a, b] 0 1 (by simp)
      (by entrywise <;> simp [swapRows])
    Hint (hidden := true) "`rw [ha, det_triangular_two d hd] at h`, then `rw [ha]` and `linarith`."
    rw [ha, det_triangular_two d hd] at h
    rw [ha]
    linarith
  · Hint (hidden := true) "Clear the entry $c$:
    `have h := hd.combo_eq !![a, b; c, e] !![a, b; 0, e - b * c / a] 0 1 (-c / a) (by simp) (by …)`.
    For the matrix identity: `entrywise <;> simp <;> field_simp <;> ring`."
    have h := hd.combo_eq !![a, b; c, e] !![a, b; 0, e - b * c / a] 0 1 (-c / a) (by simp)
      (by entrywise <;> simp <;> field_simp <;> ring)
    Hint (hidden := true) "`rw [det_triangular_two d hd] at h`, `rw [← h]`, then `field_simp`."
    rw [det_triangular_two d hd] at h
    rw [← h]
    field_simp

end LinearAlgebraGame

Conclusion "
So for $2 \\times 2$ matrices there is no choice: the four conditions force $ad - bc$.
The same argument (with induction on $n$) gives uniqueness for every size. Existence is the
next level.
"

NewTheorem LinearAlgebraGame.det_triangular_two LinearAlgebraGame.DetAxioms.swap_eq
TheoremTab "Det"
