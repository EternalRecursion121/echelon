import Game.Metadata
import Game.Ch45

World "Determinant"
Level 1
Title "Two equal rows"

Introduction "
Hefferon defines the determinant *by its properties* (Definition Four.I.2.1): a function
$d$ on $n\\times n$ matrices is a determinant if

1. swapping two rows negates it: $d(\\ldots,\\rho_j,\\ldots,\\rho_i,\\ldots) = -d(\\ldots,\\rho_i,\\ldots,\\rho_j,\\ldots)$;
2. adding $k\\rho_i$ to row $j$ ($i \\ne j$) leaves it unchanged;
3. multiplying a row by $k$ multiplies it by $k$;
4. $d(I) = 1$.

In Lean this is `DetAxioms d`, with fields `hd.swap`, `hd.combo`, `hd.scale`, `hd.one`.
In this world we first derive consequences from these four conditions alone, exactly as
Lemma Four.I.2.4 does.

**Lemma.** If rows $i \\ne j$ of $M$ are equal, then $d(M) = 0$.
"

namespace LinearAlgebraGame

/-- If $d$ satisfies the determinant conditions and rows $i \ne j$ of $M$ are equal, then
$d(M) = 0$. -/
Statement det_eq_zero_of_rows_eq {n : ℕ} (d : Matrix (Fin n) (Fin n) ℝ → ℝ) (hd : DetAxioms d)
    (M : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) (hij : i ≠ j) (h : M i = M j) : d M = 0 := by
  Hint "Idea: swap the two equal rows. The matrix does not change, but condition (1) says
  the determinant changes sign. Which number equals its own negative?"
  Hint (hidden := true) "`have h1 := hd.swap {M} {i} {j} {hij}` gives
  `d (swapRows M i j) = - d M`."
  have h1 := hd.swap M i j hij
  Hint (hidden := true) "`swapRows_eq_self {M} {h}` says swapping equal rows changes nothing.
  Rewrite with it `at {h1}`."
  rw [swapRows_eq_self M h] at h1
  Hint (hidden := true) "Now `{h1} : d M = - d M`; `linarith` finishes."
  linarith

end LinearAlgebraGame

Conclusion "
This is Lemma Four.I.2.4 (1): a matrix with two equal rows has determinant zero.
"

NewDefinition LinearAlgebraGame.DetAxioms LinearAlgebraGame.swapRows
NewTheorem LinearAlgebraGame.swapRows_eq_self Ne.symm
TheoremTab "Det"
