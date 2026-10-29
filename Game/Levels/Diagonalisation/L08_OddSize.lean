import Game.Levels.Diagonalisation.L07_WellDefined

World "Diagonalisation"
Level 8
Title "Odd size"

-- @sheet 10 Q5
/-! @answer
$|T - xI|$ is a real polynomial of degree $n$, which is odd. A real polynomial of odd degree
has a real root (it tends to $+\infty$ at one end and $-\infty$ at the other, so by the
intermediate value theorem it crosses $0$). So there is a real eigenvalue $\lambda$.
**Yes, there is also a real eigenvector:** $|T - \lambda I| = 0$ means the real matrix
$T - \lambda I$ is singular, so Gauss's method over $\mathbb R$ finds a nonzero real
$\vec v$ with $(T - \lambda I)\vec v = \vec 0$, i.e. $T\vec v = \lambda\vec v$.
(For even $n$ this fails: rotation by $90^\circ$ has no real eigenvalue.)
-/
Introduction "
**Problem Sheet 10, Question 5.** Show that a square matrix with real entries and an odd
number of rows has at least one real eigenvalue. Does it also have a real eigenvector?

The fact that an odd-degree real polynomial has a real root is analysis (intermediate
value theorem), not linear algebra; it is granted as the hypothesis `hIVT`. Its degree:
`charpolyH_natDegree T : (charpolyH T).natDegree = n`.

**Prove:** there is a real $\\lambda$ that is a root of $|T - xI|$ **and** has a real
eigenvector $\\vec v \\ne \\vec 0$ with $T\\vec v = \\lambda\\vec v$.
"

namespace LinearAlgebraGame

open Matrix Polynomial in
/-- An $n\times n$ real matrix with $n$ odd has a real eigenvalue, which comes with a real eigenvector. -/
Statement (hIVT : ∀ p : ℝ[X], Odd p.natDegree → ∃ x : ℝ, p.eval x = 0)
    {n : ℕ} (hn : Odd n) (T : Matrix (Fin n) (Fin n) ℝ) :
    ∃ μ : ℝ, (charpolyH T).eval μ = 0 ∧ ∃ v : Fin n → ℝ, v ≠ 0 ∧ T *ᵥ v = μ • v := by
  Hint "Get the root from `hIVT`. Then a root of $|T - xI|$ is an eigenvalue — with a real
  eigenvector, by your earlier level."
  Hint (hidden := true) "`obtain ⟨μ, hμ⟩ := hIVT (charpolyH T) (by rw [charpolyH_natDegree]; exact hn)`."
  obtain ⟨μ, hμ⟩ := hIVT (charpolyH T) (by rw [charpolyH_natDegree]; exact hn)
  use μ
  constructor
  · exact hμ
  · Hint (hidden := true) "`rw [← IsEigenvalue, isEigenvalue_iff_det, ← charpolyH_eval]`."
    rw [← IsEigenvalue, isEigenvalue_iff_det, ← charpolyH_eval]
    exact hμ

end LinearAlgebraGame

Conclusion "**Yes**: over $\\mathbb R$, a real eigenvalue always comes with a real eigenvector, because Gauss's method on a real singular matrix stays real."

NewTheorem LinearAlgebraGame.charpolyH_natDegree
TheoremTab "Eigen"
