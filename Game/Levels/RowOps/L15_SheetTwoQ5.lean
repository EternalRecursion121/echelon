import Game.Levels.RowOps.L14_SheetTwoQ3Special

World "RowOps"
Level 15
Title "Rational systems stay rational"

-- @sheet 2 Q5
/-! @answer
(a) Gauss's method only adds, subtracts, multiplies and divides entries of the augmented
matrix: every multiplier is a ratio of two (rational) entries, and a row operation
$k\rho_i + \rho_j$ with rational $k$ turns rational rows into rational rows (the fact
checked in Lean). So the echelon form is rational. If $S$ has a solution, the echelon form has
no row $0 = c$ with $c \ne 0$; setting every free variable to $0$ and back-substituting
uses only rational arithmetic, giving an all-rational solution.
(b) If $S$ has infinitely many solutions, the echelon form has at least one free variable.
Giving it any rational value (and the other free variables $0$) and back-substituting gives
a rational solution, and different values give different solutions: infinitely many
all-rational solutions.
-/
Introduction "
**Problem Sheet 2, Question 5.** Suppose a linear system $S$ has only rational coefficients
and constants. Sketch arguments for: (a) if $S$ has a solution, it has an all-rational
solution; (b) if $S$ has infinitely many solutions, it has infinitely many all-rational
solutions.

This is an **explain level**. Lean proves the formal core: the row operation
$k\\rho_1 + \\rho_2$ with a rational multiplier $k$ turns rational rows into a rational row
(rescaling is the case $\\rho_2 = \\vec 0$; swapping clearly keeps rows rational). So Gauss's
method never leaves $\\mathbb Q$.

Inside your proof also write your sketch of (a) and (b) as a comment block starting
`-- Explain:`.

**How to write an explanation** (this is the first explain level; later ones work the same
way). In Lean, `--` starts a *comment*: Lean ignores the rest of the line. Switch to
**Editor mode** (toggle at the top) and add, anywhere inside the proof (e.g. as the first
lines), a block like
```
-- Explain: (a) Every multiplier in Gauss's method is …
-- (b) …
```
Each line starts with `--`; the block starts with `-- Explain:` and ends at the first line
that is not a comment. The hand-in export copies it into your answer for this question.
(Typewriter mode takes one line at a time, so write the block in Editor mode.)
"

namespace LinearAlgebraGame

/-- If $k$ and the entries of rows $r, s$ are rational, so are the entries of $k r + s$. -/
Statement {n : ℕ} (k : ℝ) (r s : Fin n → ℝ) (hk : IsRat k) (hr : ∀ j, IsRat (r j))
    (hs : ∀ j, IsRat (s j)) : ∀ j, IsRat ((k • r + s) j) := by
  Hint "Fix a column `j`. `IsRat x` means `∃ q : ℚ, (q : ℝ) = x`: unpack the hypotheses."
  intro j
  obtain ⟨a, ha⟩ := hk
  obtain ⟨b, hb⟩ := hr j
  obtain ⟨c, hc⟩ := hs j
  Hint (hidden := true) "Which rational is $k r_j + s_j$? `use a * b + c`."
  use a * b + c
  Hint (hidden := true) "`norm_num` pushes the cast inside; then `rw [ha, hb, hc]`."
  norm_num
  Hint (hidden := true) "Model explanation: (a) every multiplier in Gauss's method is a ratio of
  rational entries, so by this level every row stays rational; with free variables set to 0,
  back-substitution only divides rationals by nonzero rationals, giving a rational solution.
  (b) infinitely many solutions means a free variable; each rational value of it gives a
  different rational solution."
  rw [ha, hb, hc]

end LinearAlgebraGame

Conclusion "Row operations with rational multipliers never leave $\\mathbb Q$ — the heart of both (a) and (b)."

NewDefinition LinearAlgebraGame.IsRat

DisabledTactic linarith nlinarith
