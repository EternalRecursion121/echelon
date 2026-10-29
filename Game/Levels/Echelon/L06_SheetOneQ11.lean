import Game.Levels.Echelon.L05_SheetOneQ10

World "Echelon"
Level 6
Title "All reduced echelon shapes"

-- @sheet 1 Q11
/-! @answer
$2\times 3$ (with $a, b \in \mathbb R$ arbitrary):
$\begin{pmatrix}0&0&0\\0&0&0\end{pmatrix}$,
$\begin{pmatrix}1&a&b\\0&0&0\end{pmatrix}$, $\begin{pmatrix}0&1&a\\0&0&0\end{pmatrix}$,
$\begin{pmatrix}0&0&1\\0&0&0\end{pmatrix}$, $\begin{pmatrix}1&0&a\\0&1&b\end{pmatrix}$,
$\begin{pmatrix}1&a&0\\0&0&1\end{pmatrix}$, $\begin{pmatrix}0&1&0\\0&0&1\end{pmatrix}$.
$3\times 2$: $\begin{pmatrix}0&0\\0&0\\0&0\end{pmatrix}$, $\begin{pmatrix}1&a\\0&0\\0&0\end{pmatrix}$,
$\begin{pmatrix}0&1\\0&0\\0&0\end{pmatrix}$, $\begin{pmatrix}1&0\\0&1\\0&0\end{pmatrix}$.
Completeness: a reduced echelon matrix is determined by how many nonzero rows it has, which
columns hold their leading $1$s (strictly increasing), and the free entries to the right of
each leading $1$ that are not in a pivot column. For $2\times 3$: no pivots (1 way); one pivot
in column 1, 2 or 3 (3 ways); two pivots in columns $\{1,2\}, \{1,3\}, \{2,3\}$ (3 ways). For
$3\times 2$ at most two pivots: none, column 1, column 2, or both.
-/
Introduction "
**Problem Sheet 1, Question 11.** The reduced echelon forms possible for $2\\times 2$ matrices
are $\\begin{pmatrix}0&0\\\\0&0\\end{pmatrix}, \\begin{pmatrix}1&a\\\\0&0\\end{pmatrix},
\\begin{pmatrix}0&1\\\\0&0\\end{pmatrix}, \\begin{pmatrix}1&0\\\\0&1\\end{pmatrix}$. Similarly list
the reduced echelon forms possible for $2\\times 3$ and $3\\times 2$.

**Explain level.** Make your own list on paper first (count the possible positions of the
leading entries). The statement then lists the shapes, and Lean checks that every one really
is in reduced echelon form for all values of the parameters. That the list is *complete* is
your written argument: put it in a comment `-- Explain:` inside your proof.

New: `refine ⟨?_, ?_⟩` splits a conjunction into goals in one go.
"

namespace LinearAlgebraGame

open Matrix in
/-- Each listed $2\times 3$ and $3\times 2$ shape is in reduced echelon form. -/
Statement (a b : ℝ) :
    (0 : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![1, a, b; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![0, 1, a; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![0, 0, 1; 0, 0, 0] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![1, 0, a; 0, 1, b] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![1, a, 0; 0, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (!![0, 1, 0; 0, 0, 1] : Matrix (Fin 2) (Fin 3) ℝ).IsReducedRowEchelon ∧
    (0 : Matrix (Fin 3) (Fin 2) ℝ).IsReducedRowEchelon ∧
    (!![1, a; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ).IsReducedRowEchelon ∧
    (!![0, 1; 0, 0; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ).IsReducedRowEchelon ∧
    (!![1, 0; 0, 1; 0, 0] : Matrix (Fin 3) (Fin 2) ℝ).IsReducedRowEchelon := by
  Hint "Each shape is a finite check, exactly as in the previous level. Split into the eleven
  shapes and three conditions each, then run the same check everywhere."
  Hint (hidden := true) "`refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, …⟩` (eleven triples), then
  `<;> intro i₁ i₂ <;> fin_cases i₁ <;> fin_cases i₂ <;> simp [IsLeadingEntry, Fin.forall_fin_succ]`."
  Hint (hidden := true) "Model explanation of completeness: a reduced echelon matrix is fixed by its
  pivot columns (strictly increasing, one per nonzero row) and the free entries in non-pivot
  columns to the right of each pivot; for $2\\times 3$ the possible pivot columns are: none; 1; 2; 3;
  1 and 2; 1 and 3; 2 and 3. For $3\\times 2$: none; 1; 2; 1 and 2."
  refine ⟨⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩,
    ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩, ⟨?_, ?_, ?_⟩⟩ <;>
    intro i₁ i₂ <;> fin_cases i₁ <;> fin_cases i₂ <;> simp [IsLeadingEntry, Fin.forall_fin_succ]

end LinearAlgebraGame

Conclusion "Seven shapes for $2\\times 3$, four for $3\\times 2$ (with parameters $a, b$)."
NewTactic refine
