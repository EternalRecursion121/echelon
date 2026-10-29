import Game.Levels.ChangeOfBasis.L01_ChangeOfBasisMatrix

World "ChangeOfBasis"
Level 2
Title "Find B and D from H"

-- @sheet 7 Q8
/-! @answer
"$H$ changes bases from $B$ to $\mathcal E_2$" means $H = \mathrm{Rep}_{B,\mathcal E_2}(\mathrm{id})$,
whose columns are the vectors of $B$: **$B = \langle (2,5), (1,3)\rangle$**.
"$H$ changes bases from $\mathcal E_2$ to $D$" means $H = \mathrm{Rep}_{\mathcal E_2,D}(\mathrm{id})$,
i.e. $\vec e_j = h_{1j}\vec\delta_1 + h_{2j}\vec\delta_2$; so $H^{-1} = \mathrm{Rep}_{D,\mathcal E_2}(\mathrm{id})$
has the vectors of $D$ as columns. $H^{-1} = \begin{pmatrix}3&-1\\-5&2\end{pmatrix}$ (as $\det H = 1$),
so **$D = \langle (3,-5), (-1,2)\rangle$**. Check: $2(3,-5) + 5(-1,2) = (1,0)$ and
$1(3,-5) + 3(-1,2) = (0,1)$. Both are bases since $H$ is nonsingular.
-/
Introduction "
**Problem Sheet 7, Question 8.** Let $H = \\begin{pmatrix}2&1\\\\5&3\\end{pmatrix}$. Find bases
$B, D$ for $\\mathbb R^2$ such that $H$ changes bases from $B$ to $\\mathcal E_2$ and $H$ changes
bases from $\\mathcal E_2$ to $D$.

(Both families you find will automatically be bases, because $H$ is nonsingular; Lean only
asks for the two change-of-basis equations.)
"

namespace LinearAlgebraGame

/-- There are $B$, $D$ with $H = \mathrm{Rep}_{B,\mathcal E_2}(\mathrm{id})$ and
$H = \mathrm{Rep}_{\mathcal E_2, D}(\mathrm{id})$. -/
Statement : ∃ B D : Fin 2 → (Fin 2 → ℝ),
    IsRep B (stdBasis 2) LinearMap.id !![2, 1; 5, 3] ∧
    IsRep (stdBasis 2) D LinearMap.id !![2, 1; 5, 3] := by
  Hint "$B$ you can read off by the last level. For $D$: column $j$ says
  $\\vec e_j = h_\{1j}\\vec\\delta_1 + h_\{2j}\\vec\\delta_2$. Which matrix has the $\\vec\\delta$'s
  as columns?"
  Hint (hidden := true) "The columns of $H^\{-1}$. `use ![![2, 5], ![1, 3]], ![![3, -5], ![-1, 2]]`"
  use ![![2, 5], ![1, 3]], ![![3, -5], ![-1, 2]]
  constructor
  · rw [isRep_id_std_iff]
    intro i j
    fin_cases i <;> fin_cases j <;> simp
  · Hint (hidden := true) "`intro j`, then `fin_cases j <;> entrywise <;> simp [stdBasis]`, and
    `norm_num` for the arithmetic left over."
    intro j
    fin_cases j <;> entrywise <;> simp [stdBasis] <;> norm_num

end LinearAlgebraGame

Conclusion "
$B = \\langle (2,5), (1,3)\\rangle$ (columns of $H$) and $D = \\langle (3,-5), (-1,2)\\rangle$
(columns of $H^{-1}$).
"

TheoremTab "Change of basis"
