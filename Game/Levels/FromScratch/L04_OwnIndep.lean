import Game.Levels.FromScratch.L03_OwnSpan

World "FromScratch"
Level 4
Title "Your own independence"

Introduction "
The game's `LinIndep v` says only the trivial relation holds:
`∀ c, ∑ i, c i • v i = 0 → ∀ i, c i = 0`. Check it by hand for the standard basis
$\\vec e_1 = (1, 0)$, $\\vec e_2 = (0, 1)$ of $\\mathbb{R}^2$. (The `(n := 2)` just tells Lean
the family has two members, so goals mention `Fin 2`.)
"

namespace LinearAlgebraGame

/-- $(1,0)$ and $(0,1)$ are linearly independent. -/
Statement : LinIndep (n := 2) ![(![1, 0] : Fin 2 → ℝ), ![0, 1]] := by
  intro c h i
  Hint "The combination $c_0(1,0) + c_1(0,1) = (c_0, c_1)$. Read off each coordinate."
  Hint (hidden := true) "`have h0 := congrFun {h} 0`, `have h1 := congrFun {h} 1`,
  `norm_num [Fin.sum_univ_two] at h0 h1`, then `fin_cases {i}`."
  have h0 := congrFun h 0
  have h1 := congrFun h 1
  norm_num [Fin.sum_univ_two] at h0 h1
  fin_cases i
  · exact h0
  · exact h1

end LinearAlgebraGame

Conclusion "Every coefficient shows up alone in one coordinate, so it must vanish."

NewDefinition LinearAlgebraGame.LinIndep

DisabledTactic simp
TheoremTab "From Scratch"
