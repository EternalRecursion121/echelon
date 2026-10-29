import Game.Levels.Volume.L03_ImageArea

World "Volume"
Level 4
Title "Triangles from the origin"

-- @sheet 10 Q1a
/-! @answer
Use *signed* areas, positive when the vertices are listed anticlockwise. In the picture,
$\triangle OAB$ is the large triangle; adding $\triangle OBC$ and $\triangle OCA$ (both
traversed clockwise, so negative) removes exactly the part of $\triangle OAB$ outside
$\triangle ABC$. In general the three signed triangles from any point $O$ add up to the signed
area of $\triangle ABC$, whether $O$ is inside or outside: the formula does not depend on
where $O$ is.
-/
Introduction "
**Problem Sheet 10, Question 1(a).** Points $A = (x_1,y_1)$, $B = (x_2, y_2)$, $C = (x_3,y_3)$
and the origin $O$ are as in the sheet's picture. Say briefly why one might say
$\\triangle ABC = \\triangle OAB + \\triangle OBC + \\triangle OCA$.

*Explain level.* The key is to use **signed** areas: `triArea P Q R` is
$\\tfrac12\\det(Q-P,\\ R-P)$, positive when $P, Q, R$ go anticlockwise. Lean proves the formal
core: for *any* point $O$ the three signed triangles add up to $\\triangle ABC$. Write your
explanation of the picture in a comment block starting `-- Explain:` inside your proof.

New: `unfold f` replaces a definition `f` by its body everywhere in the goal.
"

namespace LinearAlgebraGame

/-- For any point $O$, the signed areas satisfy $\triangle ABC = \triangle OAB + \triangle OBC + \triangle OCA$. -/
Statement (O A B C : Fin 2 → ℝ) :
    triArea A B C = triArea O A B + triArea O B C + triArea O C A := by
  Hint "Unfold the definition and expand the four $2\\times2$ determinants; then it is algebra."
  Hint (hidden := true) "`unfold triArea`, `simp only [Matrix.det_fin_two_of]`, `ring`."
  unfold triArea
  simp only [Matrix.det_fin_two_of]
  Hint (hidden := true) "Model explanation: with signed areas, the triangles OBC and OCA in
  the picture are traversed clockwise, so they count negatively and cut away exactly the
  part of OAB outside ABC. The identity holds for every position of O."
  ring

end LinearAlgebraGame

Conclusion "The identity holds wherever $O$ is — signs take care of the overlaps."

NewDefinition LinearAlgebraGame.triArea
TheoremTab "Det"
NewTactic unfold
