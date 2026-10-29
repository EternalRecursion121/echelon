import Game.Levels.MatrixAlgebra.L10_InvertibleIffNonsingular

World "MatrixAlgebra"
Title "Matrix Algebra"

Introduction "
Hefferon Three.IV. Matrices form an algebra of their own: products, transposes and inverses.
This world proves the rules you will use every day, and ends with the theorem that a square
matrix is invertible exactly when it is nonsingular.

**Inverses in Lean.** Hefferon calls $H$ invertible when some $H'$ has $H'H = I = HH'$, and
that is how Sheet 7 Q6 and the boss state it. Mathlib's `H⁻¹` is defined for *every* square
matrix (it is $0$ when no inverse exists), so the levels that use `H⁻¹` (Sheet 7 Q5, Q7 and Sheet 8 Q4)
assume `hH : IsUnit H.det` — \"the determinant of $H$ is nonzero\". You will meet
determinants in a later world; here just treat `IsUnit H.det` as \"$H$ is invertible\", the
hypothesis that unlocks `Matrix.nonsing_inv_mul H hH : H⁻¹ * H = 1` and
`Matrix.mul_nonsing_inv H hH : H * H⁻¹ = 1`.
"
