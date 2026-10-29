import Game.Levels.Determinant.L01_EqualRows
import Game.Levels.Determinant.L02_ZeroRow
import Game.Levels.Determinant.L03_Diagonal
import Game.Levels.Determinant.L04_Triangular
import Game.Levels.Determinant.L05_Uniqueness
import Game.Levels.Determinant.L06_MathlibDet
import Game.Levels.Determinant.L07_TwoByTwo
import Game.Levels.Determinant.L08_ThreeByThree
import Game.Levels.Determinant.L09_Vandermonde
import Game.Levels.Determinant.L10_EvalDet
import Game.Levels.Determinant.L11_Columns
import Game.Levels.Determinant.L12_AdjOffDiagonal
import Game.Levels.Determinant.L13_AdjDiagonal
import Game.Levels.Determinant.L14_IntegerSolution
import Game.Levels.Determinant.L15_Inversions

World "Determinant"
Title "Determinant"

Introduction "
Hefferon Four.I. The determinant is *defined* by four conditions; you derive what they
force (for $2\\times2$ matrices: everything — the value is unique), check that Mathlib's
determinant satisfies them, and then compute — first by hand,
then with a power tool.

**Typing:** `ℤ` is `\\Z`.
"
