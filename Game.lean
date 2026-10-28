import Game.Levels.LeanBasics
import Game.Levels.RowOps
import Game.Levels.DotProduct
import Game.Levels.Echelon
import Game.Levels.Axioms
import Game.Levels.Subspaces
import Game.Levels.Independence
import Game.Levels.BasisDim
import Game.Levels.Dimension
import Game.Levels.Isomorphisms
import Game.Levels.Homomorphisms
import Game.Levels.MatrixOfMap
import Game.Levels.MatrixAlgebra
import Game.Levels.ChangeOfBasis
import Game.Levels.Projection
import Game.Levels.Determinant
import Game.Levels.Volume
import Game.Levels.Eigen
import Game.Levels.Diagonalisation
import Game.Levels.Puzzles
import Game.Levels.FromScratch

-- Here's what we'll put on the title screen
Title "Echelon"
Introduction
"
**Echelon** is Oxford's first-year Linear Algebra course (MT2026, after Hefferon) as a game.
Every problem-sheet question is a level. Solve them in Lean, then export your own proofs
for your tutorial.
"

Info "
Based on Jim Hefferon's *Linear Algebra* (4th ed.) and the MT2026 problem sheets.
Built on lean4game and Mathlib.
"

/-! Information to be displayed on the servers landing page. -/
Languages "en"
CaptionShort "Hefferon in Lean"
CaptionLong "The Oxford first-year Linear Algebra course, as a game: every problem-sheet question is a level."
-- Prerequisites "" -- add this if your game depends on other games
-- CoverImage "images/cover.png"

/-! Build the game. Show's warnings if it found a problem with your game. -/
-- Core path, in lecture order.
Dependency LeanBasics → RowOps
Dependency RowOps → DotProduct
Dependency DotProduct → Echelon
Dependency Echelon → Axioms
Dependency Axioms → Subspaces
Dependency Subspaces → Independence
Dependency Independence → BasisDim
Dependency BasisDim → Dimension
Dependency Dimension → Isomorphisms
Dependency Isomorphisms → Homomorphisms
Dependency Homomorphisms → MatrixOfMap
Dependency MatrixOfMap → MatrixAlgebra
Dependency MatrixAlgebra → ChangeOfBasis
Dependency ChangeOfBasis → Projection
Dependency Projection → Determinant
Dependency Determinant → Volume
Dependency Volume → Eigen
Dependency Eigen → Diagonalisation
-- Optional side worlds.
Dependency Echelon → Puzzles
Dependency Independence → FromScratch

MakeGame
