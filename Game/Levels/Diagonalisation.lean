import Game.Levels.Diagonalisation.L01_Nilpotent
import Game.Levels.Diagonalisation.L02_EigenColumns
import Game.Levels.Diagonalisation.L03_DistinctEigenvalues
import Game.Levels.Diagonalisation.L04_ScalarMultiple
import Game.Levels.Diagonalisation.L05_Sum
import Game.Levels.Diagonalisation.L06_Product
import Game.Levels.Diagonalisation.L07_WellDefined
import Game.Levels.Diagonalisation.L08_OddSize
import Game.Levels.Diagonalisation.L09_LeadingCoeff
import Game.Levels.Diagonalisation.L10_Factored
import Game.Levels.Diagonalisation.L11_DetProduct
import Game.Levels.Diagonalisation.L12_GeoAlg

World "Diagonalisation"
Title "Diagonalisation"

Introduction "
Hefferon Five.II.2–3. Which matrices are similar to diagonal ones? Exactly those with a
basis of eigenvectors (Lemma 2.4) — for instance every matrix with distinct eigenvalues
(Corollary 3.19, which you prove for $2\\times2$). Then the characteristic polynomial of a
*transformation*: it is well defined, its leading coefficient, its value at $0$, and the
boss: geometric multiplicity $\\le$ algebraic multiplicity.
"
