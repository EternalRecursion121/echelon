import Game.Levels.RowOps.L01_LinearCombination
import Game.Levels.RowOps.L02_RowOp
import Game.Levels.RowOps.L03_SheetOneQ1
import Game.Levels.RowOps.L04_SheetOneQ3b
import Game.Levels.RowOps.L05_SheetOneQ3a
import Game.Levels.RowOps.L06_SheetOneQ3c
import Game.Levels.RowOps.L07_SheetOneQ2
import Game.Levels.RowOps.L08_SheetOneQ9a
import Game.Levels.RowOps.L09_SheetOneQ9b
import Game.Levels.RowOps.L10_SheetTwoQ1a
import Game.Levels.RowOps.L11_SheetTwoQ1e
import Game.Levels.RowOps.L12_SheetTwoQ3Generic
import Game.Levels.RowOps.L13_SheetTwoQ3One
import Game.Levels.RowOps.L14_SheetTwoQ3MinusOne
import Game.Levels.RowOps.L15_SheetTwoQ5
import Game.Levels.RowOps.L16_NeverTwo

World "RowOps"
Title "Row Ops"

Introduction "
Hefferon One.I: Gauss's method. A linear system is a list of equations; a *row operation*
replaces one equation by a combination of equations. In Lean every row operation is a
`rowop` (or `linear_combination`) step — you choose the multipliers, Lean checks the algebra.
"
