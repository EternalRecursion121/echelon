import Game.Levels.Volume.L01_DetMul
import Game.Levels.Volume.L02_DetInv
import Game.Levels.Volume.L03_ImageArea
import Game.Levels.Volume.L04_TriangleSum
import Game.Levels.Volume.L05_Parallelogram
import Game.Levels.Volume.L06_ThreeByThreeArea
import Game.Levels.Volume.L07_Line

World "Volume"
Title "Volume"

Introduction "
Hefferon Four.II. The determinant measures how a matrix scales areas and volumes.

Read the four conditions geometrically, with $|\\det|$ as the (signed) area of the box spanned
by the rows:
* **combination** — adding a multiple of one row to another is a *shear*: the box slides
  along one edge, base and height unchanged, so the area is unchanged;
* **scaling** — stretching one edge by $k$ multiplies the area by $k$;
* **swap** — exchanging two edges keeps the box but reverses its *orientation*, hence the sign;
* **identity** — the unit square has area $1$.
"
