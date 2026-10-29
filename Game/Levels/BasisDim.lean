import Game.Levels.BasisDim.L01_BasisUnique
import Game.Levels.BasisDim.L02_BasisIff
import Game.Levels.BasisDim.L03_P2Standard
import Game.Levels.BasisDim.L04_P2Basis
import Game.Levels.BasisDim.L05_Sym2
import Game.Levels.BasisDim.L06_Sym3
import Game.Levels.BasisDim.L07_ColSpace
import Game.Levels.BasisDim.L08_Exchange
import Game.Levels.BasisDim.L09_RankZero
import Game.Levels.BasisDim.L10_RankOne
import Game.Levels.BasisDim.L11_Augment
import Game.Levels.BasisDim.L12_Solvable
import Game.Levels.BasisDim.L13_DimMono
import Game.Levels.BasisDim.L14_NestedEq
import Game.Levels.BasisDim.L15_FunDim

World "BasisDim"
Title "Basis & Dimension"

Introduction "
Hefferon Two.III. A *basis* is an independent spanning sequence; every vector has unique
coordinates in it, and all bases have the same size — the *dimension* (the exchange lemma
is why). You will find bases, compare dimensions of nested subspaces, and prove when a linear
system is solvable in terms of rank.

**Typing:** `ᵀ` is `\\^T`, `⊥` is `\\bot`, `⊤` is `\\top`.
"
