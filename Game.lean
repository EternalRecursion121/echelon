import Game.Levels.LeanBasics
import Game.Levels.RowOps
import Game.Levels.DotProduct
import Game.Levels.Echelon
import Game.Levels.Puzzles
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
import Game.Levels.FromScratch

-- Here's what we'll put on the title screen
Title "Echelon"
Introduction
"
**Echelon** is Oxford's first-year Linear Algebra course (MT2026, after Hefferon) as a game.
Every problem-sheet question is a level. Solve them in Lean, then hand in your own proofs
for your tutorial.

New to Lean? Start with **Lean Basics** (about an hour). Doing a particular sheet? *Game Info*
(in the menu) has a sheet → level index, and explains how to hand in. Levels normally open
in order; to jump straight to this week's sheet, set the **Rules** slider on the world map to
*relaxed* (every level opens; tactics you haven't unlocked yet give a warning instead of an
error).

**Hand-in in brief:** your progress lives in this browser — download it regularly (menu →
download progress). The export turns it into your answers, and records how many *hidden* hints
you opened for each question.
"

Info "
Based on Jim Hefferon's *Linear Algebra* (4th ed.) and the MT2026 problem sheets.
Built on lean4game and Mathlib.

## Controls

- **Retry** (on any step you have run): undo that step and everything after it.
- **Start a level over:** Retry on the first step, or menu → *Clear Progress* → *Delete this Level*.
- **Editor mode** (toggle at the top): edit the whole proof as text.
- **Save your work:** menu → download progress (a `.json` file; progress otherwise lives only
  in this browser). The same file feeds the hand-in export.
- **Inventory** (right panel): tabs for Tactics, Theorems and Definitions you have unlocked;
  click an item for its documentation.

## Handing in

**Jumping to a sheet:** the world map follows the lectures, so a sheet's questions can sit
behind other levels. Set the **Rules** slider (left of the world map) to *relaxed* to open
every level directly, and use the sheet → level index below to find each question.

1. In the game: menu → download progress (a `.json` file).
2. Get the game's repository (https://github.com/EternalRecursion121/echelon; see its README)
   and run, for sheet `N`:
   `python3 scripts/export_sheet.py N --hand-in --progress <your-file>.json --pdf --name \"Your Name\"`
3. Hand in the PDF it writes (`exports/sheetN-hand-in.pdf`): for each question, the sheet's
   wording, your `-- Explain:` text (every block, printed as plain text; `$…$` stays maths),
   your Lean proof, and **on how many proof rows you opened hidden hints** (visible hints
   are not counted). Unsolved questions are marked. Questions the sheet does not split into
   lettered parts but the game does are shown as \"(part 1 of 3)\" and so on.

   `--pdf` needs **pandoc** and a TeX installation with **lualatex** (the PDF also uses the
   DejaVu and STIX Two fonts, which come with TeX Live, and macOS's Menlo). On macOS:
   `brew install pandoc` and MacTeX (`brew install --cask mactex`); with the smaller BasicTeX,
   add packages as the error messages name them (`sudo tlmgr install fvextra stix2-otf dejavu`
   is a start). Without these, leave out `--pdf`: the Markdown file
   `exports/sheetN-hand-in.md` is always written and can be handed in or printed from any
   Markdown viewer.

**Explain levels** ask for a written argument as well: in Editor mode, add comment lines
inside your proof starting with `-- Explain:` (`--` starts a comment; continue on further
`--` lines). Row Ops level 15 walks you through it.

## Typing symbols

Type the code, then a space. Hover over a symbol in the editor to see its code.

| Symbol | Type | Meaning |
|---|---|---|
| `⟨ ⟩` | `\\<` `\\>` | anonymous constructor: `⟨hx, hy⟩` |
| `·` | `\\.` | bullet: start the proof of one goal |
| `←` `→` `↔` | `\\l` `\\to` `\\iff` | rewrite backwards, implies, iff |
| `∧` `∨` `¬` | `\\and` `\\or` `\\not` | and, or, not |
| `∀` `∃` | `\\all` `\\ex` | for all, there exists |
| `≠` `≤` `≥` | `\\ne` `\\le` `\\ge` | |
| `ℝ` `ℚ` `ℤ` `ℕ` | `\\R` `\\Q` `\\Z` `\\N` | number systems |
| `•` | `\\smul` | scalar multiplication `r • v` |
| `⬝ᵥ` | `\\tr` then `\\_v` | dot product `u ⬝ᵥ v` |
| `*ᵥ` | `*` then `\\_v` | matrix times vector `A *ᵥ v` |
| `ᵀ` | `\\^T` | transpose `Aᵀ` |
| `⁻¹` | `\\inv` | inverse `A⁻¹` |
| `∑` | `\\sum` | sum |
| `∈` `∉` `⊆` | `\\in` `\\notin` `\\sub` | element of, not an element of, subset |
| `⊓` `⊔` `⊥` `⊤` | `\\inf` `\\sup` `\\bot` `\\top` | intersection, sum, zero subspace, whole space |
| `∘ₗ` `→ₗ` `≃ₗ` | `\\circ\\_l` `\\to\\_l` `\\equiv\\_l` | composition, linear map, linear isomorphism |
| `×` | `\\times` | product |
| `₀ ₁ ₂` | `\\0` `\\1` `\\2` | subscripts |

## Sheet → level index

Where each problem-sheet question lives (world and level number). Levels without a sheet
question are warm-ups and lecture results.

**Sheet 1.** Q1: Row Ops 2 · Q2: Row Ops 6 · Q3a: Row Ops 4 · Q3b: Row Ops 3 · Q3c: Row Ops 5 · Q4: Echelon 9 · Q5: Dot Product 6 · Q6: Dot Product 5 · Q7: Dot Product 3 · Q8: Dot Product 4 · Q9a: Row Ops 7 · Q9b: Row Ops 8 · Q10: Echelon 5 · Q11: Echelon 6 · Q12: Echelon 7 · Q13: Puzzles 1

**Sheet 2.** Q1a-c: Row Ops 10 · Q1d-e: Row Ops 11 · Q1f-g: Row Ops 12 · Q2: Echelon 8 · Q3: Row Ops 13 · Q3: Row Ops 14 · Q4: Echelon 14 · Q5: Row Ops 15 · Q6: Dot Product 9 · Q7: Dot Product 2 · Q8: Echelon 10 · Q8: Echelon 12 · Q8: Echelon 13 · Q9a: Echelon 3 · Q9b-c: Echelon 4 · Q10: Dimension & Rank 15

**Sheet 3.** Q1: The Ten Conditions 9 · Q2: The Ten Conditions 10 · Q3a: The Ten Conditions 4 · Q3b: The Ten Conditions 5 · Q3c: The Ten Conditions 6 · Q3d: The Ten Conditions 7 · Q4a: Independence 3 · Q4b: Independence 4 · Q5a: Independence 5 · Q5b: Independence 6 · Q6: Independence 7 · Q7: Basis & Dimension 3 · Q7: Basis & Dimension 4 · Q8a: Basis & Dimension 5 · Q8b: Basis & Dimension 6 · Q9: Basis & Dimension 9 · Q9: Basis & Dimension 10 · Q10: Basis & Dimension 7 · Q11: Basis & Dimension 12

**Sheet 4.** Q1: The Ten Conditions 11 · Q2: Subspaces 4 · Q3: The Ten Conditions 2 · Q4: Subspaces 3 · Q5a: Subspaces 6 · Q5b: Subspaces 9 · Q5c: Subspaces 7 · Q6a: Dimension & Rank 1 · Q6b: Dimension & Rank 2 · Q6c: Dimension & Rank 3 · Q7: Basis & Dimension 15 · Q8: Independence 14 · Q9: Dimension & Rank 13 · Q10a: Basis & Dimension 13 · Q10b: Basis & Dimension 14 · Q10c: Dimension & Rank 4 · Q11: Dimension & Rank 7 · Q12: Puzzles 3

**Sheet 5.** Q1: Dimension & Rank 8 · Q2: Homomorphisms 2 · Q3a: Homomorphisms 5 · Q3b: Homomorphisms 6 · Q4: Matrix of a Map 2 · Q5a: Matrix of a Map 3 · Q5b: Matrix of a Map 4 · Q6: Puzzles 4

**Sheet 6.** Q1a(i): Dimension & Rank 9 · Q1a(ii): Dimension & Rank 10 · Q1b: Dimension & Rank 11 · Q1c: Dimension & Rank 12 · Q1d: Dimension & Rank 14 · Q2a: Isomorphisms 6 · Q2b: Isomorphisms 7 · Q3: Isomorphisms 4 · Q4a: Homomorphisms 11 · Q4b: Homomorphisms 12 · Q5: Homomorphisms 13

**Sheet 7.** Q1: Matrix of a Map 5 · Q2: Matrix of a Map 6 · Q3: Matrix of a Map 9 · Q4: Matrix Algebra 1 · Q5: Matrix Algebra 6 · Q6: Matrix Algebra 5 · Q7a: Matrix Algebra 2 · Q7b: Matrix Algebra 3 · Q7c: Matrix Algebra 7 · Q7d: Matrix Algebra 8 · Q8: Change of Basis 2 · Q9: Projection 2

**Sheet 8.** Q1a: Matrix of a Map 10 · Q1b: Matrix of a Map 11 · Q2a: Matrix of a Map 12 · Q2b: Matrix of a Map 13 · Q2c: Matrix of a Map 14 · Q3: Homomorphisms 14 · Q4: Matrix Algebra 9 · Q5: Change of Basis 3 · Q6 (part 1 of 2): Projection 6 · Q6 (part 2 of 2): Projection 7 · Q7: Determinant 9

**Sheet 9.** Q1: Determinant 15 · Q2: Volume 3 · Q3: Determinant 14 · Q4: Determinant 13 · Q5: Eigen 2 · Q6: Eigen 4 · Q7 (part 1 of 3): Eigen 7 · Q7 (part 2 of 3): Eigen 8 · Q7 (part 3 of 3): Eigen 9 · Q8 (part 1 of 2): Eigen 11 · Q8 (part 2 of 2): Eigen 12

**Sheet 10.** Q1a: Volume 4 · Q1b: Volume 5 · Q1c: Volume 6 · Q1d: Volume 7 · Q2 (part 1 of 3): Diagonalisation 4 · Q2 (part 2 of 3): Diagonalisation 5 · Q2 (part 3 of 3): Diagonalisation 6 · Q3: Diagonalisation 7 · Q4: Eigen 15 · Q5: Diagonalisation 8 · Q6 (part 1 of 2): Eigen 13 · Q6 (part 2 of 2): Eigen 14 · Q7: Diagonalisation 12 · Q8a: Diagonalisation 9 · Q8b: Diagonalisation 10 · Q8c: Diagonalisation 11
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
