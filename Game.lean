import Game.Levels.LeanBasics
import Game.Levels.Axioms

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
Dependency LeanBasics → Axioms

MakeGame
