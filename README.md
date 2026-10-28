# Echelon

Oxford's first-year Linear Algebra course (MT2026, after Hefferon's *Linear Algebra*) as a
[lean4game](https://github.com/leanprover-community/lean4game). Every problem-sheet
question is a level; you prove it in Lean, then export your own proofs for your tutorial.

## Play

Once imported: <https://adam.math.hhu.de/#/g/eternalrecursion121/echelon>

## Export your proofs for a tutorial

1. In the game menu, download your progress (a `.json` file).
2. `python3 scripts/export_sheet.py N --hand-in --progress <file>.json --pdf --name "Your Name"`

This writes `exports/sheetN-hand-in.md` and `.pdf`: each question, your `-- Explain:` text,
your Lean proof, and how many hidden hints you opened. No model answers are included.

## Build locally

```
lake update && lake exe cache get && lake build
```

Shared infrastructure lives in `Game/Lib/`: `VectorSpaceAxioms` (Hefferon's conditions as a
predicate), `Poly n` (𝒫ₙ as coefficient vectors), `charpolyH` (Hefferon's sign convention)
and the `rowop` tactic (`rowop h₂ : y = 2 := h₂ - h₁` — one Gaussian row operation).

**Spoiler warning:** level files contain sample proofs, as the engine requires.
