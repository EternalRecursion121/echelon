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
your Lean proof, and on how many proof rows you opened hidden hints. No model answers are
included.

`--pdf` needs [pandoc](https://pandoc.org) and a TeX installation with `lualatex`; the PDF
header (`scripts/pdf-header.tex`) uses the DejaVu and STIX Two fonts (shipped with TeX Live)
and macOS's Menlo. On macOS: `brew install pandoc` plus MacTeX (`brew install --cask mactex`).
With the smaller BasicTeX, install what the error names (`sudo tlmgr install fvextra stix2-otf
dejavu` is a start). Without TeX, drop `--pdf`: the Markdown file is always written and can be
handed in or printed as it is.

## Build locally

```
lake update && lake exe cache get && lake build
```

Shared infrastructure lives in `Game/Lib/`: `VectorSpaceAxioms` (Hefferon's conditions as a
predicate), `Poly n` (𝒫ₙ as coefficient vectors), `charpolyH` (Hefferon's sign convention),
the `rowop` tactic (`rowop h₂ : y = 2 := h₂ - h₁` — one Gaussian row operation) and the
`entrywise` tactic (prove an equation of concrete vectors/matrices entry by entry).

**Spoiler warning:** level files contain sample proofs, as the engine requires.
