# Authoring conventions for Echelon

Read this fully before writing a level. Look at `Game/Levels/LeanBasics/*.lean` and
`Game/Levels/Axioms/*.lean` as worked examples, and `../lean4game/doc/` (especially
`create_game.md`, `hints.md`, `writing_exercises.md`) for the engine's commands.

## Who plays, and why it matters

A first-year Oxford CS student plays the levels on the game site and **hands in their own
proofs** for their problem sheets (their tutor accepts Lean). So:
- Every sheet question part gets a level whose statement faithfully captures what the
  sheet asks (not an easier variant). Where a reformulation is unavoidable, say so in the
  level's Introduction.
- Sample proofs must be correct and *short* (the "not cumbersome" requirement), but the
  player must not be able to skip the mathematics with automation (see Tactic policy).
- Hints must not give proofs away: the first visible hint states the *idea*; anything
  naming a tactic or lemma is `Hint (hidden := true)`.

## Files you own

- Your worlds: `Game/Levels/<WorldId>.lean` and `Game/Levels/<WorldId>/Lnn_Name.lean`.
- Your chapter file `Game/<ChapterFile>.lean` (name given in your brief): game-local
  definitions (e.g. `MatSimilar`) and granted lemmas. It starts with `import GameServer`,
  `import Mathlib`, `import Game.Lib`. Your first level of each world imports `Game.Metadata`
  and your chapter file.
- **Docs:** every `TheoremDoc` / `DefinitionDoc` lives in `Game/Doc/Theorems.lean` (imported by
  `Game.Metadata`, so a doc is visible in every level). Add one only if the name has none there
  yet — the engine keeps the *first* doc for a name, so duplicates are dead text. A bare short
  name under `open Matrix` (e.g. `mul_apply`) can resolve to an unrelated root lemma: write
  `Matrix.mul_apply` in sample proofs.

**Never edit**: `Game.lean`, `Game/Metadata.lean`, `Game/Lib/*`, `Game/Doc/Tactics.lean`,
other worlds, `scripts/`, `lakefile.lean`. If you need a tactic doc that isn't in
`Game/Doc/Tactics.lean`, list it in your final report (a missing doc is only a warning).

## Building (shared workspace, other authors build in parallel)

- Build only your own targets: `lake build Game.Levels.<WorldId>` (or a single level
  `lake build Game.Levels.<WorldId>.L03_Name`). **Never run a bare `lake build`** — it runs
  `MakeGame` across everybody's worlds. `PATH=$HOME/.elan/bin:$PATH` is needed.
- Scratch experiments: write files under
  `/private/tmp/claude-501/-Users-samuelratnam-Programming-lean-linear-algebra-game/a30dd6ce-73ca-497d-888d-0b653f875a49/scratchpad/<your-chapter>/`
  and run `lake env lean <file>` from the game directory.
- If you see a lock / file-in-use error, wait a few seconds and retry.

## Level file shape

```lean
import Game.Levels.<WorldId>.L02_Previous   -- level 1 imports Game.Metadata + Game.<ChapterFile>

World "<WorldId>"
Level 3
Title "Short title (never states a true/false answer)"

-- @sheet 4 Q5b            ← only for sheet questions; exactly this format, one per level
/-! @answer
The model tutorial answer in Markdown + LaTeX ($…$), 2–8 sentences, informal proof.
-/
Introduction "
Question text (for sheet levels, quote the sheet question in bold:
**Problem Sheet 4, Question 5(b).** …). Escape backslashes in strings: `$\\vec v$`.
"

namespace LinearAlgebraGame

/-- The claim in words, with LaTeX (no escaping needed in doc comments). -/
Statement name_if_reused_later (args) : goal := by
  Hint "Idea only."
  …
  Hint (hidden := true) "Tactic-level help."
  …

end LinearAlgebraGame

Conclusion "One or two sentences."

NewTactic …            -- tactics first used in this level
NewTheorem …           -- fully qualified names; every one needs a TheoremDoc in Game/Doc/Theorems.lean
DisabledTactic …       -- automation that would bypass this level
DisabledTheorem …      -- Mathlib lemmas that ARE this level's statement
TheoremTab "<Tab>"
```

- Keep the `World` and `Level` lines at the top: the hand-in export uses them.
- Name a `Statement` only if a later level in your chapter reuses it; named statements go in
  `namespace LinearAlgebraGame` to avoid clashes with Mathlib (e.g. `neg_unique`, `Similar`
  already exist in Mathlib).
- One level per independent question part (`Q3a`, `Q3b`, …). Tag parts as `Q3a`. A question
  whose parts are one argument may be one level tagged `Q3`.
- ≤ 16 levels per world.
- Use `Branch` for alternative proof routes with their own hints; use `(strict := true)` on a
  hint placed right after a `have`.
- In `Hint` strings `{h}` interpolates a hypothesis name, so a literal brace (e.g. LaTeX
  `a_{11}`) must be written `a_\{11}` (a LaTeX set brace `\{` is `\\\{`).
- Explain levels: put the sample `-- Explain:` comment at the top of the proof (the export
  copies it), and keep path-specific tips of decide levels out of the Introduction and the
  level's `NewTheorem`/`NewTactic` lines (unlock them a level earlier).

## Level kinds

- **Proof level**: ordinary statement.
- **Decide level** (true/false, "must…?", "is X a vector space?"): goal `(¬ P) ∨ P`; the
  player commits with `left` (false / no) or `right` (true / yes), then proves it. Say this
  convention in the Introduction. The title must not reveal the answer.
- **Witness level** ("find / solve / compute"): state the answer as the claim
  (e.g. `∃ p, ∀ x, sys x ↔ x = p`, or `A *ᵥ v = …`, or the solution set equals a stated set;
  the sheet levels use `∃ …, ∀ …, … ↔ …` rather than `∃!`) so the player
  supplies/checks it. Prefer doing the computation *in* Lean with `rowop` for systems.
  State results completely (e.g. eigenvalues are exactly 1 and 2, not just "1 is one").
- **Explain level** (the sheet asks to sketch, explain, or the question is discursive): Lean
  proves the precise formal core; the Introduction asks the player to also write their
  explanation as a comment block starting `-- Explain:` inside their proof (the export picks
  it up). Put the model explanation in a final `Hint (hidden := true)` and in `@answer`.

## Tactic policy: tight

The player chose tight. Unlock schedule (a tactic may be unlocked earlier only if it cannot
bypass the lesson):
Current schedule (from the `NewTactic` lines, world order):
- Lean Basics: exact rw norm_num use obtain intro constructor have left right rcases entrywise
  ext fin_cases (also the theorems `symm`/`trans`, so `h.symm`/`(…).symm` work everywhere).
- Row Ops: linear_combination rowop apply (linarith stays LOCKED in Row Ops);
  Dot Product: congr ring linarith show nlinarith positivity induction; Echelon: simp refine.
- Axioms: nth_rw by_contra calc by_cases (norm_num disabled there); Subspaces: rfl;
  Independence: module funext exfalso; Basis & Dimension: rintro field_simp match_scalars
  choose omega; Dimension: decide; Volume: unfold.
- `simp`/`norm_num` may be unlocked but must be `DisabledTactic` in any level they would solve
  outright.
- Chapter Four: `eval_det` only after the hand-computation levels.
- Never unlock: `exact?`, `aesop`, `decide` on non-finite goals, `tauto`.

**Bypass check (mandatory for every level):** in a scratch file, for each unlocked tactic
among `simp`, `norm_num`, `linarith`, `nlinarith`, `positivity`, `ring`, `module`,
`field_simp`, `linear_combination`, `omega`, `decide`, `eval_det`, check that it does NOT
close the level's statement on its own (try e.g. `by simp`, `by norm_num`, `by linarith`,
also `by simp [hyps…]`). If it does and that skips the point of the level, `DisabledTactic`
it (or `DisabledTheorem` the Mathlib lemma that is the statement). Also disable Mathlib
lemmas whose statement *is* the level (e.g. `smul_eq_zero` for "r•v = 0 ↔ r = 0").

## Mathematics conventions

- Scalars: ℝ by default. ℚ/ℤ only where the question is about them (S1 Q13 mod 3, S2 Q5
  rational solutions, S9 Q3 integer solutions).
- Vectors `Fin n → ℝ` with `![…]`; matrices `Matrix (Fin m) (Fin n) ℝ` with `!![…]`; dot
  product `⬝ᵥ`; `EuclideanSpace` only when norms/inner products are essential.
- Library you may use: `Game/Lib/` — `LinearAlgebraGame.VectorSpaceAxioms` (its bridge `axioms_of_module` is From Scratch level 1),
  `LinearAlgebraGame.Poly n` (𝒫ₙ as `Fin (n+1) → ℝ`, `Poly.eval`, `Poly.evalAt`, `Poly.deriv`),
  `LinearAlgebraGame.charpolyH` (+ `charpolyH_eq`), the `rowop` tactic, the `entrywise` tactic
  (concrete sizes only; for `Fin n` use `ext i`).
- **Engine quirk (`.symm`/`.trans`):** the server checks every identifier against the
  inventory; in `(term).symm` the field `symm` resolves to the root theorem `symm` (likewise
  `.trans`, and `.antisymm`, `.mt`, `.le_of_lt`, `.not_lt`, `.congr` → root theorems). `h.symm`
  on a bare local name is not affected. `symm`/`trans` are unlocked in Lean Basics level 2, so
  they are always allowed; avoid the other parenthesised projections in samples and hints (or
  unlock the root theorem first).
- Cross-chapter results: don't import other chapters' worlds (they are built in parallel).
  Use the Mathlib lemma instead, unlocked with `NewTheorem` and documented
  ("You proved a version of this in world X").
- Reference material: `../notes/*.md` (course notes), `../spoilers/problem-sheet-map.md`
  (worked answer + Lean approach + hacky flags for every sheet question — follow its
  de-hacking section), `../spoilers/pilot/*.lean` (compiled proofs of many sheet questions),
  `../plan/index.html` (`WORLDS` array: the planned level list per world),
  `../resources/problem_sheets/*.pdf` (render with `pdftoppm -r 90 -png` when signs matter —
  `pdftotext` drops minus signs).

## Definition of done for your chapter

1. Every planned level for your worlds exists (you may merge, split or reorder sensibly;
   every sheet question part assigned to you MUST have a tagged level with an `@answer`).
2. `lake build Game.Levels.<WorldId>` succeeds for each of your worlds with no errors and no
   "Missing Theorem Documentation" warnings.
3. Bypass check done for every level.
4. Final report: worlds and level counts; every sheet tag you created; any level whose
   statement deviates from the sheet and why; tactic docs you needed but were missing;
   anything you could not finish.
