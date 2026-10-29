import Game.Metadata

World "LeanBasics"
Level 1
Title "Goals and hypotheses"

Introduction "
A Lean proof is a conversation with a *goal* (after `⊢`) and the *hypotheses* above it.
Here the hypothesis `h` says exactly what the goal says.

**Controls.** Type one step at a time and press *Execute* (or Enter).
- **Undo:** every step you have run has a **Retry** button. It removes that step and
  everything after it, so you can try again from there.
- **Start the level over:** press Retry on your first step, or use the menu:
  *Clear Progress → Delete this Level*.
- **Editor mode** (toggle at the top) shows your whole proof as editable text — handy for
  longer proofs.
- Stuck? Hints appear on the left; some are hidden until you ask for more help. (The
  hand-in export records how many hidden hints you opened — see *Game Info* in the menu.)

**Inventory.** The panel on the right lists what you have unlocked so far, in tabs:
**Tactics** (proof steps like `exact`), **Theorems** (named facts, grouped by topic) and
**Definitions**. Click any item to read what it does and how to use it. New items appear as
you clear levels.
"

/-- If $x = 3$ then $x = 3$. -/
Statement (x : ℝ) (h : x = 3) : x = 3 := by
  Hint "`exact h` closes the goal when `h` is literally the goal."
  exact h

Conclusion "Every proof in this game ends, eventually, with a step like this one."

NewTactic exact
