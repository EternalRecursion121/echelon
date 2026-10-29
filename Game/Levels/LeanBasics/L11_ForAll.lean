import Game.Levels.LeanBasics.L10_Iff

World "LeanBasics"
Level 11
Title "Using a \"for all\""

Introduction "
A hypothesis `h : ∀ x : ℝ, P x` is a machine: feed it a number and it gives you `P` for that
number. You feed it like a function, with a space: `h 3` is the fact `P 3`.

To keep the result under a name, write `have h3 := h 3` (`have` adds a new fact to your
hypotheses). Or use it directly, e.g. `rw [h 3]`.

**Typing:** `∀` is `\\all`.
"

/-- If $f(x) = 2x$ for every real $x$, then $f(3) = 6$. -/
Statement (f : ℝ → ℝ) (h : ∀ x : ℝ, f x = 2 * x) : f 3 = 6 := by
  Hint "You need the fact for $x = 3$. Feed `{h}` the number `3`."
  Hint (hidden := true) "`have h3 := {h} 3`"
  have h3 := h 3
  Hint "Now rewrite with `{h3}` and finish with the calculator."
  Hint (hidden := true) "`rw [{h3}]`, then `norm_num`."
  rw [h3]
  norm_num

Conclusion "Applying a \"for all\" to the objects you care about is how you *use* a general
fact."

NewTactic «have»
