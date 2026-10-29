import Game.Levels.LeanBasics.L11_ForAll

World "LeanBasics"
Level 12
Title "Feeding in a proof"

Introduction "
A \"for all\" can also ask for a *proof*: `h : ∀ a b : ℝ, a < b → P a b` wants two numbers
and a proof that the first is smaller. Arguments are separated by spaces:
`h 1 2 proof` is the fact `P 1 2`, where `proof` shows `1 < 2`.

A short proof can be written in place, in brackets: `(by norm_num)`. So `h 1 2 (by norm_num)`
is `P 1 2`.

If the result is an \"exists\", take it apart with `obtain`, just like an \"and\":
`obtain ⟨c, hc⟩ := …` gives you the object `c` and its property `hc`.
"

/-- If between any two reals $a < b$ there is some $c$ with $f(c) = a + b$, then some $c$
has $f(c) = 3$. -/
Statement (f : ℝ → ℝ) (h : ∀ a b : ℝ, a < b → ∃ c : ℝ, f c = a + b) : ∃ c : ℝ, f c = 3 := by
  Hint "$3 = 1 + 2$ and $1 < 2$. Feed `{h}` the numbers $1$, $2$ and a proof of $1 < 2$."
  Hint (hidden := true) "`obtain ⟨c, hc⟩ := {h} 1 2 (by norm_num)`"
  obtain ⟨c, hc⟩ := h 1 2 (by norm_num)
  Hint "Now `{c}` is the number you need."
  Hint (hidden := true) "`use {c}`, then `rw [{hc}]` and `norm_num`."
  use c
  rw [hc]
  norm_num

Conclusion "Applying a \"for all\" to the objects you care about is how you *use* a general
fact. You will do it constantly: in Row Ops you will feed a claim about all matrices your
own counterexample."

