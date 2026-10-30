import Game.Levels.LeanBasics.L11_ForAll

World "LeanBasics"
Level 12
Title "Feeding in a proof"

Introduction "
A \"for all\" can also ask for a *proof*. Here
`h : ∀ a b : ℝ, a < b → ∃ c, f c = a + b` wants, in order:
1. a number `a`,
2. a number `b`,
3. a proof that `a < b`.

You feed all three with spaces between them, like a function. For a short proof you can write
it in place, in brackets, as `(by norm_num)`. For example, with the numbers $5$ and $7$:

`have h57 := h 5 7 (by norm_num)`

gives `h57 : ∃ c, f c = 5 + 7`. Here `(by norm_num)` is the proof of `5 < 7`.

Why the proof? `h` only promises a `c` *when* `a < b`. Feeding just the numbers, `h 5 7`, leaves
the condition still to meet: `5 < 7 → ∃ c, f c = 5 + 7`. Lean never takes even `5 < 7` on trust,
so `(by norm_num)` is the evidence that meets it.

That result is an \"exists\". Take it apart with `obtain`, just as you did with an \"and\":
`obtain ⟨c, hc⟩ := h57` gives you the number `c` and the fact `hc : f c = 5 + 7`.

(Once this feels familiar, you can do both steps at once:
`obtain ⟨c, hc⟩ := h 5 7 (by norm_num)`. Everything to the right of `:=` is the fact being
taken apart.)
"

/-- If between any two reals $a < b$ there is some $c$ with $f(c) = a + b$, then some $c$
has $f(c) = 3$. -/
Statement (f : ℝ → ℝ) (h : ∀ a b : ℝ, a < b → ∃ c : ℝ, f c = a + b) : ∃ c : ℝ, f c = 3 := by
  Hint "Which two numbers add up to $3$, with the first smaller than the second? Feed `{h}`
  those two numbers and a proof that the first is smaller, and keep the result with `have`."
  Hint (hidden := true) "$3 = 1 + 2$ and $1 < 2$: `have h12 := {h} 1 2 (by norm_num)`"
  have h12 := h 1 2 (by norm_num)
  Hint "`{h12}` says some number works. Take it apart with `obtain`."
  Hint (hidden := true) "`obtain ⟨c, hc⟩ := {h12}`"
  obtain ⟨c, hc⟩ := h12
  Hint "Now `{c}` is the number you need."
  Hint (hidden := true) "`use {c}`, then `rw [{hc}]` and `norm_num`."
  use c
  rw [hc]
  norm_num

Conclusion "Applying a \"for all\" to the objects you care about is how you *use* a general
fact. You will do it constantly: in Row Ops you will feed a claim about all matrices your
own counterexample."

