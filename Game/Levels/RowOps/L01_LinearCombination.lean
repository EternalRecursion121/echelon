import Game.Metadata
import Game.Ch1

World "RowOps"
Level 1
Title "Adding equations"

Introduction "
A linear system lives in Lean as *hypotheses*: here `h₁ : x + y = 5` and `h₂ : x - y = 1`.
Gauss's method only ever does one thing to equations: add a multiple of one to another.

`linear_combination e` proves the goal when it is exactly the combination `e` of
hypotheses, e.g. `linear_combination h₁ + h₂` or `linear_combination h₂ - 3 * h₁`.

In this world `linarith` stays locked: you choose every combination yourself.
"

namespace LinearAlgebraGame

/-- If $x + y = 5$ and $x - y = 1$ then $2x = 6$. -/
Statement (x y : ℝ) (h₁ : x + y = 5) (h₂ : x - y = 1) : 2 * x = 6 := by
  Hint "Which combination of the two equations has $2x$ on the left and $6$ on the right?"
  Hint (hidden := true) "`linear_combination h₁ + h₂`"
  linear_combination h₁ + h₂

end LinearAlgebraGame

Conclusion "Lean checked that goal − (h₁ + h₂) is an algebraic identity."

DisabledTactic norm_num linarith nlinarith
NewTactic linear_combination
