import Mathlib

/-! `rowop h : new_row := e` — one Gaussian row operation on a system held as hypotheses.

`e` combines hypotheses exactly as in `linear_combination`, so
`rowop h₂ : y = 2 := h₂ - h₁` is Hefferon's −ρ₁ + ρ₂. The player writes the new row
themselves (the arithmetic of elimination stays their job); Lean checks that it really
follows from `e`, and the new row replaces `h₂` in the context. -/

namespace LinearAlgebraGame

syntax (name := rowop) "rowop " ident " : " term " := " term : tactic

macro_rules
  | `(tactic| rowop $h:ident : $t:term := $e:term) =>
    `(tactic| have $h : $t := by linear_combination ($e:term))

end LinearAlgebraGame
