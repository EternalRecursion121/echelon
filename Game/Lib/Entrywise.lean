import Mathlib

/-! `entrywise` — prove an equation between concrete vectors or matrices one entry at a time.

It is `ext` followed by `fin_cases` on every index, then a clean-up so each goal reads
`(A *ᵥ v) 0 = ![3, 7] 0` instead of Lean's raw `((fun i => i) ⟨0, ⋯⟩)` form. -/

namespace LinearAlgebraGame

macro "entrywise" : tactic =>
  `(tactic| first
    | (ext i j
       fin_cases i <;> fin_cases j <;>
         try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk])
    | (ext i
       fin_cases i <;>
         try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk]))

end LinearAlgebraGame
