import Mathlib

/-! `rowop` — one Gaussian row operation on a system held as hypotheses.

* `rowop h2 := h2 - 3 * h1` — Hefferon's −3ρ₁ + ρ₂. Lean works out the new row (each side
  tidied separately, so `x` cancels and you see e.g. `h2 : -y = -2`) and it replaces `h2`.
* `rowop h2 : -y = -2 := h2 - 3 * h1` — the same, but you state the new row yourself and Lean
  checks it. Useful to check your own arithmetic or to choose a tidier form of the row.

The combination is written exactly as in `linear_combination`. -/

namespace LinearAlgebraGame

open Lean Elab Tactic Meta

syntax (name := rowop) "rowop " ident (" : " term)? " := " term : tactic

elab_rules : tactic
  | `(tactic| rowop $h:ident : $t:term := $e:term) => do
    evalTactic (← `(tactic| replace $h:ident : $t := by linear_combination ($e:term)))
  | `(tactic| rowop $h:ident := $e:term) => withMainContext do
    let lctx ← getLCtx
    -- the new row: substitute each equation's left (resp. right) side into the combination
    let side (left : Bool) : TacticM Term := do
      let s ← e.raw.replaceM fun stx => do
        if stx.isIdent then
          match lctx.findFromUserName? stx.getId with
          | some d =>
            match (← instantiateMVars d.type).eq? with
            | some (_, a, b) =>
              let t ← PrettyPrinter.delab (if left then a else b)
              return some (← `(($t))).raw
            | none => return none
          | none => return none
        else return none
      return ⟨s⟩
    let L ← side true
    let R ← side false
    evalTactic (← `(tactic| replace $h:ident : $L = $R := by linear_combination ($e:term)))
    evalTactic (← `(tactic| try conv at $h:ident => lhs; ring_nf))
    evalTactic (← `(tactic| try conv at $h:ident => rhs; ring_nf))

end LinearAlgebraGame
