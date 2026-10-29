import Mathlib

/-! `rowop` — one Gaussian row operation on a system held as hypotheses.

* `rowop h2 := h2 - 3 * h1` — Hefferon's −3ρ₁ + ρ₂. Lean works out the new row (each side
  tidied separately, so `x` cancels and you see e.g. `h2 : -y = -2`) and it replaces `h2`.
  When both sides are linear with numeric coefficients, the row is printed in a canonical
  form — variables in the order they were introduced (`x, y, z, w`; entries `v 0, v 1, …` by
  position), coefficient first (`3 * z`), constant last — so two rows with the same variables
  always print alike. Otherwise each side is tidied with `ring_nf`.
* `rowop h2 : -y = -2 := h2 - 3 * h1` — the same, but you state the new row yourself and Lean
  checks it. Useful to check your own arithmetic or to choose a tidier form of the row.

The combination is written exactly as in `linear_combination`. -/

namespace LinearAlgebraGame

open Lean Elab Tactic Meta

syntax (name := rowop) "rowop " ident (" : " term)? " := " term : tactic

/-- The type of the first equation hypothesis named in the combination `e` (e.g. `ℝ`). -/
def rowType? (e : Term) : TacticM (Option Expr) := withMainContext do
  let lctx ← getLCtx
  let mut out : Option Expr := none
  for stx in e.raw.topDown do
    if out.isNone && stx.isIdent then
      if let some d := lctx.findFromUserName? stx.getId then
        if let some (α, _, _) := (← instantiateMVars d.type).eq? then
          out := some α
  return out


/-! ### Canonical printing of a linear row -/

/-- A linear form: coefficients of atoms (in first-seen order) and a constant. -/
structure LinForm where
  atoms : Array (Expr × ℚ) := #[]
  const : ℚ := 0

def LinForm.scale (c : ℚ) (f : LinForm) : LinForm :=
  { atoms := f.atoms.map fun (a, k) => (a, c * k), const := c * f.const }

def LinForm.add (f g : LinForm) : LinForm := Id.run do
  let mut out := f.atoms
  for (a, k) in g.atoms do
    match out.findIdx? (fun (b, _) => b == a) with
    | some i => out := out.modify i fun (b, l) => (b, l + k)
    | none => out := out.push (a, k)
  return { atoms := out, const := f.const + g.const }

/-- Read a numeric literal (`3`, `2.5`). -/
def numLit? (e : Expr) : Option ℚ :=
  match e.getAppFnArgs with
  | (``OfNat.ofNat, #[_, n, _]) => n.rawNatLit?.map (fun n => (n : ℚ))
  | (``OfScientific.ofScientific, #[_, _, m, s, ex]) => do
      let m ← m.rawNatLit?
      let ex ← ex.rawNatLit?
      let b ← match s.constName? with
        | some ``Bool.true => some true
        | some ``Bool.false => some false
        | _ => none
      if b then some ((m : ℚ) / (10 ^ ex : ℕ)) else some ((m : ℚ) * (10 ^ ex : ℕ))
  | _ => none

/-- The linear form of `e`, or `none` if `e` is not linear with numeric coefficients. -/
partial def linForm? (e : Expr) : Option LinForm :=
  if let some q := numLit? e then some { const := q } else
  match e.getAppFnArgs with
  | (``HAdd.hAdd, #[_, _, _, _, a, b]) => do return (← linForm? a).add (← linForm? b)
  | (``HSub.hSub, #[_, _, _, _, a, b]) => do return (← linForm? a).add ((← linForm? b).scale (-1))
  | (``Neg.neg, #[_, _, a]) => do return (← linForm? a).scale (-1)
  | (``HMul.hMul, #[_, _, _, _, a, b]) => do
      let fa ← linForm? a
      let fb ← linForm? b
      if fa.atoms.all (·.2 == 0) then return fb.scale fa.const
      else if fb.atoms.all (·.2 == 0) then return fa.scale fb.const
      else none
  | (``HDiv.hDiv, #[_, _, _, _, a, b]) => do
      let fb ← linForm? b
      if fb.atoms.all (·.2 == 0) && fb.const != 0 then return (← linForm? a).scale (1 / fb.const)
      else none
  | _ => some { atoms := #[(e, 1)] }

/-- Syntax for a nonnegative rational coefficient. -/
def ratSyntax (q : ℚ) : TermElabM Term := do
  let n := Syntax.mkNumLit (toString q.num.natAbs)
  if q.den == 1 then return ⟨n⟩
  else
    let d := Syntax.mkNumLit (toString q.den)
    `(($n / $d))

/-- The canonical syntax of a linear form: atoms sorted (local variables in the order they
were introduced, other atoms such as `v 0` by their printed form), coefficient first,
constant last. -/
def linFormSyntax (f : LinForm) : TacticM Term := withMainContext do
  let lctx ← getLCtx
  let atoms := f.atoms.filter (·.2 != 0)
  let mut keyed : Array ((Nat × Nat × String) × Expr × ℚ) := #[]
  for (a, k) in atoms do
    let s := toString (← ppExpr a)
    let key := match a with
      | .fvar id => match lctx.find? id with
        | some d => (0, d.index, s)
        | none => (1, 0, s)
      | _ => (1, 0, s)
    keyed := keyed.push (key, a, k)
  let sorted := keyed.qsort fun (k1, _, _) (k2, _, _) =>
    k1.1 < k2.1 || (k1.1 == k2.1 && (k1.2.1 < k2.2.1 ||
      (k1.2.1 == k2.2.1 && k1.2.2 < k2.2.2)))
  let mut acc : Option Term := none
  for (_, a, k) in sorted do
    let aStx ← PrettyPrinter.delab a
    let mag := if k < 0 then -k else k
    let c ← ratSyntax mag
    let term ← if mag == 1 then pure aStx else `($c * $aStx)
    acc ← match acc with
      | none =>
        if k < 0 then (if mag == 1 then `(-$aStx) else `(-$c * $aStx)) else pure term
      | some t => if k < 0 then `($t - $term) else `($t + $term)
  let c := f.const
  if c != 0 || acc.isNone then
    let mag := if c < 0 then -c else c
    let cs ← ratSyntax mag
    acc ← match acc with
      | none => if c < 0 then `(-$cs) else pure cs
      | some t => if c < 0 then `($t - $cs) else `($t + $cs)
  return acc.get!

elab_rules : tactic
  | `(tactic| rowop $h:ident : $t:term := $e:term) => withMainContext do
    -- elaborate the stated row at the equations' type, so `rowop h3 : 0 = 1 := …` means the
    -- real numbers 0 and 1 (bare numerals would otherwise default to ℕ)
    let t' ← match t with
      | `($a = $b) =>
        match ← rowType? e with
        | some α => do
          let αs ← PrettyPrinter.delab α
          `((($a : $αs) = $b))
        | none => pure t
      | _ => pure t
    evalTactic (← `(tactic| replace $h:ident : $t' := by linear_combination ($e:term)))
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
    -- canonical form if both sides are linear with numeric coefficients
    let canon ← withMainContext do
      let some d := (← getLCtx).findFromUserName? h.getId | return false
      let some (_, a, b) := (← instantiateMVars d.type).eq? | return false
      let (some fa, some fb) := (linForm? a, linForm? b) | return false
      let L' ← linFormSyntax fa
      let R' ← linFormSyntax fb
      try
        evalTactic (← `(tactic| rowop $h:ident : $L' = $R' := $h:ident))
        return true
      catch _ => return false
    unless canon do
      evalTactic (← `(tactic| try conv at $h:ident => lhs; ring_nf))
      evalTactic (← `(tactic| try conv at $h:ident => rhs; ring_nf))

end LinearAlgebraGame
