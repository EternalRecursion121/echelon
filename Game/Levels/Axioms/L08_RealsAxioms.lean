import Game.Levels.Axioms.L07_OneOrInfinite

World "Axioms"
Level 8
Title "The ten conditions as a checklist"

Introduction "
To ask *\"is this a vector space?\"* we need the ten conditions as something we can check —
or refute. The game's `VectorSpaceAxioms V add smul` (see the Definitions tab) says that the
set `V` with the operations `add` and `smul` satisfies Hefferon's Definition Two.I.1.1.
Closure, conditions (1) and (6), is automatic: `add` and `smul` are functions *into* `V`.

As a warm-up, check the checklist for the simplest real vector space of all: $\\mathbb{R}$
itself, with the usual $+$ and with scalar multiplication $r \\cdot x = rx$.

The zero condition says some $z$ satisfies $v + z = v$ for all $v$. The inverse condition
says: for each $v$ there is a $w$ with $v + w$ equal to *any* $z$ that behaves like a zero.
"

namespace LinearAlgebraGame

/-- $\mathbb{R}$ with its usual addition and multiplication satisfies the ten conditions. -/
Statement : VectorSpaceAxioms ℝ (· + ·) (· * ·) := by
  Hint "`constructor` splits the checklist into its eight remaining conditions."
  constructor
  · Hint "Each of these is an identity of real numbers. `intro` the variables, then `ring`."
    intro u v
    ring
  · intro u v w
    ring
  · Hint "Which real number $z$ has $v + z = v$ for every $v$?"
    use 0
    intro v
    ring
  · intro v
    Hint (hidden := true) "Take $w = -v$ with `use -{v}`."
    use -v
    intro z hz
    Hint "`{hz}` says $z$ acts like a zero. Apply it to $x = 0$ to learn that $z = 0$."
    Hint (hidden := true) "`have h0 := {hz} 0` then `linarith`."
    have h0 := hz 0
    linarith
  · intro r s v
    ring
  · intro r u v
    ring
  · intro r s v
    ring
  · intro v
    ring

end LinearAlgebraGame

Conclusion "
Every condition was an identity of real numbers. The interesting levels are the ones where
a condition *fails*.
"

NewDefinition LinearAlgebraGame.VectorSpaceAxioms
TheoremTab "Vector spaces"
