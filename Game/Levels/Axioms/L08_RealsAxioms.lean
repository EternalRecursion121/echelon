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

Conditions (4) and (5) are one field, `has_zero_neg`, worded as Hefferon does: there is a
zero vector $z$ (with $v + z = v$ for all $v$), **and** every $v$ has an inverse $w$ with
$v + w = z$. The Definitions tab lists all seven fields with their condition numbers.
"

namespace LinearAlgebraGame

/-- $\mathbb{R}$ with its usual addition and multiplication satisfies the ten conditions. -/
Statement : VectorSpaceAxioms ℝ (· + ·) (· * ·) := by
  Hint "`constructor` splits the checklist into its seven fields."
  constructor
  · Hint "Each of these is an identity of real numbers. `intro` the variables, then `ring`."
    intro u v
    ring
  · intro u v w
    ring
  · Hint "First name the zero vector: which real number $z$ has $v + z = v$ for every $v$?
    Then split the two parts with `constructor`."
    Hint (hidden := true) "`use 0`, then `constructor`."
    use 0
    constructor
    · intro v
      ring
    · intro v
      Hint (hidden := true) "Take $w = -v$ with `use -{v}`."
      use -v
      ring
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

The same checklist holds for every `[Module ℝ V]` (the game calls this theorem
`axioms_of_module`), and it is why levels 1–7 could write `[Module ℝ V]` for
\"$V$ is a vector space\". You prove it yourself in level 1 of the optional *From Scratch*
world.
"

NewDefinition LinearAlgebraGame.VectorSpaceAxioms
NewTheorem add_comm add_neg_cancel smul_add
TheoremTab "Vector spaces"
