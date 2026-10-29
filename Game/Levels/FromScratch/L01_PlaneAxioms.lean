import Game.Metadata
import Game.Ch2a

World "FromScratch"
Level 1
Title "Every vector space satisfies the ten conditions"

Introduction "
This optional world rebuilds Two.I–II on the game's own definitions and then proves they agree
with Mathlib's. We start with the bridge the Ten Conditions world took on trust: a Mathlib
vector space `[AddCommGroup V] [Module ℝ V]` satisfies the game's checklist
`VectorSpaceAxioms` (with the usual `+` and `•`).

Each condition is one of the laws in the table of Ten Conditions level 1: `add_comm`,
`add_assoc`, `add_zero`, `add_neg_cancel`, `add_smul`, `smul_add`, `smul_smul` (condition (9)
read backwards) and `one_smul ℝ v`.
"

namespace LinearAlgebraGame

/-- Every real vector space (in Mathlib's sense) satisfies Hefferon's ten conditions. -/
Statement axioms_of_module (V : Type*) [AddCommGroup V] [Module ℝ V] :
    VectorSpaceAxioms V (· + ·) (· • ·) := by
  Hint "`constructor` gives one goal per condition."
  constructor
  · intro u v
    exact add_comm u v
  · intro u v w
    exact add_assoc u v w
  · Hint "Name the zero vector, then prove both parts: it is a zero, and every $\\vec v$ has an
    inverse."
    Hint (hidden := true) "`use 0`, `constructor`; for the inverse of `v` take `-v`."
    use 0
    constructor
    · intro v
      exact add_zero v
    · intro v
      use -v
      Hint (hidden := true) "`exact add_neg_cancel {v}`"
      exact add_neg_cancel v
  · intro r s v
    exact add_smul r s v
  · intro r u v
    exact smul_add r u v
  · intro r s v
    Hint (hidden := true) "`rw [smul_smul]`"
    rw [smul_smul]
  · intro v
    exact one_smul ℝ v

end LinearAlgebraGame

Conclusion "
So every theorem of Chapter Two stated for `[Module ℝ V]` is a theorem about Hefferon's vector
spaces. `axioms_of_module V` is now in your inventory.
"

DisabledTactic simp
TheoremTab "From Scratch"
