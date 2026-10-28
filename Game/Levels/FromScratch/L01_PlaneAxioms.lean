import Game.Metadata
import Game.Ch2a

World "FromScratch"
Level 1
Title "The plane satisfies the ten conditions"

Introduction "
This optional world rebuilds Two.I–II on the game's own definitions and then proves they agree
with Mathlib's. We start where Hefferon does: $\\mathbb{R}^2$ (here `ℝ × ℝ`) with the usual
operations satisfies the ten conditions, i.e. `VectorSpaceAxioms`.

Each condition is an existing algebraic law: `add_comm`, `add_assoc`, `add_zero`,
`add_smul`, `smul_add`, `smul_smul`, `one_smul`.
"

namespace LinearAlgebraGame

/-- $\mathbb{R}^2$ with the usual operations satisfies Hefferon's conditions. -/
Statement : VectorSpaceAxioms (ℝ × ℝ) (· + ·) (· • ·) := by
  constructor
  · intro u v
    exact add_comm u v
  · intro u v w
    exact add_assoc u v w
  · use 0
    intro v
    exact add_zero v
  · Hint "Take $\\vec w = -\\vec v$. A would-be zero $\\vec z$ satisfies $\\vec 0 + \\vec z = \\vec 0$,
    so $\\vec z = \\vec 0$."
    intro v
    use -v
    intro z hz
    Hint (hidden := true) "`have h0 := {hz} 0`, `rw [zero_add] at h0`, `rw [h0, add_neg_cancel]`."
    have h0 := hz 0
    rw [zero_add] at h0
    rw [h0, add_neg_cancel]
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
The same proof works for any Mathlib vector space: that is the library's
`VectorSpaceAxioms.of_module`.
"

NewTheorem add_comm add_neg_cancel smul_add
DisabledTheorem LinearAlgebraGame.VectorSpaceAxioms.of_module
DisabledTactic simp
TheoremTab "From Scratch"
