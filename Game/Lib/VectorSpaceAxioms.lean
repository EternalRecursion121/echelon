import Mathlib

/-! Hefferon's Definition Two.I.1.1 as a *predicate* on explicit operations.

Mathlib's `Module` is a typeclass, so "this set with these operations is *not* a vector
space" cannot be stated against it. This predicate can. Closure (Hefferon's conditions 1
and 6) is automatic from the types of `add` and `smul`. Conditions (4) and (5) are one field,
`has_zero_neg`, because (5) refers to the zero vector of (4) — exactly as Hefferon states them.

The bridge "every Mathlib real vector space satisfies the ten conditions"
(`LinearAlgebraGame.axioms_of_module`) is proved by the player in From Scratch
level 1. -/

namespace LinearAlgebraGame

structure VectorSpaceAxioms (V : Type*) (add : V → V → V) (smul : ℝ → V → V) : Prop where
  add_comm : ∀ u v, add u v = add v u
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  has_zero_neg : ∃ z, (∀ v, add v z = v) ∧ ∀ v, ∃ w, add v w = z
  add_smul : ∀ r s v, smul (r + s) v = add (smul r v) (smul s v)
  smul_add : ∀ r u v, smul r (add u v) = add (smul r u) (smul r v)
  mul_smul : ∀ r s v, smul (r * s) v = smul r (smul s v)
  one_smul : ∀ v, smul 1 v = v

end LinearAlgebraGame
