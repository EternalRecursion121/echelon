import Mathlib

/-! Hefferon's Definition Two.I.1.1 as a *predicate* on explicit operations.

Mathlib's `Module` is a typeclass, so "this set with these operations is *not* a vector
space" cannot be stated against it. This predicate can. Closure (Hefferon's conditions 1
and 6) is automatic from the types of `add` and `smul`. -/

namespace LinearAlgebraGame

structure VectorSpaceAxioms (V : Type*) (add : V → V → V) (smul : ℝ → V → V) : Prop where
  add_comm : ∀ u v, add u v = add v u
  add_assoc : ∀ u v w, add (add u v) w = add u (add v w)
  has_zero : ∃ z, ∀ v, add v z = v
  has_neg : ∀ v, ∃ w, ∀ z, (∀ x, add x z = x) → add v w = z
  add_smul : ∀ r s v, smul (r + s) v = add (smul r v) (smul s v)
  smul_add : ∀ r u v, smul r (add u v) = add (smul r u) (smul r v)
  mul_smul : ∀ r s v, smul (r * s) v = smul r (smul s v)
  one_smul : ∀ v, smul 1 v = v

/-- Bridge: every Mathlib real vector space satisfies the ten conditions. -/
theorem VectorSpaceAxioms.of_module (V : Type*) [AddCommGroup V] [Module ℝ V] :
    VectorSpaceAxioms V (· + ·) (· • ·) where
  add_comm := _root_.add_comm
  add_assoc := _root_.add_assoc
  has_zero := ⟨0, add_zero⟩
  has_neg v := ⟨-v, fun z hz => by
    have : z = 0 := by simpa using hz 0
    rw [this, add_neg_cancel]⟩
  add_smul := _root_.add_smul
  smul_add := _root_.smul_add
  mul_smul r s v := (smul_smul r s v).symm
  one_smul v := _root_.one_smul ℝ v

end LinearAlgebraGame
