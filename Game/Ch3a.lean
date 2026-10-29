import GameServer
import Mathlib
import Game.Lib

/-! # Chapter Three, part 1: Isomorphisms (Three.I) and Homomorphisms (Three.II)

Game-local definitions for the worlds
`Isomorphisms` and `Homomorphisms`.
(Inventory docs for everything live in `Game/Doc/Theorems.lean`.) -/

namespace LinearAlgebraGame

/-- The line segment from `u` to `v` (Sheet 5 Q3): `{ t • u + (1 - t) • v | t ∈ [0, 1] }`. -/
def seg {V : Type*} [AddCommGroup V] [Module ℝ V] (u v : V) : Set V :=
  {x | ∃ t ∈ Set.Icc (0 : ℝ) 1, x = t • u + (1 - t) • v}

/-- A set is convex if it contains the segment between any two of its points (Sheet 5 Q3b). -/
def IsConvex {V : Type*} [AddCommGroup V] [Module ℝ V] (C : Set V) : Prop :=
  ∀ u ∈ C, ∀ v ∈ C, seg u v ⊆ C

/-- A pair of subspace elements is zero iff both underlying vectors are zero. -/
theorem pair_eq_zero_iff {V : Type*} [AddCommGroup V] [Module ℝ V] {U W : Submodule ℝ V}
    (u : U) (w : W) : (u, w) = 0 ↔ (u : V) = 0 ∧ (w : V) = 0 := by
  rw [Prod.ext_iff]
  simp

end LinearAlgebraGame
