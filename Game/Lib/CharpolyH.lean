import Mathlib

/-! Hefferon's characteristic polynomial |T − xI| (Def Five.II.3.9).

Mathlib's `Matrix.charpoly` is det(xI − T), which differs by the sign (−1)ⁿ. -/

namespace LinearAlgebraGame

open Polynomial

/-- Hefferon's characteristic polynomial: det(T − x·I). -/
noncomputable def charpolyH {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) : ℝ[X] :=
  ((C : ℝ →+* ℝ[X]).mapMatrix T - Matrix.scalar (Fin n) (X : ℝ[X])).det

/-- Bridge to Mathlib: |T − xI| = (−1)ⁿ · det(xI − T). -/
theorem charpolyH_eq {n : ℕ} (T : Matrix (Fin n) (Fin n) ℝ) :
    charpolyH T = (-1) ^ n * T.charpoly := by
  rw [charpolyH, Matrix.charpoly, Matrix.charmatrix, ← neg_sub, Matrix.det_neg,
    Fintype.card_fin]

end LinearAlgebraGame
