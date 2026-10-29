import Mathlib

/-! `entrywise` — prove an equation between concrete vectors or matrices one entry at a time.

It is `ext` followed by `fin_cases` on every index, then a clean-up so each goal reads
`(A *ᵥ v) 0 = ![3, 7] 0` instead of Lean's raw `((fun i => i) ⟨0, ⋯⟩)` form:
* indices are normalised everywhere (both sides), `v = 0` becomes `v 0 = 0` (not `v 0 = 0 0`);
* entries of the identity matrix are evaluated (`(1 : Matrix _ _ ℝ) 0 1` becomes `0`) —
  `simp` cannot see inside `1 i j` otherwise;
* sums over `Fin 2`, `Fin 3`, `Fin 4` that are already visible are written out
  (`∑ x, f x` becomes `f 0 + f 1 + f 2`), so `norm_num` can finish them.
Matrix products `(A * B) i j` and `A *ᵥ v` are NOT expanded: that is the player's
`Matrix.mul_apply` / `Matrix.mulVec` step. -/

namespace LinearAlgebraGame

macro "entrywise_clean" : tactic =>
  `(tactic| try simp only [Fin.zero_eta, Fin.mk_one, Fin.isValue, Fin.reduceFinMk, Pi.zero_apply,
      Matrix.zero_apply, Matrix.one_apply_eq, Matrix.one_apply_ne, ne_eq, Fin.reduceEq,
      not_false_eq_true, Fin.sum_univ_two, Fin.sum_univ_three, Fin.sum_univ_four])

macro "entrywise" : tactic =>
  `(tactic| first
    | (ext i j
       fin_cases i <;> fin_cases j <;> entrywise_clean)
    | (ext i
       fin_cases i <;> entrywise_clean)
    | fail "entrywise needs vectors or matrices of a concrete size like Fin 3 (here the size is a letter): use ext i instead")

end LinearAlgebraGame
