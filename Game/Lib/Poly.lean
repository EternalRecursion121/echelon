import Mathlib

/-! Poly n: polynomials of degree ≤ n, as coefficient vectors (a₀, …, aₙ).

Mathlib's `Polynomial.degreeLT` works, but its coercions are hard on beginners. Hefferon
identifies 𝒫ₙ with ℝⁿ⁺¹ via the basis ⟨1, x, …, xⁿ⟩ anyway, so the game does the same. -/

namespace LinearAlgebraGame

/-- Polynomials of degree at most `n`, stored as coefficients: `p i` is the coefficient of xⁱ. -/
abbrev Poly (n : ℕ) := Fin (n + 1) → ℝ

/-- Evaluate a polynomial at `x`. -/
def Poly.eval {n : ℕ} (p : Poly n) (x : ℝ) : ℝ := ∑ i, p i * x ^ (i : ℕ)

/-- Evaluation at a fixed point is linear in the polynomial. -/
def Poly.evalAt {n : ℕ} (x : ℝ) : Poly n →ₗ[ℝ] ℝ where
  toFun p := p.eval x
  map_add' p q := by simp [Poly.eval, add_mul, Finset.sum_add_distrib]
  map_smul' r p := by simp [Poly.eval, Finset.mul_sum, mul_assoc]

/-- Differentiation d/dx : Poly n → Poly n: the coefficient of xⁱ in p' is (i+1)·aᵢ₊₁. -/
def Poly.deriv {n : ℕ} : Poly n →ₗ[ℝ] Poly n where
  toFun p i := if h : (i : ℕ) < n then ((i : ℕ) + 1 : ℝ) * p ⟨i + 1, by omega⟩ else 0
  map_add' p q := by
    funext i; simp only [Pi.add_apply]; split_ifs <;> ring
  map_smul' r p := by
    funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; split_ifs <;> ring

end LinearAlgebraGame
