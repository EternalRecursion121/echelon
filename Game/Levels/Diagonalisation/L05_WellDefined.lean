import Game.Levels.Diagonalisation.L04_Product

World "Diagonalisation"
Level 5
Title "The characteristic polynomial is well defined"

-- @sheet 10 Q3
/-! @answer
The characteristic polynomial of $t$ is defined as $|T - xI|$ for $T = \mathrm{Rep}_{B,B}(t)$.
Another basis gives a similar matrix $\hat T = PTP^{-1}$. Since $xI = P(xI)P^{-1}$,
$$|\hat T - xI| = |P(T - xI)P^{-1}| = |P|\,|T - xI|\,|P^{-1}| = |T - xI|,$$
using $|AB| = |A||B|$ and $|P||P^{-1}| = |PP^{-1}| = 1$. So the polynomial does not depend on the basis.
-/
Introduction "
**Problem Sheet 10, Question 3.** Prove that the characteristic polynomial of a
transformation is well-defined.

The matrices of one transformation in different bases are exactly the similar matrices.
So: **prove that similar matrices have the same characteristic polynomial** $|T - xI|$.

In `charpolyH T`, the real matrix $T$ becomes a matrix of polynomials via
`C.mapMatrix`, which respects products (`map_mul`) and the identity (`map_one`).
`Matrix.scalar_commute` says $xI$ commutes with every matrix.
"

namespace LinearAlgebraGame

open Matrix Polynomial in
/-- Similar matrices have the same characteristic polynomial. -/
Statement charpolyH_similar {n : ℕ} (T S : Matrix (Fin n) (Fin n) ℝ) (h : MatSimilar T S) :
    charpolyH T = charpolyH S := by
  Hint "Hefferon: $|PTP⁻¹ - xI| = |P(T - xI)P⁻¹| = |P|\\,|T - xI|\\,|P⁻¹|$."
  obtain ⟨P, hP, hS⟩ := h
  rw [hS, charpolyH, charpolyH]
  Hint (hidden := true) "First: `have hPQ : C.mapMatrix P * C.mapMatrix P⁻¹ = 1` by
  `rw [← map_mul, mul_inv_of_isUnit hP, map_one]`."
  have hPQ : (C : ℝ →+* ℝ[X]).mapMatrix P * (C : ℝ →+* ℝ[X]).mapMatrix P⁻¹ = 1 := by
    rw [← map_mul, mul_inv_of_isUnit hP, map_one]
  Hint (hidden := true) "Next, $P(xI)P⁻¹ = xI$: rewrite with
  `← (scalar_commute X (fun _ => Commute.all _ _) _).eq`, `Matrix.mul_assoc`, `hPQ`, `Matrix.mul_one`."
  have hs : (C : ℝ →+* ℝ[X]).mapMatrix P * scalar (Fin n) X * (C : ℝ →+* ℝ[X]).mapMatrix P⁻¹
      = scalar (Fin n) X := by
    rw [← (scalar_commute X (fun _ => Commute.all _ _) _).eq, Matrix.mul_assoc, hPQ,
      Matrix.mul_one]
  Hint (hidden := true) "Now the key identity
  `C.mapMatrix (P * T * P⁻¹) - scalar X = C.mapMatrix P * (C.mapMatrix T - scalar X) * C.mapMatrix P⁻¹`:
  `rw [map_mul, map_mul, Matrix.mul_sub, Matrix.sub_mul, hs]`."
  have key : (C : ℝ →+* ℝ[X]).mapMatrix (P * T * P⁻¹) - scalar (Fin n) X
      = (C : ℝ →+* ℝ[X]).mapMatrix P * ((C : ℝ →+* ℝ[X]).mapMatrix T - scalar (Fin n) X)
        * (C : ℝ →+* ℝ[X]).mapMatrix P⁻¹ := by
    rw [map_mul, map_mul, Matrix.mul_sub, Matrix.sub_mul, hs]
  Hint (hidden := true) "Finally `rw [key, det_mul, det_mul]`, move `det P` next to `det P⁻¹`
  (`mul_comm`, `mul_assoc`), and use `← det_mul, hPQ, det_one`."
  rw [key, det_mul, det_mul, mul_comm (det ((C : ℝ →+* ℝ[X]).mapMatrix P)), mul_assoc, ← det_mul,
    hPQ, det_one, mul_one]

end LinearAlgebraGame

Conclusion "So the characteristic polynomial, its roots (eigenvalues) and their multiplicities belong to the transformation, not to a basis."

NewTheorem map_mul map_one Matrix.scalar_commute Commute.all Matrix.mul_sub Matrix.sub_mul mul_assoc
DisabledTheorem Matrix.charpoly_units_conj Matrix.charpoly_units_conj'
TheoremTab "Eigen"
