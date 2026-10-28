import Game.Levels.MatrixAlgebra.L09_RowSums

World "MatrixAlgebra"
Level 10
Title "Invertible iff nonsingular"

Introduction "
**Boss.** Hefferon Theorem Three.IV.4.3: a square matrix is invertible if and only if it is
nonsingular ($H\\vec x = \\vec 0$ only for $\\vec x = \\vec 0$).

* (⇒) is a one-line cancellation.
* (⇐) The dimension count of Chapter Two (one-to-one ⇒ onto for a square matrix) is granted as
  `exists_right_inv_of_nonsingular`: a nonsingular square matrix has a **right** inverse $G$.
  But we need $G$ to be a two-sided inverse. Show that $G$ is itself nonsingular, give it a
  right inverse $K$ too, and let `inv_left_eq_inv_right` finish.

(`mul_eq_one_comm`, which would do the second half for you, is disabled.)
"

namespace LinearAlgebraGame

open Matrix in
/-- $H$ has a two-sided inverse iff $H\vec x = \vec 0 \Rightarrow \vec x = \vec 0$. -/
Statement {n : ℕ} (H : Matrix (Fin n) (Fin n) ℝ) :
    (∃ G, G * H = 1 ∧ H * G = 1) ↔ ∀ x, H *ᵥ x = 0 → x = 0 := by
  constructor
  · Hint "If $GH = I$ and $H\\vec x = \\vec 0$, then $\\vec x = (GH)\\vec x = \\dots$"
    intro hG x hx
    obtain ⟨G, hGH, _⟩ := hG
    Hint (hidden := true) "`calc x = (G * H) *ᵥ x := by rw [{hGH}, Matrix.one_mulVec]`
    `_ = 0 := by rw [← Matrix.mulVec_mulVec, {hx}, Matrix.mulVec_zero]`"
    calc x = (G * H) *ᵥ x := by rw [hGH, Matrix.one_mulVec]
      _ = 0 := by rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
  · intro hinj
    Hint "Get a right inverse $G$ of $H$ from the granted theorem."
    obtain ⟨G, hHG⟩ := exists_right_inv_of_nonsingular H hinj
    Hint "Now show $G$ is nonsingular: if $G\\vec x = 0$ then $\\vec x = (HG)\\vec x = 0$."
    have hGinj : ∀ x, G *ᵥ x = 0 → x = 0 := by
      intro x hx
      calc x = (H * G) *ᵥ x := by rw [hHG, Matrix.one_mulVec]
        _ = 0 := by rw [← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]
    Hint "So $G$ has a right inverse $K$ as well. $G$ now has a left inverse $H$ and a right
    inverse $K$…"
    obtain ⟨K, hGK⟩ := exists_right_inv_of_nonsingular G hGinj
    have hHK : H = K := inv_left_eq_inv_right hHG hGK
    Hint (hidden := true) "`refine ⟨G, ?_, {hHG}⟩` and then `rw [{hHK}, {hGK}]`."
    refine ⟨G, ?_, hHG⟩
    rw [hHK, hGK]

end LinearAlgebraGame

Conclusion "
For square matrices: invertible ⇔ nonsingular ⇔ one-sided inverse. You have also shown that a
one-sided inverse of a square matrix is automatically two-sided.
"

NewTheorem LinearAlgebraGame.exists_right_inv_of_nonsingular
DisabledTheorem mul_eq_one_comm Matrix.mulVec_injective_iff_isUnit Matrix.mulVec_surjective_iff_exists_right_inverse
TheoremTab "Matrices"
