import Game.Levels.Diagonalisation.L11_DetProduct

World "Diagonalisation"
Level 12
Title "Boss: geometric ≤ algebraic"

-- @sheet 10 Q7
/-! @answer
Let $k = \dim V_\lambda$ and let $\vec v_1,\dots,\vec v_k$ be a basis of $V_\lambda$, extended to a
basis $\vec v_1,\dots,\vec v_n$ of the whole space. Let $P^{-1}$ have columns $\vec v_1,\dots,\vec v_n$
and $B = PAP^{-1}$. For $j \le k$, column $j$ of $B$ is
$B\vec e_j = PA\vec v_j = \lambda P\vec v_j = \lambda\vec e_j$. So the first $k$ columns of $B - xI$
are $(\lambda - x)\vec e_j$, and expanding the determinant along them gives
$|B - xI| = (\lambda - x)^k\,q(x)$. Since $B$ is similar to $A$ (Q3), $|A - xI| = |B - xI|$ is
divisible by $(x - \lambda)^k$, so the algebraic multiplicity of $\lambda$ is at least $k$.
-/
Introduction "
**Problem Sheet 10, Question 7.** Let $\\lambda$ be an eigenvalue of $A$. Prove that the
geometric multiplicity of $\\lambda$ is at most the algebraic multiplicity.

*Hint (from the sheet):* let $\\langle\\vec v_1,\\dots,\\vec v_k\\rangle$ be a basis for the
eigenspace, extend it to a basis $\\langle\\vec v_1,\\dots,\\vec v_n\\rangle$, form the matrix
with columns $\\vec v_1,\\dots,\\vec v_n$ (we call it $Q = P^{-1}$). What are the first $k$
columns of $B = Q^{-1}AQ$?

In Lean, $k = \\dim V_\\lambda$ (`hk`), and $\\vec e_j$ is `Pi.single j 1`; column $j$ of a
matrix $M$ is $M\\vec e_j$. Two pieces of bookkeeping are **granted** as hypotheses:

* `hext` — basis extension: there is a nonsingular $Q$ whose first $k$ columns $Q\\vec e_j$
  are eigenvectors (Chapter Two's \"extend to a basis\");
* `hblock` — Laplace expansion: if $k \\le n$ and the first $k$ columns of $B$ are
  $\\lambda\\vec e_j$, then $(x - \\lambda)^k$ divides $|B - xI|$.

The rest is yours: compute the first $k$ columns of $B = Q^{-1}AQ$, check $k \\le n$, use Q3
(`charpolyH_similar`), and convert divisibility into multiplicity with
`Polynomial.le_rootMultiplicity_iff`.

Your hand-in should also justify the two granted steps in words: inside your proof write a
comment block starting `-- Explain:` saying why such a $Q$ exists (extend a basis of the
eigenspace) and why $(x - \\lambda)^k$ divides $|B - xI|$ (expand the determinant along the first
$k$ columns).
"

namespace LinearAlgebraGame

open Matrix Polynomial Module in
/-- The geometric multiplicity of $\lambda$ is at most its algebraic multiplicity. -/
Statement {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (μ : ℝ) (k : ℕ)
    (hk : finrank ℝ (End.eigenspace (toLin' A) μ) = k)
    (hext : ∃ Q : Matrix (Fin n) (Fin n) ℝ, IsUnit Q ∧
      ∀ j : Fin n, (j : ℕ) < k → A *ᵥ (Q *ᵥ Pi.single j 1) = μ • (Q *ᵥ Pi.single j 1))
    (hblock : ∀ B : Matrix (Fin n) (Fin n) ℝ, k ≤ n →
      (∀ j : Fin n, (j : ℕ) < k → B *ᵥ Pi.single j 1 = μ • Pi.single j 1) →
        (X - C μ) ^ k ∣ charpolyH B) :
    k ≤ rootMultiplicity μ (charpolyH A) := by
  -- Explain: (hext) extend a basis v₁,…,v_k of the eigenspace to a basis v₁,…,v_n of ℝⁿ; the
  -- matrix Q with these columns is nonsingular and Q e_j = v_j is an eigenvector for j ≤ k.
  -- (hblock) if column j of B is λ e_j for j ≤ k, the first k columns of B - xI are (λ - x) e_j;
  -- expanding the determinant along them gives |B - xI| = (λ - x)^k q(x).
  Hint "Take $Q$ from `hext` and set $B = Q⁻¹AQ$. Show column $j$ of $B$ is $\\lambda\\vec e_j$ for $j < k$."
  obtain ⟨Q, hQ, hcols⟩ := hext
  Hint (hidden := true) "`have hB : ∀ j : Fin n, (j : ℕ) < k → (Q⁻¹ * A * Q) *ᵥ Pi.single j 1 = μ • Pi.single j 1`.
  For it: `intro j hj`, then
  `rw [← mulVec_mulVec, ← mulVec_mulVec, hcols j hj, mulVec_smul, mulVec_mulVec, inv_mul_of_isUnit hQ, one_mulVec]`."
  have hB : ∀ j : Fin n, (j : ℕ) < k → (Q⁻¹ * A * Q) *ᵥ Pi.single j 1 = μ • Pi.single j 1 := by
    intro j hj
    rw [← mulVec_mulVec, ← mulVec_mulVec, hcols j hj, mulVec_smul, mulVec_mulVec,
      inv_mul_of_isUnit hQ, one_mulVec]
  Hint (hidden := true) "The dimension of a subspace of $\\mathbb R^n$ is at most $n$:
  `have hkn : k ≤ n`, by `rw [← hk]`, `have h := Submodule.finrank_le (End.eigenspace (toLin' A) μ)`,
  `rw [Module.finrank_fin_fun] at h` and `exact h`."
  have hkn : k ≤ n := by
    rw [← hk]
    have h := Submodule.finrank_le (End.eigenspace (toLin' A) μ)
    rw [Module.finrank_fin_fun] at h
    exact h
  Hint (hidden := true) "`have hdvd := hblock _ hkn hB`, then replace `charpolyH (Q⁻¹ * A * Q)` by
  `charpolyH A` using `charpolyH_similar` (similar via `P := Q⁻¹`)."
  have hdvd := hblock _ hkn hB
  have hsim : MatSimilar A (Q⁻¹ * A * Q) := by
    use Q⁻¹
    constructor
    · exact isUnit_inv_of_isUnit hQ
    · rw [inv_inv_of_isUnit hQ]
  rw [← charpolyH_similar A _ hsim] at hdvd
  Hint (hidden := true) "`exact (le_rootMultiplicity_iff (charpolyH_ne_zero A)).2 hdvd`."
  exact (le_rootMultiplicity_iff (charpolyH_ne_zero A)).2 hdvd

end LinearAlgebraGame

Conclusion "
Geometric $\\le$ algebraic. Equality for every eigenvalue (with all eigenvalues real) is
exactly the condition for $A$ to be diagonalisable.
"

NewTheorem LinearAlgebraGame.charpolyH_similar LinearAlgebraGame.charpolyH_ne_zero Polynomial.le_rootMultiplicity_iff
DisabledTheorem LinearMap.finrank_eigenspace_le
TheoremTab "Eigen"
