import Game.Levels.Dimension.L12_DimFormula

World "Dimension"
Level 13
Title "Two 3-dimensional subspaces of ℝ⁵"

-- @sheet 4 Q9
/-! @answer
$U + W \subseteq \mathbb R^5$, so $\dim(U+W) \le 5$. By the dimension formula
$\dim(U\cap W) = \dim U + \dim W - \dim(U+W) \ge 3 + 3 - 5 = 1$, so $U\cap W \neq \{\vec 0\}$.
(Without the formula: take bases $\vec u_1,\vec u_2,\vec u_3$ and $\vec w_1,\vec w_2,\vec w_3$;
six vectors in $\mathbb R^5$ are dependent, $\sum a_i\vec u_i = -\sum b_i\vec w_i$ with not all
coefficients zero, and this common vector is nonzero by independence of each basis and lies in
$U\cap W$.)
**Generalisation:** if $U, W$ are subspaces of an $n$-dimensional space with
$\dim U + \dim W > n$, then $U \cap W$ is non-trivial.
-/
Introduction "
**Problem Sheet 4, Question 9.** Prove that if $U$ and $W$ are both three-dimensional
subspaces of $\\mathbb R^5$ then $U \\cap W$ is non-trivial. Generalise the claim (no new proof
is required as it would be similar).

In Lean $U\\cap W$ is `U ⊓ W`, $U + W$ is `U ⊔ W` and the trivial subspace is `⊥`. Use your
dimension formula `dim_formula`; the bases it needs come from `exists_bases_inf U W`
(granted: a basis of $U\\cap W$ extends to bases of $U$ and of $W$).
`Submodule.finrank_le` bounds the dimension of a subspace by that of the whole space, and
`Module.finrank_fin_fun` says $\\dim \\mathbb R^n = n$.

Write the generalisation as a comment starting `-- Explain:`.
"

namespace LinearAlgebraGame

/-- Two 3-dimensional subspaces of $\mathbb R^5$ meet non-trivially. -/
Statement (U W : Submodule ℝ (Fin 5 → ℝ)) (hU : Module.finrank ℝ U = 3)
    (hW : Module.finrank ℝ W = 3) : U ⊓ W ≠ ⊥ := by
  Hint "Suppose $U\\cap W$ is trivial; then the dimension formula says $\\dim(U+W) = 6$."
  intro h
  Hint (hidden := true) "`obtain ⟨j, k, p, β, μ, ω, hβ, hU', hW'⟩ := exists_bases_inf U W`, then
  `have key := dim_formula U W β μ ω hβ hU' hW'`."
  obtain ⟨j, k, p, β, μ, ω, hβ, hU', hW'⟩ := exists_bases_inf U W
  have key := dim_formula U W β μ ω hβ hU' hW'
  Hint (hidden := true) "`rw [{h}, finrank_bot, {hU}, {hW}] at {key}`"
  rw [h, finrank_bot, hU, hW] at key
  Hint "But $U + W$ lives in $\\mathbb R^5$."
  have h5 := Submodule.finrank_le (U ⊔ W)
  rw [Module.finrank_fin_fun] at h5
  -- Explain: in general, if dim U + dim W > dim V then U ∩ W ≠ {0}.
  Hint (hidden := true) "Generalisation: *if $\\dim U + \\dim W > \\dim V$ then
  $U\\cap W$ is non-trivial*. Finish with `omega`."
  omega

end LinearAlgebraGame

Conclusion "
In general: $\\dim U + \\dim W > \\dim V \\implies U \\cap W \\ne \\{\\vec 0\\}$.
"

DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTheorem LinearAlgebraGame.dim_formula LinearAlgebraGame.exists_bases_inf finrank_bot Submodule.finrank_le Module.finrank_fin_fun
