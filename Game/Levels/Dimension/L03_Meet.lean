import Game.Levels.Dimension.L02_InfiniteDim

World "Dimension"
Level 3
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

In Lean $U\\cap W$ is `U ⊓ W`, $U + W$ is `U ⊔ W` and the trivial subspace is `⊥`. From
lectures (Two.III.4) you may use the dimension formula
`Submodule.finrank_sup_add_finrank_inf_eq`:
$\\dim(U+W) + \\dim(U\\cap W) = \\dim U + \\dim W$ — you will prove it yourself on Sheet 6.
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
  have key := Submodule.finrank_sup_add_finrank_inf_eq U W
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
NewTheorem finrank_bot Submodule.finrank_le Submodule.finrank_sup_add_finrank_inf_eq Module.finrank_fin_fun trivial
