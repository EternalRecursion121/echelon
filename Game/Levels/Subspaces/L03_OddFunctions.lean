import Game.Levels.Subspaces.L02_Planes

World "Subspaces"
Level 3
Title "Odd functions"

-- @sheet 4 Q4
/-! @answer
**Yes.** The zero function is odd: $0(-x) = 0 = -0(x)$. If $f, g$ are odd and
$c_1, c_2 \in \mathbb{R}$ then for every $x$,
$$(c_1f + c_2g)(-x) = c_1f(-x) + c_2g(-x) = -c_1f(x) - c_2g(x) = -(c_1f + c_2g)(x),$$
so $c_1f + c_2g$ is odd. By the subspace test (Lemma Two.I.2.9), $S$ is a subspace.
(Examples: $x^3$ and $\sin x$ are in $S$, and so is $2x^3 - 5\sin x$.)
-/
Introduction "
**Problem Sheet 4, Question 4.** Is the set of odd functions
$S := \\{f : \\mathbb{R} \\to \\mathbb{R} \\mid f(-x) = -f(x) \\text{ for all } x\\}$
a subspace of the vector space of real-valued functions of one real variable?
Two members are $f_3(x) = x^3$ and $f_4(x) = \\sin(x)$.

Decide: `left` for \"no\", `right` for \"yes\".
"

namespace LinearAlgebraGame

/-- Are the odd functions a subspace of the functions $\mathbb{R} \to \mathbb{R}$? -/
Statement : (¬ ∃ W : Submodule ℝ (ℝ → ℝ), (W : Set (ℝ → ℝ)) = {f | ∀ x, f (-x) = -f x}) ∨
    ∃ W : Submodule ℝ (ℝ → ℝ), (W : Set (ℝ → ℝ)) = {f | ∀ x, f (-x) = -f x} := by
  Hint "Is a combination of odd functions odd? Is the zero function odd?"
  right
  apply subspace_test
  · use 0
    intro x
    Hint (hidden := true) "`rw [Pi.zero_apply, Pi.zero_apply, neg_zero]`"
    rw [Pi.zero_apply, Pi.zero_apply, neg_zero]
  · intro c₁ c₂ f g hf hg x
    Hint "Evaluate the combination pointwise, then use that `{f}` and `{g}` are odd."
    Hint (hidden := true) "`rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply,
    Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, {hf} x, {hg} x]`
    then `ring`."
    rw [Pi.add_apply, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, Pi.smul_apply,
      smul_eq_mul, smul_eq_mul, smul_eq_mul, smul_eq_mul, hf x, hg x]
    ring

end LinearAlgebraGame

Conclusion "**Answer: yes**, the odd functions form a subspace."

DisabledTactic simp norm_num
TheoremTab "Subspaces"
NewTheorem neg_zero
