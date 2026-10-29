import Game.Levels.Subspaces.L03_OddFunctions

World "Subspaces"
Level 4
Title "Solutions of a differential equation"

-- @sheet 4 Q2
/-! @answer
Write $S = \{f \mid f \text{ differentiable}, f' + 2f = 0\}$, a subset of the vector space of
all functions $\mathbb{R}\to\mathbb{R}$. It suffices (subspace test) to check that $S$ is
nonempty and closed under linear combinations; the other conditions (commutativity,
associativity, distributivity, $1\cdot f = f$, inverses) are then inherited from the
function space. The zero function is differentiable with $0' + 2\cdot 0 = 0$. If
$f, g \in S$ then $c_1f + c_2g$ is differentiable and, since differentiation is linear,
$(c_1f + c_2g)' + 2(c_1f + c_2g) = c_1(f' + 2f) + c_2(g' + 2g) = 0$. (The solutions are
exactly $Ce^{-2x}$.)
-/
Introduction "
**Problem Sheet 4, Question 2.** Briefly argue why the set of functions
$\\{f : \\mathbb{R} \\to \\mathbb{R} \\mid \\frac{df}{dx} + 2f = 0\\}$ is a vector space. You may
focus on the least obvious points, but make sure you are convinced of all 10 conditions.

Since this set sits inside the vector space of all functions, it is enough to show it is a
subspace (the remaining conditions are inherited). In Lean the set must say that $f$ is
**differentiable** — the next hint explains why. Also write your brief argument as a
comment starting `-- Explain:` inside your proof.

`Differentiable ℝ f` means `∀ x, DifferentiableAt ℝ f x` ($f$ is differentiable at every
point). Your inventory gains the calculus you need, all in the Subspaces tab:
- for the zero function: `differentiable_const`, `deriv_const`, and `Pi.zero_def` (the zero
  function is the constant function `fun _ => 0`), `mul_zero`;
- for combinations (granted, since calculus is not the point here): `differentiable_comb` and
  `deriv_comb` — differentiation is linear.
"

namespace LinearAlgebraGame

/-- The differentiable solutions of $f' + 2f = 0$ form a subspace of the functions
$\mathbb{R}\to\mathbb{R}$. -/
Statement : ∃ W : Submodule ℝ (ℝ → ℝ),
    (W : Set (ℝ → ℝ)) = {f | Differentiable ℝ f ∧ ∀ x, deriv f x + 2 * f x = 0} := by
  Hint "Why `Differentiable`? Lean's `deriv f x` is a total function: where $f$ is not
  differentiable it returns the *junk value* $0$. The rule
  $(f + g)' = f' + g'$ is only true when $f$ and $g$ are differentiable, so
  without that condition in the set we could not prove closure under addition. On paper,
  \"$\\frac\{df}\{dx}$ exists\" is implicit in writing the equation; Lean makes it explicit."
  apply subspace_test
  · use 0
    constructor
    · Hint (hidden := true) "`exact differentiable_const 0`"
      exact differentiable_const 0
    · intro x
      Hint (hidden := true) "`rw [Pi.zero_def, deriv_const, mul_zero, add_zero]`"
      rw [Pi.zero_def, deriv_const, mul_zero, add_zero]
  · intro c₁ c₂ f g hf hg
    obtain ⟨hfd, hf⟩ := hf
    obtain ⟨hgd, hg⟩ := hg
    constructor
    · Hint (hidden := true) "`exact differentiable_comb {hfd} {hgd} c₁ c₂`"
      exact differentiable_comb hfd hgd c₁ c₂
    · intro x
      Hint "Differentiation is linear: split the derivative of the combination."
      Hint (hidden := true) "`rw [deriv_comb {hfd} {hgd}]`, then unfold the pointwise operations
      with `Pi.add_apply`, `Pi.smul_apply`, `smul_eq_mul`."
      rw [deriv_comb hfd hgd, Pi.add_apply, Pi.smul_apply, Pi.smul_apply, smul_eq_mul,
        smul_eq_mul]
      Hint (hidden := true) "Model explanation: the set lies inside the vector space of all
      functions, so by the subspace test we only need nonemptiness (the zero function solves
      the equation) and closure under combinations, which holds because differentiation is
      linear: $(c_1f + c_2g)' + 2(c_1f+c_2g) = c_1(f'+2f) + c_2(g'+2g) = 0$."
      Hint (hidden := true) "`linear_combination c₁ * {hf} x + c₂ * {hg} x`"
      linear_combination c₁ * hf x + c₂ * hg x

end LinearAlgebraGame

Conclusion "
The solution set of a *homogeneous linear* equation is always a subspace — whether the
equation is $A\\vec x = \\vec 0$ or $f' + 2f = 0$.
"

DisabledTactic simp
TheoremTab "Subspaces"
NewTheorem differentiable_const LinearAlgebraGame.differentiable_comb LinearAlgebraGame.deriv_comb deriv_const Pi.zero_def MulZeroClass.mul_zero
