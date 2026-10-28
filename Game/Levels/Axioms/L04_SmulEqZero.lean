import Game.Levels.Axioms.L03_NegOneSmul

World "Axioms"
Level 4
Title "When is r · v zero?"

-- @sheet 3 Q3a
/-! @answer
Let $\vec v \neq \vec 0$.
($\Leftarrow$) If $r = 0$ then $r\cdot\vec v = 0\cdot\vec v = \vec 0$ by Lemma Two.I.1.16.
($\Rightarrow$) Suppose $r\cdot\vec v = \vec 0$ but $r \neq 0$. Then $r^{-1}$ exists and
$$\vec v = 1\cdot\vec v = (r^{-1}r)\cdot\vec v = r^{-1}\cdot(r\cdot\vec v) = r^{-1}\cdot\vec 0 = \vec 0,$$
contradicting $\vec v \neq \vec 0$. Hence $r = 0$.
-/
Introduction "
**Problem Sheet 3, Question 3.** Using the idea of a vector space we can reprove that the
solution set of a homogeneous linear system has either one element or infinitely many
elements. Assume that $\\vec v \\in V$ is not $\\vec 0$.

**(a)** Prove that $r \\cdot \\vec v = \\vec 0$ if and only if $r = 0$.

Parts (a)–(d) are levels 4–7 of this world; each part may use the previous ones.
"

namespace LinearAlgebraGame

/-- If $\vec v \neq \vec 0$ then $r\cdot\vec v = \vec 0$ if and only if $r = 0$. -/
Statement smul_eq_zero_iff_of_ne {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V)
    (hv : v ≠ 0) (r : ℝ) : r • v = 0 ↔ r = 0 := by
  Hint "Two directions. The interesting one: if $r \\neq 0$ you may divide by $r$."
  constructor
  · intro h
    Hint "Argue by contradiction: suppose $r \\neq 0$. Then $\\vec v = r^\{-1}\\cdot(r\\cdot\\vec v)$."
    Hint (hidden := true) "`by_contra hr` assumes `hr : ¬ r = 0` and asks for `False`.
    Then `apply {hv}` turns the goal into `{v} = 0`."
    by_contra hr
    apply hv
    Hint (hidden := true) "A `calc` chain: `{v} = (1:ℝ) • {v}`, `_ = (r⁻¹ * r) • {v}`,
    `_ = r⁻¹ • (r • {v})`, `_ = 0`. The lemmas are `one_smul`, `inv_mul_cancel₀ {hr}`,
    `smul_smul` and `smul_zero`."
    calc v = (1 : ℝ) • v := by rw [one_smul]
      _ = (r⁻¹ * r) • v := by rw [inv_mul_cancel₀ hr]
      _ = r⁻¹ • (r • v) := by rw [smul_smul]
      _ = 0 := by rw [h, smul_zero]
  · intro h
    Hint (hidden := true) "Rewrite with `{h}`, then use your level-1 theorem `zero_smul_eq_zero`."
    rw [h]
    exact zero_smul_eq_zero v

end LinearAlgebraGame

Conclusion "
The key step is the one Hefferon uses: a nonzero scalar can be undone by multiplying by its
inverse. Note where $\\vec v \\neq \\vec 0$ was used — only to reach the contradiction.
"

DisabledTheorem smul_eq_zero smul_eq_zero_iff_left smul_eq_zero_iff_right smul_ne_zero_iff smul_left_injective smul_right_injective smul_left_inj smul_right_inj
DisabledTactic norm_num simp
TheoremTab "Vector spaces"
NewTactic by_contra
NewTheorem inv_mul_cancel₀ smul_zero smul_smul
