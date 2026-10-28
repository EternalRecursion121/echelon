import Game.Levels.DotProduct.L08_Triangle

World "DotProduct"
Level 9
Title "The triangle inequality for n vectors"

-- @sheet 2 Q6
/-! @answer
**Yes.** By induction on $n$. For $n = 0$ both sides are $0$. If it holds for $n$, then by
the triangle inequality
$$|\vec u_1 + \dots + \vec u_{n+1}| \le |\vec u_1 + \dots + \vec u_n| + |\vec u_{n+1}|
\le |\vec u_1| + \dots + |\vec u_n| + |\vec u_{n+1}|.$$
-/
Introduction "
**Problem Sheet 2, Question 6.** Is $|\\vec u_1 + \\dots + \\vec u_n| \\le |\\vec u_1| + \\dots + |\\vec u_n|$?
If it is true then it would generalise the Triangle Inequality.

Decide with `left`/`right`. The vectors are `u 0, u 1, …` and
$\\sum_{i < n}$ is `∑ i ∈ Finset.range n`. New: `induction n with` — prove the case
`zero`, then the case `succ n ih` using the hypothesis `ih` for $n$.
"

namespace LinearAlgebraGame

/-- Is $\left|\sum_{i<n} \vec u_i\right| \le \sum_{i<n} |\vec u_i|$ for all $n$? -/
Statement : (¬ ∀ (m : ℕ) (u : ℕ → Fin m → ℝ) (n : ℕ),
      len (∑ i ∈ Finset.range n, u i) ≤ ∑ i ∈ Finset.range n, len (u i)) ∨
    (∀ (m : ℕ) (u : ℕ → Fin m → ℝ) (n : ℕ),
      len (∑ i ∈ Finset.range n, u i) ≤ ∑ i ∈ Finset.range n, len (u i)) := by
  Hint "Decide first. What does the case of two vectors say?"
  Hint (hidden := true) "It is true: argue one vector at a time (induction)."
  right
  intro m u n
  Hint (hidden := true) "`induction n with` `| zero => …` `| succ n ih => …`"
  induction n with
  | zero =>
    Hint (hidden := true) "Both sums are empty: `rw [Finset.sum_range_zero, Finset.sum_range_zero, len,
    dotProduct_zero, Real.sqrt_zero]`."
    rw [Finset.sum_range_zero, Finset.sum_range_zero, len, dotProduct_zero, Real.sqrt_zero]
  | succ n ih =>
    Hint "Split off the last vector and use the triangle inequality."
    Hint (hidden := true) "`rw [Finset.sum_range_succ, Finset.sum_range_succ]`, then
    `have h := len_add_le (∑ i ∈ Finset.range n, u i) (u n)` and `linarith`."
    rw [Finset.sum_range_succ, Finset.sum_range_succ]
    have h := len_add_le (∑ i ∈ Finset.range n, u i) (u n)
    linarith

end LinearAlgebraGame

Conclusion "**Answer: yes**, by induction from the triangle inequality."

NewTactic induction
NewTheorem Finset.sum_range_zero Finset.sum_range_succ Real.sqrt_zero
