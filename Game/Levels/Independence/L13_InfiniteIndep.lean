import Game.Levels.Independence.L12_EarlierOnes

World "Independence"
Level 13
Title "Infinitely many independent functions"

-- @sheet 4 Q8
/-! @answer
Take the "spike" functions $\delta_n$ for $n \in \mathbb{N}$: $\delta_n(x) = 1$ if $x = n$ and
$0$ otherwise. They are distinct, so $\{\delta_n\}$ is infinite. If a finite combination
$\sum_{n \in F} c_n\delta_n$ is the zero function, evaluate it at $x = m$ for $m \in F$: every
term vanishes except $c_m\delta_m(m) = c_m$, so $c_m = 0$. Hence the set is linearly
independent. (Another answer: the monomials $1, x, x^2, \ldots$.)
-/
Introduction "
**Problem Sheet 4, Question 8.** Produce an infinite linearly independent subset of the space
(under the natural operations) of all functions $f : \\mathbb{R} \\to \\mathbb{R}$.

We ask for a family $f_0, f_1, f_2, \\ldots$ indexed by $\\mathbb{N}$. An independent family
has no repeats (two equal members give the relation $f_m - f_n = 0$), so its members form an
infinite set.

For infinite families, independence is `linearIndependent_iff'`: for every finite set `s` of
indices and coefficients `g`, if $\\sum_{i \\in s} g_i f_i = 0$ then each $g_i = 0$ for $i \\in s$.
"

namespace LinearAlgebraGame

/-- There is a linearly independent sequence of functions $\mathbb{R} \to \mathbb{R}$. -/
Statement : ∃ f : ℕ → (ℝ → ℝ), LinearIndependent ℝ f := by
  Hint "Pick functions that are easy to tell apart by evaluating at a single point: \"spikes\"
  that are $1$ at $x = n$ and $0$ everywhere else."
  Hint (hidden := true) "`use fun n x => if x = n then 1 else 0`"
  use fun n x => if x = n then 1 else 0
  rw [linearIndependent_iff']
  intro s g h i hi
  Hint "Evaluate the vanishing combination at the point $x = i$."
  Hint (hidden := true) "`have h1 := congrFun {h} {i}`, then `simp [Finset.sum_apply, {hi}] at h1`."
  have h1 := congrFun h i
  simp [Finset.sum_apply, hi] at h1
  exact h1

end LinearAlgebraGame

Conclusion "
So the space of all functions is not finite-dimensional — no finite set can span it.
"

TheoremTab "Independence"
NewTheorem linearIndependent_iff' Finset.sum_apply
