import Game.Levels.Axioms.L06_Infinite

World "Axioms"
Level 7
Title "One or infinitely many"

-- @sheet 3 Q3d
/-! @answer
The solution set $S$ of a homogeneous system $A\vec x = \vec 0$ is nonempty (it contains
$\vec 0$) and is a vector space (it is closed under linear combinations, Sheet 2 Q4).
If $\vec 0$ is the only solution, $S$ has exactly one element. Otherwise $S$ contains some
$\vec x \neq \vec 0$, so $S$ is a nontrivial vector space and by part (c) it is infinite.
-/
Introduction "
**Problem Sheet 3, Question 3(d).** Use the fact that a nonempty solution set of a
homogeneous linear system is a vector space to draw the conclusion: the solution set has
either one element or infinitely many.

Here the system is $A\\vec x = \\vec 0$ for an $m\\times n$ matrix $A$. Since $\\vec 0$ is
always a solution, \"one element\" means the solution set is $\\{\\vec 0\\}$.

**The fact you may use.** The solution set, viewed as a vector space, is
`LinearMap.ker A.mulVecLin` (the *null space* of $A$). Two granted lemmas connect it to the set
in the statement:
- `solutionSet_infinite_iff A`: the solution set is infinite iff `Infinite (LinearMap.ker A.mulVecLin)`;
- `solution_ne_zero A hx hx0`: a solution $\\vec x$ (`hx : A *ᵥ x = 0`) with `hx0 : x ≠ 0` is a
  nonzero vector of that vector space.

So the work left is the case split, and part (c).

An underscore `_` in an argument list means \"Lean, fill this in yourself\": use it for an
argument Lean can work out from the others (e.g. the vector in `infinite_of_ne_zero _ h`).

New: `by_cases h : P` splits the proof into two cases, one with `h : P` and one with `h : ¬P`.
"

namespace LinearAlgebraGame

open Matrix in
/-- The solution set of $A\vec x = \vec 0$ is $\{\vec 0\}$ or infinite. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) :
    {x : Fin n → ℝ | A *ᵥ x = 0} = {0} ∨ Set.Infinite {x : Fin n → ℝ | A *ᵥ x = 0} := by
  Hint "Either there is a nonzero solution or there isn't. Split on that."
  Hint (hidden := true) "`by_cases h : ∃ x, A *ᵥ x = 0 ∧ x ≠ 0`"
  by_cases h : ∃ x, A *ᵥ x = 0 ∧ x ≠ 0
  · right
    obtain ⟨x, hx, hx0⟩ := h
    Hint "The null space contains a nonzero vector, so part (c) applies to it."
    Hint (hidden := true) "`rw [solutionSet_infinite_iff]`, then
    `exact infinite_of_ne_zero _ (solution_ne_zero A {hx} {hx0})`."
    rw [solutionSet_infinite_iff]
    exact infinite_of_ne_zero _ (solution_ne_zero A hx hx0)
  · left
    Hint "Two sets are equal when they have the same elements: `ext x`."
    ext x
    constructor
    · intro hx
      Hint (hidden := true) "If `{x} ≠ 0` it would be a nonzero solution, contradicting `{h}`.
      `by_contra hne` then `exact {h} ⟨{x}, {hx}, hne⟩`."
      by_contra hne
      exact h ⟨x, hx, hne⟩
    · intro hx
      Hint (hidden := true) "`rw [{hx}]` then `exact mulVec_zero A`."
      rw [hx]
      exact mulVec_zero A

end LinearAlgebraGame

Conclusion "
This is Hefferon's second proof of the \"one or infinitely many\" theorem — now with no
row reduction at all, only the vector space axioms.
"

NewTheorem LinearAlgebraGame.infinite_of_ne_zero LinearAlgebraGame.solutionSet_infinite_iff LinearAlgebraGame.solution_ne_zero
DisabledTactic norm_num simp
TheoremTab "Vector spaces"
NewDefinition LinearMap.ker
NewTactic by_cases
