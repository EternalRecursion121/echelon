import Game.Levels.Echelon.L13_SheetTwoQ8c

World "Echelon"
Level 14
Title "Homogeneous solutions"

-- @sheet 2 Q4
/-! @answer
If $A\vec s = \vec 0$ and $A\vec t = \vec 0$ then (a) $A(\vec s + \vec t) = A\vec s + A\vec t
= \vec 0$; (b) $A(3\vec s) = 3A\vec s = \vec 0$; (c) $A(k\vec s + m\vec t) = kA\vec s + mA\vec t
= \vec 0$.

**What's wrong with the argument:** the three facts only produce *new* solutions if we start
from a nonzero one. Every homogeneous system has the solution $\vec 0$, and sums and
multiples of $\vec 0$ are just $\vec 0$ again. So the argument proves nothing for a system
whose only solution is $\vec 0$ — and such systems exist, e.g. $x = 0, y = 0$ (any
nonsingular system). The correct conclusion is "one solution or infinitely many".
-/
Introduction "
**Problem Sheet 2, Question 4.** Prove that if $\\vec s$ and $\\vec t$ satisfy a homogeneous
system then so do these vectors: (a) $\\vec s + \\vec t$, (b) $3\\vec s$,
(c) $k\\vec s + m\\vec t$ for $k, m \\in \\mathbb{R}$.

What's wrong with this argument: *\"These three show that if a homogeneous system has one
solution then it has many solutions — any multiple of a solution is another solution, and
any sum of solutions is a solution also — so there are no homogeneous systems with exactly
one solution.\"*?

The last part of the statement is the formal core of the answer: a homogeneous system whose
**only** solution is $\\vec 0$. Also write your explanation of the flaw as a comment
starting `-- Explain:` inside your proof.

Multiplying by $A$ respects sums and scalar multiples: `mulVec_add` says
$A(\\vec s + \\vec t) = A\\vec s + A\\vec t$, `mulVec_smul` says $A(k\\vec s) = k(A\\vec s)$.
To tidy up, `add_zero` ($\\vec v + \\vec 0 = \\vec v$) and `smul_zero` ($k\\vec 0 = \\vec 0$);
and `one_mulVec` says $I\\vec x = \\vec x$.
"

namespace LinearAlgebraGame

open Matrix in
/-- Solutions of $A\vec x = \vec 0$ are closed under sums, multiples and combinations; yet some
homogeneous system has only the solution $\vec 0$. -/
Statement {m n : ℕ} (A : Matrix (Fin m) (Fin n) ℝ) (s t : Fin n → ℝ)
    (hs : A *ᵥ s = 0) (ht : A *ᵥ t = 0) :
    A *ᵥ (s + t) = 0 ∧ A *ᵥ ((3 : ℝ) • s) = 0 ∧ (∀ k m : ℝ, A *ᵥ (k • s + m • t) = 0) ∧
      ∃ B : Matrix (Fin 2) (Fin 2) ℝ, ∀ x, B *ᵥ x = 0 ↔ x = 0 := by
  Hint "Multiplying by $A$ respects sums and scalar multiples."
  refine ⟨?_, ?_, ?_, ?_⟩
  · Hint (hidden := true) "`rw [mulVec_add, {hs}, {ht}, add_zero]`"
    rw [mulVec_add, hs, ht, add_zero]
  · Hint (hidden := true) "`rw [mulVec_smul, {hs}, smul_zero]`"
    rw [mulVec_smul, hs, smul_zero]
  · intro k m
    rw [mulVec_add, mulVec_smul, mulVec_smul, hs, ht, smul_zero, smul_zero, add_zero]
  · Hint "Find a $2\\times 2$ homogeneous system with exactly one solution."
    Hint (hidden := true) "The identity matrix: `use 1`, `intro x`, `rw [one_mulVec]`."
    use 1
    intro x
    Hint (hidden := true) "Model explanation: every homogeneous system has the solution
    $\\vec 0$, and sums and multiples of $\\vec 0$ are $\\vec 0$. The argument only
    produces new solutions if one starts from a nonzero solution, which need not exist
    (e.g. $x = 0, y = 0$)."
    rw [one_mulVec]

end LinearAlgebraGame

Conclusion "
The flaw: starting from the solution $\\vec 0$, sums and multiples give only $\\vec 0$.
So: one solution, or infinitely many — you will prove exactly this with vector spaces in Sheet 3 Q3(d).
"

DisabledTactic simp norm_num
TheoremTab "Matrices"
NewTheorem Matrix.mulVec_add Matrix.one_mulVec add_zero smul_zero
