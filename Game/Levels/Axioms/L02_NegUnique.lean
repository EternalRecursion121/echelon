import Game.Levels.Axioms.L01_ZeroSmul

World "Axioms"
Level 2
Title "Two inverses?"

-- @sheet 4 Q3
/-! @answer
**No.** Suppose $w$ and $w'$ are both additive inverses of $v$, so $w + v = \vec 0$ and
$v + w' = \vec 0$. Then, using the zero-vector, associativity and commutativity conditions,
$$w = w + \vec 0 = w + (v + w') = (w + v) + w' = \vec 0 + w' = w'.$$
So additive inverses are unique, which is what justifies writing $-v$.
-/
Introduction "
**Problem Sheet 4, Question 3.** In a vector space every element has an additive
inverse. Can some elements have two or more?

Decide what you believe before reading on. Then the statement takes two inverses $w$ and
$w'$ of the same $v$; your job is to compare them.
"

namespace LinearAlgebraGame

/-- If $w$ and $w'$ are both additive inverses of $v$, then $w = w'$. -/
Statement neg_unique {V : Type*} [AddCommGroup V] [Module ℝ V] (v w w' : V)
    (hw : w + v = 0) (hw' : v + w' = 0) : w = w' := by
  Hint "Start from $w = w + \\vec 0$ and replace $\\vec 0$ by something involving $w'$.
  A `calc` block lets you write a chain of equalities."
  Hint (hidden := true) "$w = w + 0 = w + (v + w') = (w + v) + w' = 0 + w' = w'$."
  calc w = w + 0 := by rw [add_zero]
    _ = w + (v + w') := by rw [hw']
    _ = (w + v) + w' := by rw [add_assoc]
    _ = 0 + w' := by rw [hw]
    _ = w' := by rw [zero_add]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 4 Q3: no.** If $w$ and $w'$ are both inverses of $v$ then
$w = w + (v + w') = (w + v) + w' = w'$.
"

NewTactic «calc»

DisabledTheorem neg_eq_of_add_eq_zero_right neg_eq_of_add_eq_zero_left
DisabledTactic norm_num simp
NewTheorem add_assoc zero_add
