import Game.Levels.Axioms.L01_ZeroSmul

World "Axioms"
Level 2
Title "Inverses are unique"

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

Decide what you believe, then prove it. Suppose $w$ and $w'$ are both inverses of $v$.
"

namespace LinearAlgebraGame

/-- If $w$ and $w'$ are both additive inverses of $v$, then $w = w'$. -/
Statement neg_unique {V : Type*} [AddCommGroup V] [Module ℝ V] (v w w' : V)
    (hw : w + v = 0) (hw' : v + w' = 0) : w = w' := by
  Hint "Write $w = w + 0 = w + (v + w') = (w + v) + w' = 0 + w' = w'$.
  A `calc` block lets you write exactly that chain."
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

/-- $(a + b) + c = a + (b + c)$ — Hefferon's condition (3). -/
TheoremDoc add_assoc as "add_assoc" in "Axioms"
/-- $\vec 0 + v = v$. -/
TheoremDoc zero_add as "zero_add" in "Axioms"
/-- `calc` writes a chain of equalities, each with its own justification. -/
TacticDoc «calc»

NewTactic «calc»
NewTheorem add_assoc zero_add
/-- disabled -/
TheoremDoc neg_eq_of_add_eq_zero_right as "neg_eq_of_add_eq_zero_right" in "Axioms"
/-- disabled -/
TheoremDoc neg_eq_of_add_eq_zero_left as "neg_eq_of_add_eq_zero_left" in "Axioms"
DisabledTheorem neg_eq_of_add_eq_zero_right neg_eq_of_add_eq_zero_left
DisabledTactic norm_num
