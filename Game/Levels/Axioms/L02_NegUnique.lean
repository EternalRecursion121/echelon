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

This is a *decide* level: `right` claims \"no — any two inverses of the same $v$ are equal\",
`left` claims \"yes — some $v$ has two different inverses\". Commit, then prove your claim.
"

namespace LinearAlgebraGame

/-- Must two additive inverses of the same vector be equal? -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] :
    (¬ ∀ v w w' : V, w + v = 0 → v + w' = 0 → w = w') ∨
      ∀ v w w' : V, w + v = 0 → v + w' = 0 → w = w' := by
  Hint "Decide first. Take two inverses $w$, $w'$ of the same $v$ and try to compare them —
  or look for an example where they differ."
  right
  intro v w w' hw hw'
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
