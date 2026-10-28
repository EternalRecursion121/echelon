import Game.Levels.Independence.L06_FunctionsB

World "Independence"
Level 7
Title "u, u+v, u+v+w"

-- @sheet 3 Q6
/-! @answer
Suppose $a\vec u + b(\vec u + \vec v) + c(\vec u + \vec v + \vec w) = \vec 0$. Regrouping,
$(a + b + c)\vec u + (b + c)\vec v + c\vec w = \vec 0$. Since $\{\vec u, \vec v, \vec w\}$ is
independent, $a + b + c = 0$, $b + c = 0$ and $c = 0$; hence $c = 0$, $b = 0$, $a = 0$. So
only the trivial relation holds and $\{\vec u, \vec u + \vec v, \vec u + \vec v + \vec w\}$
is independent.
-/
Introduction "
**Problem Sheet 3, Question 6.** Show that if the set $\\{\\vec u, \\vec v, \\vec w\\}$ is
linearly independent then so is the set $\\{\\vec u, \\vec u + \\vec v, \\vec u + \\vec v + \\vec w\\}$.
"

namespace LinearAlgebraGame

/-- If $\vec u, \vec v, \vec w$ are independent, so are
$\vec u, \vec u + \vec v, \vec u + \vec v + \vec w$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (u v w : V)
    (h : LinearIndependent ℝ ![u, v, w]) : LinearIndependent ℝ ![u, u + v, u + v + w] := by
  Hint "Take a relation among the new vectors and regroup it as a relation among
  $\\vec u, \\vec v, \\vec w$."
  rw [linIndep_three_iff] at h ⊢
  intro a b c hrel
  Hint (hidden := true) "`have key : (a + b + c) • u + (b + c) • v + c • w = 0 := by rw [← {hrel}]; module`"
  have key : (a + b + c) • u + (b + c) • v + c • w = 0 := by
    rw [← hrel]
    module
  Hint (hidden := true) "`obtain ⟨h1, h2, h3⟩ := {h} _ _ _ {key}`, then `linarith` for each part."
  obtain ⟨h1, h2, h3⟩ := h _ _ _ key
  refine ⟨?_, ?_, h3⟩
  · linarith
  · linarith

end LinearAlgebraGame

Conclusion "
The new vectors are the old ones times an upper-triangular matrix with $1$s on the diagonal —
a theme that returns with change of basis.
"

TheoremTab "Independence"
