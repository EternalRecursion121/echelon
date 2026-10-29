import Game.Levels.Puzzles.L03_Library

World "Puzzles"
Level 4
Title "The rope"

-- @sheet 5 Q6
/-! @answer
If the earth's radius is $R$, the snug rope has length $2\pi R$; raised $2$ m all round it is a
circle of radius $R + 2$, of length $2\pi(R+2)$. The extra rope is
$2\pi(R + 2) - 2\pi R = 4\pi \approx 12.6$ m — **independent of $R$** (the same for a football).
-/
Introduction "
**Problem Sheet 5, Question 6 (optional).** Imagine a rope wound around the earth's equator so
that it fits snugly (suppose that the earth is a sphere). How much extra rope must we add so
that around the entire world the rope will now be 2m off the ground?

The claim: there is one amount $L$ that works whatever the radius $R$ is.
"

namespace LinearAlgebraGame

/-- There is an $L$ with $2\pi(R+2) - 2\pi R = L$ for every radius $R$. -/
Statement : ∃ L : ℝ, ∀ R : ℝ, 2 * Real.pi * (R + 2) - 2 * Real.pi * R = L := by
  Hint "Expand the difference. Does $R$ survive?"
  Hint (hidden := true) "`use 4 * Real.pi`, `intro R`, `ring`."
  use 4 * Real.pi
  intro R
  ring

end LinearAlgebraGame

Conclusion "**Answer:** $4\\pi \\approx 12.6$ m, whatever the size of the planet."
