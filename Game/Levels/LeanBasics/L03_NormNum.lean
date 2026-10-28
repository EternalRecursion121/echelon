import Game.Levels.LeanBasics.L02_Rewrite

World "LeanBasics"
Level 3
Title "The calculator"

Introduction "
`norm_num` does arithmetic with explicit numbers: it proves `2 + 2 = 4` or that
`(3 : ℝ) ≠ 5`. It is a calculator, not a mathematician. Some worlds switch it off when
it would do the interesting part of the work for you.
"

/-- If $x = 2$ then $x + x = 4$. -/
Statement (x : ℝ) (h : x = 2) : x + x = 4 := by
  Hint "First get rid of `x` with `rw`, then let `norm_num` add up."
  rw [h]
  norm_num

NewTactic norm_num
