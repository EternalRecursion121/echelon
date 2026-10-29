import Game.Levels.Axioms.L02_NegUnique

World "Axioms"
Level 3
Title "Minus one times a vector"

Introduction "
Lemma Two.I.1.16 (2): $(-1)\\cdot\\vec v + \\vec v = \\vec 0$, i.e. $(-1)\\cdot\\vec v$ *is* the
additive inverse of $\\vec v$. Your two earlier theorems are now tools.

New: `nth_rw n [h]` rewrites only the `n`-th occurrence of the left side of `h` (counting from 1), when plain `rw` would rewrite the wrong one.

Reminder: `one_smul ℝ v : (1 : ℝ) • v = v` takes the scalars `ℝ` as an explicit argument.
Rewriting *backwards* with it (`← one_smul ℝ v`) turns a `v` into `1 • v`; without the
arguments Lean cannot tell which `v` to expand and complains about a \"metavariable\".
"

namespace LinearAlgebraGame

/-- $(-1)\cdot \vec v + \vec v = \vec 0$. -/
Statement neg_one_smul_add {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (-1 : ℝ) • v + v = 0 := by
  Hint (hidden := true) "Idea: write the second $v$ as $1 \\cdot v$, then combine the scalars."
  Hint (hidden := true) "`nth_rw 2 [← one_smul ℝ {v}]`, then `rw [← add_smul]`."
  nth_rw 2 [← one_smul ℝ v]
  rw [← add_smul]
  rw [neg_add_cancel]
  Hint (hidden := true) "`exact zero_smul_eq_zero {v}`"
  exact zero_smul_eq_zero v

end LinearAlgebraGame

Conclusion "Now `-v` and `(-1)•v` are interchangeable — the game will let `simp` do this from here on."

NewTactic nth_rw
DisabledTheorem neg_one_smul
DisabledTactic norm_num simp
NewTheorem neg_add_cancel LinearAlgebraGame.zero_smul_eq_zero one_smul
