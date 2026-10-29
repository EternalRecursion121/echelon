import Game.Levels.Independence.L05_FunctionsA

World "Independence"
Level 6
Title "Squares of sine and cosine"

-- @sheet 3 Q5b
/-! @answer
**Dependent.** For every $x$, $\sin^2 x + \cos^2 x = 1$, so
$$-2\cdot h(x) + 1\cdot i(x) + 4\cdot j(x) = -4 + 4\sin^2x + 4\cos^2x = 0.$$
This is a nontrivial linear relation among $h, i, j$.
-/
Introduction "
**Problem Sheet 3, Question 5(b).** (Functions $\\mathbb{R}^+ \\to \\mathbb{R}$.) Is
$\\{h, i, j\\}$ linearly independent, where $h(x) = 2$, $i(x) = 4\\sin^2(x)$ and
$j(x) = \\cos^2(x)$?

New tactic: `funext x` proves two functions equal by proving they agree at every `x`.

Three vectors: `linIndep_three_iff` (now unlocked) says
`LinearIndependent ℝ ![u, v, w] ↔ ∀ a b c, a • u + b • v + c • w = 0 → a = 0 ∧ b = 0 ∧ c = 0`.

Decide: `left` for dependent, `right` for independent.
"

namespace LinearAlgebraGame

/-- Are $2$, $4\sin^2 x$ and $\cos^2 x$ linearly independent on $\mathbb{R}^+$? -/
Statement : (¬ LinearIndependent ℝ ![(fun _ : PosReal => (2 : ℝ)),
      (fun x : PosReal => 4 * Real.sin x.1 ^ 2), (fun x : PosReal => Real.cos x.1 ^ 2)]) ∨
    LinearIndependent ℝ ![(fun _ : PosReal => (2 : ℝ)),
      (fun x : PosReal => 4 * Real.sin x.1 ^ 2), (fun x : PosReal => Real.cos x.1 ^ 2)] := by
  Hint "Decide first. Test it: look for numbers $a, b, c$, not all zero, with
  $2a + 4b\\sin^2 x + c\\cos^2 x = 0$ for every $x$ — or show none exist."
  Hint (hidden := true) "Which famous identity links $\\sin^2$, $\\cos^2$ and a constant?
  `Real.sin_sq_add_cos_sq x : sin x ^ 2 + cos x ^ 2 = 1`."
  left
  rw [linIndep_three_iff]
  intro h
  Hint (hidden := true) "State the relation:
  `have hrel : (-2 : ℝ) • (fun _ : PosReal => (2 : ℝ)) + (1 : ℝ) • (fun x : PosReal => 4 * Real.sin x.1 ^ 2) + (4 : ℝ) • (fun x : PosReal => Real.cos x.1 ^ 2) = 0`."
  have hrel : (-2 : ℝ) • (fun _ : PosReal => (2 : ℝ)) +
      (1 : ℝ) • (fun x : PosReal => 4 * Real.sin x.1 ^ 2) +
      (4 : ℝ) • (fun x : PosReal => Real.cos x.1 ^ 2) = 0 := by
    Hint (hidden := true) "`funext x`, `simp`, then
    `linear_combination 4 * Real.sin_sq_add_cos_sq x.1`."
    funext x
    simp
    linear_combination 4 * Real.sin_sq_add_cos_sq x.1
  Hint (hidden := true) "`have h1 := {h} _ _ _ {hrel}` and `norm_num at h1`."
  have h1 := h _ _ _ hrel
  norm_num at h1

end LinearAlgebraGame

Conclusion "**Answer: dependent**: $-2h + i + 4j = 0$."

TheoremTab "Independence"
NewTheorem LinearAlgebraGame.linIndep_three_iff
NewTactic funext
