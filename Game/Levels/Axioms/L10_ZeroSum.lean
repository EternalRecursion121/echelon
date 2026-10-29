import Game.Levels.Axioms.L09_PositiveQuadratics

World "Axioms"
Level 10
Title "A strange addition"

-- @sheet 3 Q2
/-! @answer
**Not a vector space**: there is no additive identity. With $\vec v \oplus \vec w = \vec 0$
for all $\vec v, \vec w$, any $\vec z$ gives $(1,0) \oplus \vec z = (0,0) \neq (1,0)$, so
condition (4) fails. (Distributivity (7) fails too: $(1+1)\cdot(1,0) = (2,0)$, but
$1\cdot(1,0) \oplus 1\cdot(1,0) = (0,0)$.)
-/
Introduction "
**Problem Sheet 3, Question 2.** Prove or disprove that $\\mathbb{R}^2$ is a vector space
under these operations:
$$\\begin{pmatrix} x_1 \\\\ y_1 \\end{pmatrix} + \\begin{pmatrix} x_2 \\\\ y_2 \\end{pmatrix}
= \\begin{pmatrix} 0 \\\\ 0 \\end{pmatrix}
\\quad\\text{and}\\quad
r\\begin{pmatrix} x \\\\ y \\end{pmatrix} = \\begin{pmatrix} rx \\\\ ry \\end{pmatrix}.$$

Vectors of $\\mathbb{R}^2$ are pairs `(x, y) : ℝ × ℝ`; `v.1` and `v.2` are the components.
Decide: `left` for \"not a vector space\", `right` for \"vector space\".
"

namespace LinearAlgebraGame

/-- Is $\mathbb{R}^2$ with $\vec v + \vec w = \vec 0$ and the usual scaling a vector space? -/
Statement : (¬ VectorSpaceAxioms (ℝ × ℝ) (fun _ _ => (0, 0)) (fun r v => (r * v.1, r * v.2))) ∨
    VectorSpaceAxioms (ℝ × ℝ) (fun _ _ => (0, 0)) (fun r v => (r * v.1, r * v.2)) := by
  Hint "Decide first: run through the conditions one by one with this strange addition. Do
  they all hold?"
  Hint (hidden := true) "Is there a vector $\\vec z$ with $\\vec v + \\vec z = \\vec v$ for every $\\vec v$?"
  left
  intro h
  Hint (hidden := true) "`obtain ⟨z, hz, hneg⟩ := {h}.has_zero_neg`"
  obtain ⟨z, hz, hneg⟩ := h.has_zero_neg
  Hint "Test `{hz}` on a vector that is not $\\vec 0$, say $(1, 0)$."
  Hint (hidden := true) "`have h1 := {hz} (1, 0)`, then compare first components:
  `have h2 := congrArg Prod.fst h1` and `norm_num at h2`."
  have h1 := hz (1, 0)
  have h2 := congrArg Prod.fst h1
  norm_num at h2

end LinearAlgebraGame

Conclusion "
**Answer: not a vector space** — no additive identity, since every sum is $(0,0)$.
"

TheoremTab "Vector spaces"
