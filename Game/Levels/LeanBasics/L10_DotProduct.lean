import Game.Levels.LeanBasics.L09_VectorEq

World "LeanBasics"
Level 10
Title "The dot product"

Introduction "
The dot product $u \\cdot v = u_0 v_0 + u_1 v_1 + \\dots$ is written `u ⬝ᵥ v` in Lean.

When every entry is a number, `norm_num` computes a dot product by itself.

When the entries are letters (later: `![x, y] ⬝ᵥ …`), `norm_num` needs to be told to look
inside the definition. Put the names it should unfold in square brackets:
`norm_num [dotProduct, Fin.sum_univ_two]` unfolds `⬝ᵥ` into a sum, and
`Fin.sum_univ_two` says a sum over two positions is (entry 0) + (entry 1). Keep this
recipe in mind — you will need it in Row Ops.

**Typing:** `⬝ᵥ` is `\\tr` then `\\_v`.
"

open Matrix in
/-- $(1, 2) \cdot (3, 4) = 11$. -/
Statement : (![1, 2] : Fin 2 → ℝ) ⬝ᵥ ![3, 4] = 11 := by
  Hint "Add up $1 \\cdot 3 + 2 \\cdot 4$: the entries are all numbers, so the calculator can do it."
  Hint (hidden := true) "`norm_num` (or, writing the sum out yourself, `norm_num [dotProduct, Fin.sum_univ_two]`)"
  norm_num

/-- `u ⬝ᵥ v`: the dot product. -/
DefinitionDoc dotProduct as "⬝ᵥ"
/-- $\sum_{i<2} f(i) = f(0) + f(1)$. -/
TheoremDoc Fin.sum_univ_two as "Fin.sum_univ_two" in "Vectors"
NewTheorem Fin.sum_univ_two
NewDefinition dotProduct
