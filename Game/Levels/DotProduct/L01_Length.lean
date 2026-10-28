import Game.Metadata
import Game.Ch1

World "DotProduct"
Level 1
Title "Dot product and length"

Introduction "
The dot product of $\\vec u, \\vec v \\in \\mathbb R^n$ is $\\vec u \\cdot \\vec v = \\sum_i u_i v_i$,
written `u ⬝ᵥ v`. Hefferon's length is $|\\vec v| = \\sqrt{\\vec v \\cdot \\vec v}$; in this game
it is `len v` (Lean's own `‖v‖` on `Fin n → ℝ` is a different, \"max\" norm, so we avoid it).

`rw [len]` unfolds the definition.
"

namespace LinearAlgebraGame

/-- $\left|\begin{pmatrix}3\\4\end{pmatrix}\right| = 5$. -/
Statement : len ![3, 4] = 5 := by
  Hint "Unfold `len`, then compute $3\\cdot 3 + 4 \\cdot 4$."
  Hint (hidden := true) "`rw [len]`, then `norm_num [dotProduct, Fin.sum_univ_two]`."
  rw [len]
  norm_num [dotProduct, Fin.sum_univ_two]

end LinearAlgebraGame

Conclusion "$\\sqrt{9 + 16} = 5$: Pythagoras."

NewDefinition LinearAlgebraGame.len
TheoremTab "Dot"
