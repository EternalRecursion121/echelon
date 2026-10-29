import Game.Levels.BasisDim.L03_P2Standard

World "BasisDim"
Level 4
Title "Must every basis have every degree?"

-- @sheet 3 Q7
/-! @answer
**No**, a basis of $\mathcal P_2$ need not contain a polynomial of each degree. For example
$\langle x^2,\ x^2 + x,\ x^2 + x + 1\rangle$ is a basis — every element has degree 2.
It spans: $a_0 + a_1x + a_2x^2 = (a_2 - a_1)\,x^2 + (a_1 - a_0)(x^2 + x) + a_0(x^2+x+1)$;
and the representation is unique, since comparing constant, $x$ and $x^2$ coefficients of
$c_1x^2 + c_2(x^2+x) + c_3(x^2+x+1)$ gives $c_3 = a_0$, $c_2 + c_3 = a_1$,
$c_1 + c_2 + c_3 = a_2$. By Theorem 1.12 it is a basis.
-/
Introduction "
**Problem Sheet 3, Question 7** (second half). Must any basis of $\\mathcal P_2$ contain a
polynomial of each degree: degree zero, degree one, and degree two?

`p.HasDegree d` says $p$ has degree exactly $d$: its coefficient `p d` is nonzero and all
higher coefficients vanish.

This is a *decide* level, of the form `¬ P ∨ P`: commit with `left` (no, not every basis
must) or `right` (yes, every basis must), then prove your choice.
"

namespace LinearAlgebraGame

/-- Decide whether every basis of $\mathcal P_2$ contains a polynomial of each degree $0, 1, 2$. -/
Statement :
    (¬ ∀ v : Fin 3 → Poly 2, IsBasisOf v ⊤ → ∀ d : Fin 3, ∃ i, (v i).HasDegree d) ∨
      (∀ v : Fin 3 → Poly 2, IsBasisOf v ⊤ → ∀ d : Fin 3, ∃ i, (v i).HasDegree d) := by
  Hint "Decide first. Experiment on paper: write down a few bases of $\\mathcal P_2$ other than
  $\\langle 1, x, x^2\\rangle$ and look at the degrees that occur."
  left
  Hint "To refute a \"for all\", assume it (`intro h`) and feed it an example of your choice."
  intro h
  Hint (hidden := true) "Try $\\langle x^2, x^2 + x, x^2 + x + 1\\rangle$, i.e.
  `have hB := {h} ![![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] ?_` (the `?_` leaves \"it is a basis\"
  as a second goal)."
  have hB := h ![![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] ?_
  · Hint (hidden := true) "Which element could have degree $0$? Ask the hypothesis:
    `obtain ⟨i, -, hi⟩ := hB 0`."
    obtain ⟨i, -, hi⟩ := hB 0
    Hint (hidden := true) "Its $x^2$ coefficient must vanish: `have := {hi} 2 (by simp)`,
    then `fin_cases {i}` and `simp at this`."
    have := hi 2 (by simp)
    fin_cases i <;> simp at this
  · Hint "Now prove your sequence is a basis, with Theorem 1.12."
    rw [isBasisOf_top_iff]
    intro x
    Hint (hidden := true) "The coefficients of $a_0 + a_1x + a_2x^2$ are
    $(a_2 - a_1,\\ a_1 - a_0,\\ a_0)$: `refine ⟨![x 2 - x 1, x 1 - x 0, x 0], ?_, ?_⟩`."
    refine ⟨![x 2 - x 1, x 1 - x 0, x 0], ?_, ?_⟩
    · Hint (hidden := true) "`entrywise <;> simp [Fin.sum_univ_three]`"
      entrywise <;> simp [Fin.sum_univ_three]
    · intro c hc
      Hint "Compare coordinates one at a time."
      have h0 := congrFun hc 0
      have h1 := congrFun hc 1
      have h2 := congrFun hc 2
      simp [Fin.sum_univ_three] at h0 h1 h2
      Hint (hidden := true) "`funext i; fin_cases i <;> simp <;> linarith`"
      funext i
      fin_cases i <;> simp <;> linarith

end LinearAlgebraGame

Conclusion "
**Answer: no.** $\\langle x^2, x^2+x, x^2+x+1\\rangle$ is a basis of $\\mathcal P_2$ with
every element of degree 2.
"

TheoremTab "Basis"
NewDefinition LinearAlgebraGame.Poly.HasDegree
