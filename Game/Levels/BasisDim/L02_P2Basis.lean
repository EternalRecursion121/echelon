import Game.Levels.BasisDim.L01_BasisUnique

World "BasisDim"
Level 2
Title "A basis for 𝒫₂"

-- @sheet 3 Q7
/-! @answer
The standard basis $\langle 1, x, x^2\rangle$ is a basis of $\mathcal P_2$: every
$a_0 + a_1x + a_2x^2$ is uniquely the combination with coefficients $a_0, a_1, a_2$.

**No**, a basis need not contain a polynomial of each degree. For example
$\langle x^2,\ x^2 + x,\ x^2 + x + 1\rangle$ is a basis — every element has degree 2.
It spans: $a_0 + a_1x + a_2x^2 = (a_2 - a_1)\,x^2 + (a_1 - a_0)(x^2 + x) + a_0(x^2+x+1)$;
and the representation is unique, since comparing constant, $x$ and $x^2$ coefficients of
$c_1x^2 + c_2(x^2+x) + c_3(x^2+x+1)$ gives $c_3 = a_0$, $c_2 + c_3 = a_1$,
$c_1 + c_2 + c_3 = a_2$. By Theorem 1.12 it is a basis.
-/
Introduction "
**Problem Sheet 3, Question 7.** Find a basis for $\\mathcal P_2$, the space of all
quadratic polynomials. Must any such basis contain a polynomial of each degree: degree
zero, degree one, and degree two?

In this game $\\mathcal P_2$ is `Poly 2`: a polynomial $a_0 + a_1x + a_2x^2$ is stored as its
coefficient vector `![a₀, a₁, a₂]`. `p.HasDegree d` says $p$ has degree exactly $d$.

The goal has two parts: first show the standard basis $\\langle 1, x, x^2\\rangle$ is a
basis; then the *decide* part, of the form `¬ P ∨ P`: commit with `left` (no, not every
basis must) or `right` (yes), then prove your choice.
"

namespace LinearAlgebraGame

/-- $\langle 1, x, x^2\rangle$ is a basis of $\mathcal P_2$; and decide whether every basis of
$\mathcal P_2$ contains a polynomial of each degree $0, 1, 2$. -/
Statement :
    IsBasisOf (![![1, 0, 0], ![0, 1, 0], ![0, 0, 1]] : Fin 3 → Poly 2) ⊤ ∧
    ((¬ ∀ v : Fin 3 → Poly 2, IsBasisOf v ⊤ → ∀ d : Fin 3, ∃ i, (v i).HasDegree d) ∨
      (∀ v : Fin 3 → Poly 2, IsBasisOf v ⊤ → ∀ d : Fin 3, ∃ i, (v i).HasDegree d)) := by
  Hint "Use Theorem 1.12 (unique representation) for the first part: for each $x$, give the
  coefficients and show they are the only ones."
  constructor
  · rw [isBasisOf_top_iff]
    intro x
    Hint (hidden := true) "The coefficients of $x$ in the standard basis are $x$ itself:
    `refine ⟨x, ?_, ?_⟩`."
    refine ⟨x, ?_, ?_⟩
    · Hint (hidden := true) "`ext i`, `fin_cases i`, then `simp [Fin.sum_univ_three]`."
      ext i
      fin_cases i <;> simp [Fin.sum_univ_three]
    · intro c hc
      Hint (hidden := true) "Read off each coordinate of `{hc}`: `funext i`, `fin_cases i`,
      then `simp [← {hc}, Fin.sum_univ_three]`."
      funext i
      fin_cases i <;> simp [← hc, Fin.sum_univ_three]
  · Hint "Decide. Can you think of a basis of $\\mathcal P_2$ in which every element has
    degree 2?"
    left
    intro h
    Hint (hidden := true) "Try $\\langle x^2, x^2 + x, x^2 + x + 1\\rangle$, i.e.
    `have hB := {h} ![![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] ?_`."
    have hB := h ![![0, 0, 1], ![0, 1, 1], ![1, 1, 1]] ?_
    · Hint "Which element could have degree $0$? Ask the hypothesis for one."
      obtain ⟨i, -, hi⟩ := hB 0
      Hint (hidden := true) "Its $x^2$ coefficient must vanish: `have := {hi} 2 (by simp)`,
      then `fin_cases {i}` and `simp at this`."
      have := hi 2 (by simp)
      fin_cases i <;> simp at this
    · Hint "Now prove it is a basis. With Theorem 1.12: the coefficients of
      $a_0 + a_1x + a_2x^2$ are $(a_2 - a_1,\\ a_1 - a_0,\\ a_0)$."
      rw [isBasisOf_top_iff]
      intro x
      refine ⟨![x 2 - x 1, x 1 - x 0, x 0], ?_, ?_⟩
      · Hint (hidden := true) "`ext i; fin_cases i <;> simp [Fin.sum_univ_three]`"
        ext i
        fin_cases i <;> simp [Fin.sum_univ_three]
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

NewTheorem LinearAlgebraGame.isBasisOf_top_iff
TheoremTab "Basis"
NewDefinition LinearAlgebraGame.Poly.HasDegree LinearAlgebraGame.Poly
