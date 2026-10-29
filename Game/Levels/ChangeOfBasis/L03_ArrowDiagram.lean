import Game.Levels.ChangeOfBasis.L02_FindBases

World "ChangeOfBasis"
Level 3
Title "The arrow diagram"

-- @sheet 8 Q5
/-! @answer
Arrow diagram: $V_{\hat B} \xrightarrow{\mathrm{id}} V_B \xrightarrow{t} W_D \xrightarrow{\mathrm{id}} W_{\hat D}$,
so $\mathrm{Rep}_{\hat B,\hat D}(t) = P\,H\,Q$ with $Q = \mathrm{Rep}_{\hat B,B}(\mathrm{id})$ and
$P = \mathrm{Rep}_{D,\hat D}(\mathrm{id})$. For $Q$, write $\hat B = \mathcal E_2$ in terms of $B$:
$\vec e_1 = 1\cdot(1,0) + 0\cdot(1,1)$, $\vec e_2 = -1\cdot(1,0) + 1\cdot(1,1)$, so
$Q = \begin{pmatrix}1&-1\\0&1\end{pmatrix}$. For $P$, write $D$ in terms of $\hat D$:
$(0,1) = 0\cdot(1,-1) + 1\cdot(0,1)$ and $(-1,0) = -1\cdot(1,-1) - 1\cdot(0,1)$, so
$P = \begin{pmatrix}0&-1\\1&-1\end{pmatrix}$.
-/
Introduction "
**Problem Sheet 8, Question 5.** Find the change of basis matrices $Q$ and $P$ that will
convert the representation of a transformation $t : \\mathbb R^2 \\to \\mathbb R^2$ with respect
to $B, D$ to one with respect to $\\hat B, \\hat D$. Draw the arrow diagram first.
$$B = \\langle (1,0), (1,1)\\rangle,\\quad D = \\langle (0,1), (-1,0)\\rangle,\\quad
\\hat B = \\mathcal E_2,\\quad \\hat D = \\langle (1,-1), (0,1)\\rangle.$$

**The arrow diagram.** Going round the square the long way — up the left side, along the top,
down the right — gives the same map as the bottom edge:
$$\\begin{array}{ccc}
V_B & \\xrightarrow[\\;H\\;]{t} & W_D \\\\
{\\scriptstyle\\mathrm{id}}\\big\\uparrow{\\scriptstyle Q} & & \\big\\downarrow{\\scriptstyle P}\\,{\\scriptstyle\\mathrm{id}} \\\\
V_{\\hat B} & \\xrightarrow[\\;\\hat H\\;]{t} & W_{\\hat D}
\\end{array}
\\qquad Q = \\mathrm{Rep}_{\\hat B,B}(\\mathrm{id}),\\quad P = \\mathrm{Rep}_{D,\\hat D}(\\mathrm{id}),\\quad \\hat H = PHQ.$$
(Read $\\hat H = PHQ$ right to left: first $Q$, then $H$, then $P$.)

In Lean: find $P$, $Q$ such that **whenever** $H$ represents $t$ with respect to $B, D$, the
matrix $PHQ$ represents $t$ with respect to $\\hat B, \\hat D$. The statement names the bases
`B`, `D` and `D'` (for $\\hat D$; $\\hat B$ is `stdBasis 2`), so you can write e.g.
`IsRep (stdBasis 2) B LinearMap.id Q` — and unfold the names with `simp [B]`. Your
`isRep_comp` from the Matrix of a Map world composes arrows.

(If you ever type a basis out in full instead, give its type:
`(![![0, 1], ![-1, 0]] : Fin 2 → Fin 2 → ℝ)`. Without it Lean guesses integer entries and
complains `failed to synthesize Module ℝ (Fin (Nat.succ 0).succ → ℤ)`.)
"

namespace LinearAlgebraGame

/-- There are $P$, $Q$ with $\mathrm{Rep}_{\hat B,\hat D}(t) = P\,\mathrm{Rep}_{B,D}(t)\,Q$
for every $t$. -/
Statement :
    let B : Fin 2 → (Fin 2 → ℝ) := ![![1, 0], ![1, 1]]
    let D : Fin 2 → (Fin 2 → ℝ) := ![![0, 1], ![-1, 0]]
    let D' : Fin 2 → (Fin 2 → ℝ) := ![![1, -1], ![0, 1]]
    ∃ P Q : Matrix (Fin 2) (Fin 2) ℝ, ∀ (t : (Fin 2 → ℝ) →ₗ[ℝ] (Fin 2 → ℝ))
      (H : Matrix (Fin 2) (Fin 2) ℝ), IsRep B D t H → IsRep (stdBasis 2) D' t (P * H * Q) := by
  Hint "Draw $\\hat B \\to B \\to D \\to \\hat D$: first $\\mathrm\{id}$, then $t$, then $\\mathrm\{id}$.
  $Q$ represents the first arrow and $P$ the last."
  Hint (hidden := true) "`use !![0, -1; 1, -1], !![1, -1; 0, 1]`"
  use !![0, -1; 1, -1], !![1, -1; 0, 1]
  intro t H hH
  Hint (hidden := true) "State the two change-of-basis facts as `have`s, e.g.
  `have hQ : IsRep (stdBasis 2) B LinearMap.id !![1, -1; 0, 1]`."
  Hint "Each matrix represents the identity map with respect to a pair of bases. Check those two facts, then compose the three arrows."
  have hQ : IsRep (stdBasis 2) B LinearMap.id !![1, -1; 0, 1] := by
    Hint (hidden := true) "`intro j`, then `fin_cases j <;> entrywise <;> simp [B, stdBasis]`."
    intro j
    fin_cases j <;> entrywise <;> simp [B, stdBasis]
  have hP : IsRep D D' LinearMap.id !![0, -1; 1, -1] := by
    intro j
    fin_cases j <;> entrywise <;> simp [D, D']
  Hint (hidden := true) "Compose: `have h := isRep_comp (isRep_comp hQ {hH}) hP`."
  have h := isRep_comp (isRep_comp hQ hH) hP
  Hint (hidden := true) "Tidy with `rw [LinearMap.comp_id, LinearMap.id_comp] at h`, then
  `rw [Matrix.mul_assoc]` and `exact h`."
  rw [LinearMap.comp_id, LinearMap.id_comp] at h
  rw [Matrix.mul_assoc]
  exact h

end LinearAlgebraGame

Conclusion "
$Q = \\mathrm{Rep}_{\\hat B,B}(\\mathrm{id}) = \\begin{pmatrix}1&-1\\\\0&1\\end{pmatrix}$ and
$P = \\mathrm{Rep}_{D,\\hat D}(\\mathrm{id}) = \\begin{pmatrix}0&-1\\\\1&-1\\end{pmatrix}$.
"

NewTheorem LinearMap.comp_id LinearMap.id_comp
TheoremTab "Change of basis"
