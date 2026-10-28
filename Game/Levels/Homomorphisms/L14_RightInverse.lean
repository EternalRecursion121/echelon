import Game.Levels.Homomorphisms.L13_RankOne

World "Homomorphisms"
Level 14
Title "Right inverses"

-- @sheet 8 Q3
/-! @answer
**No.** Let $g : \mathbb R^2 \to \mathbb R$, $g(x,y) = x$; it is linear and surjective. Let
$f : \mathbb R \to \mathbb R^2$, $f(x) = (x, x^2)$. Then $g(f(x)) = x$, so $f$ is a right inverse
of $g$. But $f$ is not linear: $f(2\cdot 1) = (2,4)$ while $2\cdot f(1) = (2,2)$.
(Linear right inverses do exist — e.g. $x \mapsto (x,0)$ — but a right inverse need not be one.)
-/
Introduction "
**Problem Sheet 8, Question 3.** Assume that $g : V \\to W$ is linear and surjective. If
$f : W \\to V$ is a left inverse of $g$ then $f$ must be linear (Theorem 2.20). Now suppose
instead that $f : W \\to V$ is a right inverse of $g$ (that is, $g(f(\\vec w)) = \\vec w$ for all
$\\vec w$). Must $f$ be linear?

The claim `P` below quantifies over all spaces $V$, $W$, all surjective linear $g$ and all
right inverses $f$; `IsLinearMap ℝ f` says $f$ preserves $+$ and $\\cdot$ (with
`hf.map_add` and `hf.map_smul`).

This is a *decide* level: commit with `left` (no) or `right` (yes), then prove your choice.
To use a hypothesis `H : ∀ (V W : Type) …`, apply it to concrete spaces, e.g.
`H (Fin 2 → ℝ) ℝ g f hsurj hinv`; `LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ` is $(x,y) \\mapsto x$.
"

namespace LinearAlgebraGame

/-- Decide: must every right inverse of a surjective linear map be linear? -/
Statement : (¬ ∀ (V W : Type) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
      (g : V →ₗ[ℝ] W) (f : W → V), Function.Surjective g → (∀ w, g (f w) = w) →
      IsLinearMap ℝ f) ∨
    (∀ (V W : Type) [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
      (g : V →ₗ[ℝ] W) (f : W → V), Function.Surjective g → (∀ w, g (f w) = w) →
      IsLinearMap ℝ f) := by
  Hint "Decide first. $g$ forgets information; a right inverse only has to put *something*
  back. Try $g(x,y) = x$."
  left
  intro H
  Hint "Take $g(x, y) = x$ and $f(x) = (x, x^2)$."
  Hint (hidden := true) "`have hsurj : Function.Surjective (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by`
  `intro x; use ![x, 0]; exact rfl`"
  have hsurj : Function.Surjective (LinearMap.proj 0 : (Fin 2 → ℝ) →ₗ[ℝ] ℝ) := by
    intro x
    use ![x, 0]
    exact rfl
  Hint (strict := true) (hidden := true) "`have hf := H (Fin 2 → ℝ) ℝ (LinearMap.proj 0) (fun x => ![x, x ^ 2]) hsurj (fun x => rfl)`"
  have hf := H (Fin 2 → ℝ) ℝ (LinearMap.proj 0) (fun x => ![x, x ^ 2]) hsurj (fun x => rfl)
  Hint (strict := true) "Compare $f(2 \\cdot 1)$ with $2\\cdot f(1)$ in the second coordinate."
  Hint (hidden := true) "`have h2 := {hf}.map_smul 2 1`, `have h3 := congrFun h2 1`, `norm_num at h3`."
  have h2 := hf.map_smul 2 1
  have h3 := congrFun h2 1
  norm_num at h3

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 8 Q3: no.** $g(x,y) = x$ is linear and onto, and $f(x) = (x, x^2)$ satisfies
$g \\circ f = \\mathrm{id}$, but $f(2) = (2,4) \\neq (2,2) = 2 f(1)$.
"

NewDefinition LinearMap.proj IsLinearMap
TheoremTab "Maps"
