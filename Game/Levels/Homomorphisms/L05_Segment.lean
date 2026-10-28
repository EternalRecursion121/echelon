import Game.Levels.Homomorphisms.L04_Extension

World "Homomorphisms"
Level 5
Title "Images of segments"

-- @sheet 5 Q3a
/-! @answer
If $\vec x = t\vec u + (1-t)\vec v$ with $t\in[0..1]$ then by linearity
$h(\vec x) = t\,h(\vec u) + (1-t)\,h(\vec v)$, which lies on the segment between $h(\vec u)$ and
$h(\vec v)$. Conversely a point $t\,h(\vec u)+(1-t)\,h(\vec v)$ of that segment is
$h(t\vec u + (1-t)\vec v)$, the image of a point of $\ell$. So $h(\ell)$ is exactly the segment
between $h(\vec u)$ and $h(\vec v)$.
-/
Introduction "
**Problem Sheet 5, Question 3(a).** Where $\\vec u, \\vec v \\in \\mathbb R^n$, by definition the
line segment connecting them is the set
$\\ell = \\{ t\\cdot\\vec u + (1-t)\\cdot\\vec v \\mid t \\in [0..1] \\}$. Show that the image, under a
homomorphism $h$, of the segment between $\\vec u$ and $\\vec v$ is the segment between
$h(\\vec u)$ and $h(\\vec v)$.

In Lean the segment is `seg u v` (see the definition in your inventory) and the image of a set
$S$ is `h '' S`. Equality of sets: use `ext y` and prove both inclusions.
"

namespace LinearAlgebraGame

/-- $h(\ell) = $ the segment between $h(\vec u)$ and $h(\vec v)$. -/
Statement image_seg {n m : ℕ} (h : (Fin n → ℝ) →ₗ[ℝ] (Fin m → ℝ)) (u v : Fin n → ℝ) :
    h '' seg u v = seg (h u) (h v) := by
  Hint "Two inclusions. Each point of either set is described by some $t \\in [0..1]$."
  ext y
  constructor
  · Hint (hidden := true) "`rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩` names $t$ and substitutes."
    rintro ⟨x, ⟨t, ht, rfl⟩, rfl⟩
    Hint "Same $t$ works: linearity moves $h$ inside."
    Hint (hidden := true) "`exact ⟨t, ht, by rw [map_add, map_smul, map_smul]⟩`"
    exact ⟨t, ht, by rw [map_add, map_smul, map_smul]⟩
  · Hint (hidden := true) "`rintro ⟨t, ht, rfl⟩`"
    rintro ⟨t, ht, rfl⟩
    Hint "Which point of $\\ell$ maps to $t\\,h(\\vec u) + (1-t)\\,h(\\vec v)$?"
    Hint (hidden := true) "`exact ⟨t • u + (1 - t) • v, ⟨t, ht, rfl⟩, by rw [map_add, map_smul, map_smul]⟩`"
    exact ⟨t • u + (1 - t) • v, ⟨t, ht, rfl⟩, by rw [map_add, map_smul, map_smul]⟩

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 5 Q3(a):** $h(t\\vec u + (1-t)\\vec v) = t\\,h(\\vec u) + (1-t)\\,h(\\vec v)$, so the
image of the segment is the segment of the images, with the same parameter $t$.
"

NewDefinition LinearAlgebraGame.seg
DisabledTactic simp norm_num
TheoremTab "Maps"
