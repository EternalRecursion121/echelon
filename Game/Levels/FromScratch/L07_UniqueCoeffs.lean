import Game.Levels.FromScratch.L06_Bridge

World "FromScratch"
Level 7
Title "Unique coefficients (boss)"

Introduction "
Why do we care about independence? Because it makes coefficients *unique*: if
$\\vec v_0, \\ldots, \\vec v_{n-1}$ are independent, a vector can be written as
$\\sum_i c_i\\vec v_i$ in at most one way — and only independent families have this property.
(This is the heart of Hefferon's Theorem Two.III.1.12: coordinates with respect to a basis are
well defined.)

Prove it with your own `LinIndep`. For functions `c d : Fin n → ℝ`, `c = d` means
`c i = d i` for every `i` (`funext i`), and `(c - d) i = c i - d i`.
"

namespace LinearAlgebraGame

/-- $\vec v_0, \ldots, \vec v_{n-1}$ are independent iff equal combinations have equal
coefficients. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] {n : ℕ} (v : Fin n → V) :
    LinIndep v ↔ ∀ c d : Fin n → ℝ, ∑ i, c i • v i = ∑ i, d i • v i → c = d := by
  constructor
  · Hint "If two combinations agree, their difference is a relation with coefficients
    $c - d$."
    intro h c d hcd
    funext i
    Hint (hidden := true) "`have h1 := {h} (c - d) (by simp [sub_smul, {hcd}]) {i}`"
    have h1 := h (c - d) (by simp [sub_smul, hcd]) i
    Hint (hidden := true) "`simp at h1`, then `linarith`."
    simp at h1
    linarith
  · Hint "A relation $\\sum_i c_i\\vec v_i = \\vec 0$ is two combinations that agree: the one with
    coefficients $c$ and the one with all coefficients $0$."
    intro h c hc i
    Hint (hidden := true) "`have h1 := {h} {c} 0 (by rw [{hc}]; simp)`"
    have h1 := h c 0 (by rw [hc]; simp)
    Hint (hidden := true) "`rw [{h1}, Pi.zero_apply]`"
    rw [h1, Pi.zero_apply]

end LinearAlgebraGame

Conclusion "
Independent = every vector of the span has exactly one list of coordinates. Bases (next
chapter) are the independent spanning sets, so coordinates with respect to a basis are well
defined.
"

TheoremTab "From Scratch"
