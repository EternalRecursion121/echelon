import Game.Levels.Homomorphisms.L03_NonExample

World "Homomorphisms"
Level 4
Title "Extending linearly from a basis"

Introduction "
Hefferon Theorem Three.II.1.9: a homomorphism is determined by its action on a basis, and
*any* assignment of values to the basis vectors extends linearly to a homomorphism.

For a basis `B` and values `f : Fin n → W`, Lean's `B.constr ℝ f : V →ₗ[ℝ] W` is the linear
extension (Definition 1.10), and `B.constr_basis ℝ f i` says it sends `B i` to `f i`.
Existence is therefore given; your job is **uniqueness**: a second linear map with the same
values on the basis equals it everywhere.
"

namespace LinearAlgebraGame

/-- For a basis $B$ and any vectors $f(1),\dots,f(n)$ of $W$ there is exactly one linear map with $h(\vec\beta_i) = f(i)$. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (B : Module.Basis (Fin n) ℝ V) (f : Fin n → W) :
    ∃! h : V →ₗ[ℝ] W, ∀ i, h (B i) = f i := by
  Hint (hidden := true) "`use B.constr ℝ f`, then `constructor`."
  use B.constr ℝ f
  constructor
  · intro i
    Hint (hidden := true) "`exact B.constr_basis ℝ f i`"
    exact B.constr_basis ℝ f i
  · intro g hg
    Hint "Two maps are equal if they agree at every $\\vec v$. Write
    $\\vec v = c_1\\vec\\beta_1+\\dots+c_n\\vec\\beta_n$ and use linearity of both."
    Hint (hidden := true) "`ext v`, then `rw [← B.sum_repr v, map_sum, map_sum]`."
    ext v
    rw [← B.sum_repr v, map_sum, map_sum]
    Hint (hidden := true) "`simp only [map_smul, hg, B.constr_basis]`"
    simp only [map_smul, hg, B.constr_basis]

end LinearAlgebraGame

Conclusion "
Example: rotation of the plane through $\\theta$ is the linear extension of
$\\vec e_1 \\mapsto (\\cos\\theta, \\sin\\theta)$, $\\vec e_2 \\mapsto (-\\sin\\theta, \\cos\\theta)$.
"

NewDefinition Module.Basis.constr
DisabledTheorem Module.Basis.ext Module.Basis.constr_eq
TheoremTab "Bases"
NewTheorem Module.Basis.constr_basis map_sum
