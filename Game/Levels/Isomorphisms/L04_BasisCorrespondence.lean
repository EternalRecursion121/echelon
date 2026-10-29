import Game.Levels.Isomorphisms.L03_Equivalence

World "Isomorphisms"
Level 4
Title "Extending a correspondence between bases"

-- @sheet 6 Q3
/-! @answer
**Yes.** Write $\vec v = c_1\vec\beta_1+\dots+c_n\vec\beta_n$ (coordinates with respect to $B$),
so $\hat f(\vec v) = c_1 f(\vec\beta_1)+\dots+c_n f(\vec\beta_n)$.
*Linear:* the coordinates of $\vec u + \vec v$ are the sums of the coordinates and those of
$r\vec v$ are $r$ times them, so $\hat f(\vec u+\vec v)=\hat f(\vec u)+\hat f(\vec v)$ and
$\hat f(r\vec v)=r\hat f(\vec v)$.
*One-to-one:* the coordinates of $\hat f(\vec v)$ with respect to $D$ are exactly $c_1,\dots,c_n$
(as $D$ is a basis, representations are unique); so $\hat f(\vec u)=\hat f(\vec v)$ forces
$\vec u$ and $\vec v$ to have the same $B$-coordinates, hence $\vec u=\vec v$.
*Onto:* any $\vec w = d_1 f(\vec\beta_1)+\dots+d_n f(\vec\beta_n)$ since $D$ spans $W$, and then
$\vec w = \hat f(d_1\vec\beta_1+\dots+d_n\vec\beta_n)$.
-/
Introduction "
**Problem Sheet 6, Question 3.** Does every correspondence between bases, when extended to
the spaces, give an isomorphism? That is, suppose that $V$ is a vector space with basis
$B = \\langle \\vec\\beta_1, \\dots, \\vec\\beta_n\\rangle$ and that $f : B \\to D$ is a
correspondence such that $D = \\langle f(\\vec\\beta_1), \\dots, f(\\vec\\beta_n)\\rangle$ is a
basis for $W$. Must $\\hat f : V \\to W$ sending $\\vec v = c_1\\vec\\beta_1 + \\dots + c_n\\vec\\beta_n$
to $\\hat f(\\vec v) = c_1 f(\\vec\\beta_1) + \\dots + c_n f(\\vec\\beta_n)$ be an isomorphism?

From now on bases of a whole space come in Lean's own packaging:
`B : Module.Basis (Fin n) ℝ V` is a basis $\\langle B_0, \\dots, B_{n-1}\\rangle$ of all of $V$ —
the same thing as the game's `IsBasisOf B ⊤` — bundled with its coordinate map: `B.repr v i` is
the coordinate $c_i$ of $\\vec v$ (`Module.Basis.sum_repr`: $\\sum_i c_i B_i = \\vec v$; and
`Module.Basis.repr_sum_self`: the coordinates of $\\sum_i c_i B_i$ are the $c_i$). `B.repr v` is
a *finitely supported function*, and `Finsupp.add_apply` / `Finsupp.smul_apply` evaluate sums
and multiples of those.

In Lean: `D i` is $f(\\vec\\beta_i)$ and `hfhat` is the definition of $\\hat f$. \"Isomorphism\" is written out as: preserves $+$, preserves $\\cdot$,
one-to-one, onto.

This is a *decide* level: the goal is `¬ P ∨ P`. Commit with `left` (no, it need not be)
or `right` (yes, it must be), then prove your choice.
"

namespace LinearAlgebraGame

/-- Decide: must $\hat f$ be an isomorphism? -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    {n : ℕ} (B : Module.Basis (Fin n) ℝ V) (D : Module.Basis (Fin n) ℝ W) (fhat : V → W)
    (hfhat : ∀ v, fhat v = ∑ i, B.repr v i • D i) :
    (¬ ((∀ u v, fhat (u + v) = fhat u + fhat v) ∧ (∀ (r : ℝ) v, fhat (r • v) = r • fhat v) ∧
      (∀ u v, fhat u = fhat v → u = v) ∧ (∀ w, ∃ v, fhat v = w))) ∨
    ((∀ u v, fhat (u + v) = fhat u + fhat v) ∧ (∀ (r : ℝ) v, fhat (r • v) = r • fhat v) ∧
      (∀ u v, fhat u = fhat v → u = v) ∧ (∀ w, ∃ v, fhat v = w)) := by
  Hint "Decide first: check the four properties one at a time on paper, writing vectors in
  coordinates."
  right
  Hint (hidden := true) "Four properties: split with `refine ⟨?_, ?_, ?_, ?_⟩`."
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u v
    Hint "Coordinates of a sum are sums of coordinates; then distribute."
    Hint (hidden := true) "`rw [hfhat, hfhat, hfhat, map_add, ← Finset.sum_add_distrib]`, then
    compare the sums term by term: `congr 1`, `funext i`, `rw [Finsupp.add_apply, add_smul]`."
    rw [hfhat, hfhat, hfhat, map_add, ← Finset.sum_add_distrib]
    congr 1
    funext i
    rw [Finsupp.add_apply, add_smul]
  · intro r v
    Hint (hidden := true) "`rw [hfhat, hfhat, map_smul, Finset.smul_sum]`, then term by term:
    `congr 1`, `funext i`, `rw [Finsupp.smul_apply, smul_eq_mul, smul_smul]`."
    rw [hfhat, hfhat, map_smul, Finset.smul_sum]
    congr 1
    funext i
    rw [Finsupp.smul_apply, smul_eq_mul, smul_smul]
  · intro u v h
    Hint "Key fact: the $D$-coordinates of $\\hat f(\\vec x)$ are the $B$-coordinates of $\\vec x$.
    State it as a separate fact first."
    Hint (hidden := true) "`have key : ∀ x, D.repr (fhat x) = B.repr x := by …`
    (inside: `intro x`, `ext i`, `rw [hfhat, Module.Basis.repr_sum_self]`)."
    have key : ∀ x, D.repr (fhat x) = B.repr x := by
      intro x
      ext i
      rw [hfhat, Module.Basis.repr_sum_self]
    Hint (strict := true) (hidden := true) "Vectors with equal coordinates are equal: `apply B.repr.injective`, then
    `rw [← key, ← key, {h}]`."
    apply B.repr.injective
    rw [← key, ← key, h]
  · intro w
    Hint "$D$ spans $W$: use the $D$-coordinates of $\\vec w$ as $B$-coordinates."
    Hint (hidden := true) "`use ∑ i, D.repr {w} i • B i`, then
    `rw [hfhat, Module.Basis.repr_sum_self]` and `exact D.sum_repr {w}`."
    use ∑ i, D.repr w i • B i
    rw [hfhat, Module.Basis.repr_sum_self]
    exact D.sum_repr w

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q3: yes.** $\\hat f$ is linear, and it is a correspondence because both
$B$ and $D$ give *unique* coordinates. Mathlib calls this isomorphism `Basis.equiv`.
"

DisabledTactic simp norm_num
TheoremTab "Bases"
NewTheorem Finsupp.add_apply Finsupp.smul_apply Module.Basis.repr_sum_self Module.Basis.sum_repr
NewDefinition Module.Basis Module.Basis.repr
