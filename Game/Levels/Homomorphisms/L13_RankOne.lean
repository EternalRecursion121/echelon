import Game.Levels.Homomorphisms.L12_InjOnto

World "Homomorphisms"
Level 13
Title "A rank-one transformation"

-- @sheet 6 Q5
/-! @answer
Since $\operatorname{rank}(t) = 1$, the range is spanned by a single nonzero vector $\vec w$,
so for each $\vec v$ there is a scalar $a(\vec v)$ with $t(\vec v) = a(\vec v)\,\vec w$. In
particular $t(\vec w) = r\vec w$ for some real $r$. Then for every $\vec v$,
$$t(t(\vec v)) = t(a(\vec v)\vec w) = a(\vec v)\,t(\vec w) = a(\vec v)\,r\,\vec w = r\,t(\vec v),$$
so $t\circ t = r\cdot t$.
-/
Introduction "
**Problem Sheet 6, Question 5.** Prove that for any transformation $t : V \\to V$ that is rank
one, the map given by composing the operator with itself $t \\circ t : V \\to V$ satisfies
$t \\circ t = r \\cdot t$ for some real number $r$.

In Lean, rank one is `finrank ℝ (LinearMap.range t) = 1` and the composite is `t ∘ₗ t`.
`exists_line_of_finrank_eq_one` (from Basis & Dimension) turns a one-dimensional subspace into
a line: a nonzero $\\vec w$ in it such that every member is a multiple $c\\,\\vec w$.
`LinearMap.mem_range_self t v : t v ∈ range t`.
"

namespace LinearAlgebraGame

/-- If $\operatorname{rank} t = 1$ then $t\circ t = r\cdot t$ for some $r\in\mathbb R$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (t : V →ₗ[ℝ] V)
    (ht : Module.finrank ℝ (LinearMap.range t) = 1) :
    ∃ r : ℝ, t ∘ₗ t = r • t := by
  Hint "The range is the line through one vector $\\vec w$. Get $\\vec w$ first."
  Hint (hidden := true) "`obtain ⟨w, -, -, hw⟩ := exists_line_of_finrank_eq_one ht`"
  obtain ⟨w, -, -, hw⟩ := exists_line_of_finrank_eq_one ht
  Hint (strict := true) "$t(\\vec w)$ is in the range too, so $t(\\vec w) = r\\vec w$ for some $r$.
  That $r$ works."
  Hint (hidden := true) "`obtain ⟨r, hr⟩ := hw (t w) (LinearMap.mem_range_self t w)`, `use r`, `ext v`."
  obtain ⟨r, hr⟩ := hw (t w) (LinearMap.mem_range_self t w)
  use r
  ext v
  Hint (hidden := true) "`rw [LinearMap.comp_apply, LinearMap.smul_apply]`"
  rw [LinearMap.comp_apply, LinearMap.smul_apply]
  Hint "$t(\\vec v)$ is in the range as well: a multiple $a\\vec w$."
  Hint (hidden := true) "`obtain ⟨a, ha⟩ := hw (t v) (LinearMap.mem_range_self t v)`, then
  `rw [← ha, map_smul, ← hr, smul_smul, smul_smul, mul_comm]`."
  obtain ⟨a, ha⟩ := hw (t v) (LinearMap.mem_range_self t v)
  rw [← ha, map_smul, ← hr, smul_smul, smul_smul, mul_comm]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q5:** with $\\mathscr R(t) = [\\vec w]$ and $t(\\vec w) = r\\vec w$,
$t(t(\\vec v)) = a\\,t(\\vec w) = r\\,(a\\vec w) = r\\,t(\\vec v)$.
"

DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTheorem LinearMap.mem_range_self LinearMap.smul_apply LinearMap.comp_apply
