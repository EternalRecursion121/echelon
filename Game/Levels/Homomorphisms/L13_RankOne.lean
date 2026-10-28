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
`finrank_eq_one_iff'` turns a one-dimensional space into \"spanned by one nonzero vector\".
Elements of the range are pairs `⟨x, proof⟩`; `(w : V)` is the underlying vector.
"

namespace LinearAlgebraGame

/-- If $\operatorname{rank} t = 1$ then $t\circ t = r\cdot t$ for some $r\in\mathbb R$. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (t : V →ₗ[ℝ] V)
    (ht : Module.finrank ℝ (LinearMap.range t) = 1) :
    ∃ r : ℝ, t ∘ₗ t = r • t := by
  Hint "The range is the line through one vector $\\vec w$. Get $\\vec w$ first."
  Hint (hidden := true) "`obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp ht`"
  obtain ⟨w, hw0, hw⟩ := finrank_eq_one_iff'.mp ht
  Hint (strict := true) "Now show every $t(\\vec v)$ is a multiple of $\\vec w$."
  Hint (hidden := true) "`have key : ∀ v, ∃ a : ℝ, t v = a • (w : V) := by …`; inside,
  `intro v`, `obtain ⟨a, ha⟩ := hw ⟨t v, LinearMap.mem_range_self t v⟩`, `use a`,
  `rw [← Submodule.coe_smul, ha]`."
  have key : ∀ v, ∃ a : ℝ, t v = a • (w : V) := by
    intro v
    obtain ⟨a, ha⟩ := hw ⟨t v, LinearMap.mem_range_self t v⟩
    use a
    rw [← Submodule.coe_smul, ha]
  Hint (strict := true) "$\\vec w$ is in the range too, so $t(\\vec w) = r\\vec w$ for some $r$. That $r$ works."
  Hint (hidden := true) "`obtain ⟨r, hr⟩ := key w`, `use r`, `ext v`."
  obtain ⟨r, hr⟩ := key w
  use r
  ext v
  Hint (hidden := true) "`rw [LinearMap.comp_apply, LinearMap.smul_apply]`, then
  `obtain ⟨a, ha⟩ := key {v}` and `rw [ha, map_smul, hr, smul_comm]`."
  rw [LinearMap.comp_apply, LinearMap.smul_apply]
  obtain ⟨a, ha⟩ := key v
  rw [ha, map_smul, hr, smul_comm]

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q5:** with $\\mathscr R(t) = [\\vec w]$ and $t(\\vec w) = r\\vec w$,
$t(t(\\vec v)) = a\\,t(\\vec w) = r\\,(a\\vec w) = r\\,t(\\vec v)$.
"

DisabledTactic simp norm_num
TheoremTab "Dimension"
NewTheorem LinearMap.mem_range_self Submodule.coe_smul LinearMap.smul_apply SMulCommClass.smul_comm LinearMap.comp_apply
