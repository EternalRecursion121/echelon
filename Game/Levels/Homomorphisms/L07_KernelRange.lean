import Game.Levels.Homomorphisms.L06_Convex

World "Homomorphisms"
Level 7
Title "Null space and range are subspaces"

Introduction "
The **null space** $\\mathscr N(h) = \\{\\vec v \\mid h(\\vec v) = \\vec 0\\}$ and the **range space**
$\\mathscr R(h) = \\{h(\\vec v) \\mid \\vec v \\in V\\}$ (Hefferon Three.II.2). Both contain $\\vec 0$
(by `hom_map_zero`). Show they are closed under linear combinations of two vectors; by
Hefferon's subspace criterion (Lemma Two.I.2.9) they are subspaces.
"

namespace LinearAlgebraGame

/-- $\mathscr N(h)$ and $\mathscr R(h)$ are closed under linear combinations. -/
Statement {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]
    (h : V →ₗ[ℝ] W) :
    (∀ (u v : V) (r s : ℝ), h u = 0 → h v = 0 → h (r • u + s • v) = 0) ∧
    (∀ (w₁ w₂ : W) (r s : ℝ), (∃ v, h v = w₁) → (∃ v, h v = w₂) →
      ∃ v, h v = r • w₁ + s • w₂) := by
  constructor
  · intro u v r s hu hv
    Hint "Linearity, then the hypotheses."
    Hint (hidden := true) "`rw [map_add, map_smul, map_smul, {hu}, {hv}, smul_zero, smul_zero, add_zero]`"
    rw [map_add, map_smul, map_smul, hu, hv, smul_zero, smul_zero, add_zero]
  · Hint (hidden := true) "`rintro w₁ w₂ r s ⟨v₁, rfl⟩ ⟨v₂, rfl⟩`"
    rintro w₁ w₂ r s ⟨v₁, rfl⟩ ⟨v₂, rfl⟩
    Hint "Which vector maps to $r\\,h(\\vec v_1) + s\\,h(\\vec v_2)$?"
    Hint (hidden := true) "`use {r} • {v₁} + {s} • {v₂}`, then `rw [map_add, map_smul, map_smul]`."
    use r • v₁ + s • v₂
    rw [map_add, map_smul, map_smul]

end LinearAlgebraGame

Conclusion "
Lean builds these subspaces for you: `LinearMap.ker h` and `LinearMap.range h`, with
`LinearMap.mem_ker : v ∈ ker h ↔ h v = 0` and `LinearMap.mem_range : w ∈ range h ↔ ∃ v, h v = w`.
The **rank** of $h$ is `finrank ℝ (LinearMap.range h)`, the **nullity** `finrank ℝ (LinearMap.ker h)`.
"

NewTheorem LinearMap.mem_range

DisabledTactic simp norm_num
TheoremTab "Maps"
