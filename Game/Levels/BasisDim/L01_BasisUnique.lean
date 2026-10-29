import Game.Metadata
import Game.Ch2b

World "BasisDim"
Level 1
Title "Coordinates exist and are unique"

Introduction "
A **basis** of a subspace $W$ is a sequence $\\langle \\vec\\beta_1, \\dots, \\vec\\beta_n\\rangle$
that is linearly independent and spans $W$. In this game a sequence is a family
`v : ι → V`, and `IsBasisOf v W` means exactly

`LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = W`.

Hefferon's **Theorem Two.III.1.12** says: $B$ is a basis of $V$ if and only if every vector
of $V$ can be written as a linear combination of $B$ in **exactly one** way. Those unique
coefficients are the *coordinates* $\\operatorname{Rep}_B(\\vec v)$. This level proves the
direction *basis ⇒ exactly one way*; the next level proves the converse.

\"Exactly one way\" is written out: some `c` works, **and** every `d` that works equals `c`.

New: `rintro` is `intro` followed by `obtain`: `rintro ⟨a, b⟩` introduces a hypothesis and takes it apart at once (a pattern `rfl` substitutes an equation away).
"

namespace LinearAlgebraGame

/-- If $v$ is a basis of the whole space, every vector has exactly one representation
$\sum_i c_i v_i$. -/
Statement rep_unique_of_isBasisOf {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (v : ι → V) (hv : IsBasisOf v ⊤) :
    ∀ x : V, ∃ c : ι → ℝ, ∑ i, c i • v i = x ∧ ∀ d : ι → ℝ, ∑ i, d i • v i = x → d = c := by
  Hint "Spanning gives *existence* of coefficients; independence gives *uniqueness*
  (subtract two representations)."
  Hint (hidden := true) "`obtain ⟨hli, hsp⟩ := hv` takes the basis apart; then `intro x`."
  obtain ⟨hli, hsp⟩ := hv
  intro x
  Hint "First, $x$ lies in the span, so it has some coefficients."
  Hint (hidden := true) "`Submodule.mem_span_range_iff_exists_fun` turns
  membership of a span into the existence of coefficients."
  have hx : x ∈ Submodule.span ℝ (Set.range v) := by
    Hint (hidden := true) "`rw [{hsp}]` and then `exact Submodule.mem_top`."
    rw [hsp]
    exact Submodule.mem_top
  rw [Submodule.mem_span_range_iff_exists_fun] at hx
  obtain ⟨c, hc⟩ := hx
  Hint (hidden := true) "`refine ⟨{c}, {hc}, ?_⟩` leaves the uniqueness."
  refine ⟨c, hc, ?_⟩
  intro d hd
  Hint "Subtract the two representations: independence says the difference has zero coefficients."
  Hint (hidden := true) "Independence in its usable form is `Fintype.linearIndependent_iff`: only the trivial
  relation. Apply it to the relation with coefficients $d - c$."
  rw [Fintype.linearIndependent_iff] at hli
  Hint (hidden := true) "`have h0 := {hli} ({d} - {c}) (by simp [sub_smul, Finset.sum_sub_distrib, {hc}, {hd}])`"
  have h0 := hli (d - c) (by simp [sub_smul, Finset.sum_sub_distrib, hc, hd])
  funext i
  have := h0 i
  Hint (hidden := true) "`simp at this` then `linarith`."
  simp at this
  linarith

end LinearAlgebraGame

Conclusion "
Spanning gave the coordinates, independence made them unique. Next: the converse.
"

TheoremTab "Basis"

NewDefinition LinearAlgebraGame.IsBasisOf
NewTactic rintro
NewTheorem Finset.sum_sub_distrib Submodule.mem_top
