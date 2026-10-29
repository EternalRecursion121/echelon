import Game.Metadata
import Game.Ch2b

World "BasisDim"
Level 1
Title "Basis means unique representation"

Introduction "
A **basis** of a subspace $W$ is a sequence $\\langle \\vec\\beta_1, \\dots, \\vec\\beta_n\\rangle$
that is linearly independent and spans $W$. In this game a sequence is a family
`v : ι → V`, and `IsBasisOf v W` means exactly

`LinearIndependent ℝ v ∧ Submodule.span ℝ (Set.range v) = W`.

Hefferon's **Theorem Two.III.1.12**: $B$ is a basis of $V$ if and only if every vector
of $V$ can be written as a linear combination of $B$ in **exactly one** way. Those unique
coefficients are the *coordinates* $\\operatorname{Rep}_B(\\vec v)$.

Prove it. (`∃! c, P c` means: some `c` satisfies `P`, and any `d` satisfying `P` equals `c`.)

New: `rintro` is `intro` followed by `obtain`: `rintro ⟨a, b⟩` introduces a hypothesis and takes it apart at once (a pattern `rfl` substitutes an equation away).
"

namespace LinearAlgebraGame

/-- A family $v$ is a basis of the whole space iff every vector has exactly one
representation $\sum_i c_i v_i$. -/
Statement isBasisOf_top_iff {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (v : ι → V) :
    IsBasisOf v ⊤ ↔ ∀ x : V, ∃! c : ι → ℝ, ∑ i, c i • v i = x := by
  Hint "Two directions. Spanning gives *existence* of coefficients; independence gives
  *uniqueness* (subtract two representations)."
  constructor
  · Hint (hidden := true) "`rintro ⟨hli, hsp⟩ x` takes the basis apart."
    rintro ⟨hli, hsp⟩ x
    Hint "First, $x$ lies in the span, so it has some coefficients."
    Hint (hidden := true) "`Submodule.mem_span_range_iff_exists_fun` turns
    membership of a span into the existence of coefficients."
    have hx : x ∈ Submodule.span ℝ (Set.range v) := by
      Hint (hidden := true) "`rw [{hsp}]` and then `exact Submodule.mem_top`."
      rw [hsp]
      exact Submodule.mem_top
    rw [Submodule.mem_span_range_iff_exists_fun] at hx
    obtain ⟨c, hc⟩ := hx
    Hint (hidden := true) "`refine ⟨{c}, {hc}, fun d hd => ?_⟩` leaves the uniqueness."
    refine ⟨c, hc, fun d hd => ?_⟩
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
  · intro h
    constructor
    · Hint "Independence: a relation $\\sum g_i v_i = 0$ and the trivial one $\\sum 0\\cdot v_i = 0$
      are two representations of $\\vec 0$, so they agree."
      rw [Fintype.linearIndependent_iff]
      intro g hg
      Hint (hidden := true) "`obtain ⟨c, -, hc⟩ := h 0`"
      obtain ⟨c, -, hc⟩ := h 0
      have h1 := hc g hg
      have h2 := hc 0 (by simp)
      intro i
      Hint (hidden := true) "`rw [{h1}, ← {h2}]` and the goal is `0 i = 0`, which is `exact rfl`."
      rw [h1, ← h2]
      exact rfl
    · Hint "Spanning: every $x$ is in the span — use the existence part."
      Hint (hidden := true) "`rw [eq_top_iff]` reduces to `⊤ ≤ span`."
      rw [eq_top_iff]
      intro x _
      rw [Submodule.mem_span_range_iff_exists_fun]
      obtain ⟨c, hc, -⟩ := h x
      exact ⟨c, hc⟩

end LinearAlgebraGame

Conclusion "
So a basis is exactly a coordinate system: $\\operatorname{Rep}_B(\\vec v)$ is the unique
$c$ with $\\sum c_i\\vec\\beta_i = \\vec v$. `isBasisOf_top_iff` is now in your inventory.
"

TheoremTab "Basis"

NewDefinition LinearAlgebraGame.IsBasisOf
NewTactic rintro
NewTheorem eq_top_iff Finset.sum_sub_distrib Submodule.mem_top Iff.rfl
