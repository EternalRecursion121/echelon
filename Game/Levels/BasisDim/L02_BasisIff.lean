import Game.Levels.BasisDim.L01_BasisUnique

World "BasisDim"
Level 2
Title "Basis means unique representation"

Introduction "
Now the converse, and with it all of Theorem Two.III.1.12: $v$ is a basis of the whole space
($\\top$) **if and only if** every vector has exactly one representation. The direction ⇒ is
the previous level, `rep_unique_of_isBasisOf`.
"

namespace LinearAlgebraGame

/-- A family $v$ is a basis of the whole space iff every vector has exactly one
representation $\sum_i c_i v_i$. -/
Statement isBasisOf_top_iff {ι V : Type*} [Fintype ι] [AddCommGroup V] [Module ℝ V]
    (v : ι → V) :
    IsBasisOf v ⊤ ↔
      ∀ x : V, ∃ c : ι → ℝ, ∑ i, c i • v i = x ∧ ∀ d : ι → ℝ, ∑ i, d i • v i = x → d = c := by
  constructor
  · Hint "This direction is the previous level."
    Hint (hidden := true) "`exact rep_unique_of_isBasisOf v`"
    exact rep_unique_of_isBasisOf v
  · intro h
    constructor
    · Hint "Independence: a relation $\\sum g_i v_i = 0$ and the trivial one $\\sum 0\\cdot v_i = 0$
      are two representations of $\\vec 0$, so they agree."
      rw [Fintype.linearIndependent_iff]
      intro g hg
      Hint (hidden := true) "`obtain ⟨c, -, hc⟩ := h 0` gives the uniqueness part for $\\vec 0$."
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

NewTheorem LinearAlgebraGame.rep_unique_of_isBasisOf eq_top_iff
