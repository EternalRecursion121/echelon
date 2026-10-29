import Game.Metadata
import Game.Ch2a

World "Subspaces"
Level 1
Title "The subspace test"

Introduction "
A *subspace* of $V$ is a subset that is itself a vector space under the inherited
operations (Definition Two.I.2.1). In Lean a subspace of $V$ is a `Submodule ℝ V`: a set
(its *carrier*) together with proofs that it contains $\\vec 0$ and is closed under $+$ and
under scalar multiplication. \"The set $S$ is a subspace\" is therefore
`∃ W : Submodule ℝ V, (W : Set V) = S`.

**Lemma Two.I.2.9 (the subspace test).** A nonempty subset $S$ is a subspace if it is closed
under linear combinations of pairs: $c_1\\vec s_1 + c_2\\vec s_2 \\in S$ for all scalars and
all $\\vec s_1, \\vec s_2 \\in S$.

**Building a subspace.** A `Submodule` is a structure with four fields: the carrier set and
three closure proofs. Write it out field by field, with `?_` for each proof you still owe:

`refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩`

This leaves four goals in order: closure under $+$, $\\vec 0 \\in S$, closure under scaling,
and finally `↑{ carrier := S, … } = S` — \"the set of the subspace you built is `S`\", true by
definition.

New tactic: `rfl` closes a goal `a = b` whose two sides are equal *by definition*.
"

namespace LinearAlgebraGame

/-- Lemma Two.I.2.9: a nonempty subset closed under pairwise linear combinations is a
subspace. -/
Statement subspace_test {V : Type*} [AddCommGroup V] [Module ℝ V] (S : Set V)
    (hne : S.Nonempty)
    (h : ∀ (c₁ c₂ : ℝ) (s₁ s₂ : V), s₁ ∈ S → s₂ ∈ S → c₁ • s₁ + c₂ • s₂ ∈ S) :
    ∃ W : Submodule ℝ V, (W : Set V) = S := by
  Hint "First get hold of an element of `S`: `obtain ⟨s, hs⟩ := {hne}`."
  obtain ⟨s, hs⟩ := hne
  Hint "Now build the subspace with carrier `S`, as in the introduction."
  Hint (hidden := true) "`refine ⟨\{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩`"
  refine ⟨{ carrier := S, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, ?_⟩
  · Hint "Closure under $+$: a sum is the combination with $c_1 = c_2 = 1$."
    intro a b ha hb
    Hint (hidden := true) "`have h1 := {h} 1 1 {a} {b} {ha} {hb}`, then `rw [one_smul, one_smul] at h1`."
    have h1 := h 1 1 a b ha hb
    rw [one_smul, one_smul] at h1
    exact h1
  · Hint "Contains $\\vec 0$: here is where *nonempty* matters. Use $0\\cdot s + 0\\cdot s$
    for the element `{s}` you have."
    Hint (hidden := true) "`have h0 := {h} 0 0 {s} {s} {hs} {hs}`, then `rw [zero_smul, add_zero] at h0`."
    have h0 := h 0 0 s s hs hs
    rw [zero_smul, add_zero] at h0
    exact h0
  · Hint "Closure under scaling: $c\\cdot a = c\\cdot a + 0\\cdot a$."
    intro c a ha
    Hint (hidden := true) "`have h1 := {h} {c} 0 {a} {a} {ha} {ha}`"
    have h1 := h c 0 a a ha ha
    rw [zero_smul, add_zero] at h1
    exact h1
  · Hint "The set of the subspace you built is `S` by definition."
    rfl

end LinearAlgebraGame

Conclusion "
From now on `subspace_test` is in your inventory: to show a set is a subspace, `apply
subspace_test` and check two things — it is nonempty, and closed under combinations.
"

TheoremTab "Subspaces"
NewTheorem zero_smul
NewTactic rfl
