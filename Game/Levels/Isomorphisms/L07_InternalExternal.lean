import Game.Levels.Isomorphisms.L06_ProductDim

World "Isomorphisms"
Level 7
Title "Internal and external direct sums"

-- @sheet 6 Q2b
/-! @answer
$f(\vec u,\vec w)=\vec u+\vec w$ is linear since addition and scalar multiplication in
$U\times W$ are componentwise. *One-to-one:* if $f(\vec u,\vec w)=\vec 0$ then
$\vec u=-\vec w\in U\cap W=\{\vec 0\}$, so $\vec u=\vec 0$ and then $\vec w=\vec 0$; a linear
map with trivial null space is one-to-one. *Onto:* $V=U+W$, so every $\vec v$ is
$\vec u+\vec w=f(\vec u,\vec w)$ for some $\vec u\in U$, $\vec w\in W$. Hence $f$ is an
isomorphism and the internal and external direct sums are isomorphic.
-/
Introduction "
**Problem Sheet 6, Question 2(b).** Suppose that $U$ and $W$ are subspaces of a vector space
$V$ such that $V = U \\oplus W$ (the *internal* direct sum). Show that the map
$f : U \\times W \\to V$ given by $(\\vec u, \\vec w) \\mapsto \\vec u + \\vec w$ is an isomorphism.
Thus if the internal direct sum is defined then the internal and external direct sums are
isomorphic.

In Lean, $V = U \\oplus W$ is Hefferon's definition: `U ⊔ W = ⊤` ($U + W = V$) and
`U ⊓ W = ⊥` ($U \\cap W = \\{\\vec 0\\}$). The map is `U.subtype.coprod W.subtype`
(`LinearMap.coprod_apply` and `Submodule.subtype_apply` unfold it to $\\vec u + \\vec w$). It is
built as a linear map, so linearity is automatic; you prove one-to-one and onto.

Granted: `injective_iff_map_eq_zero` — a linear map is one-to-one iff only $\\vec 0$ maps to
$\\vec 0$ (you prove this yourself in the Homomorphisms world). An element of $U \\times W$ is a
pair `(u, w)` with `u : U`, `w : W`; `(u : V)` is the underlying vector of `u`.
"

namespace LinearAlgebraGame

/-- If $U + W = V$ and $U \cap W = \{\vec 0\}$, then $(\vec u,\vec w)\mapsto\vec u+\vec w$ is one-to-one and onto. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (U W : Submodule ℝ V)
    (hsum : U ⊔ W = ⊤) (hint : U ⊓ W = ⊥) :
    Function.Injective (U.subtype.coprod W.subtype) ∧
    Function.Surjective (U.subtype.coprod W.subtype) := by
  constructor
  · Hint "If $\\vec u + \\vec w = \\vec 0$ then $\\vec u = -\\vec w$ lies in both $U$ and $W$."
    Hint (hidden := true) "`rw [injective_iff_map_eq_zero]`, then `rintro ⟨u, w⟩ h`."
    rw [injective_iff_map_eq_zero]
    rintro ⟨u, w⟩ h
    Hint (hidden := true) "`rw [LinearMap.coprod_apply, Submodule.subtype_apply, Submodule.subtype_apply] at {h}`"
    rw [LinearMap.coprod_apply, Submodule.subtype_apply, Submodule.subtype_apply] at h
    Hint "First show that $\\vec u$ lies in $U \\cap W$."
    Hint (hidden := true) "`have hu : (u : V) ∈ U ⊓ W := by constructor …`: the first part is `u.2`;
    for the second, `rw [eq_neg_of_add_eq_zero_left {h}]` and `exact W.neg_mem w.2`."
    have hu : (u : V) ∈ U ⊓ W := by
      constructor
      · exact u.2
      · rw [eq_neg_of_add_eq_zero_left h]
        exact W.neg_mem w.2
    Hint (strict := true) (hidden := true) "`rw [hint, Submodule.mem_bot] at hu`"
    rw [hint, Submodule.mem_bot] at hu
    Hint (hidden := true) "Now $\\vec w = \\vec 0$ too: `have hw : (w : V) = 0 := by rw [hu, zero_add] at {h}; exact {h}`."
    have hw : (w : V) = 0 := by
      rw [hu, zero_add] at h
      exact h
    Hint (strict := true) "`pair_eq_zero_iff` says a pair `(u, w)` of subspace elements is zero
    iff both underlying vectors are."
    Hint (hidden := true) "`rw [pair_eq_zero_iff]`, then `exact ⟨hu, hw⟩`."
    rw [pair_eq_zero_iff]
    exact ⟨hu, hw⟩
  · intro v
    Hint "$V = U + W$, so $\\vec v$ is a sum $\\vec y + \\vec z$ with $\\vec y\\in U$, $\\vec z\\in W$."
    Hint (hidden := true) "`have hv : v ∈ U ⊔ W := by rw [hsum]; exact Submodule.mem_top`, then
    `obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv`."
    have hv : v ∈ U ⊔ W := by
      rw [hsum]
      exact Submodule.mem_top
    obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hv
    Hint "Your preimage is a pair of subspace elements. An element of a subspace `U` is written
    `⟨y, hy⟩`: the vector `y` together with a proof `hy : y ∈ U`."
    Hint (hidden := true) "`use (⟨y, hy⟩, ⟨z, hz⟩)`, then `exact hyz`."
    use (⟨y, hy⟩, ⟨z, hz⟩)
    exact hyz

end LinearAlgebraGame

Conclusion "
**Answer to Sheet 6 Q2(b):** $f$ is linear, one-to-one (its null space is
$\\{(\\vec u, -\\vec u) : \\vec u \\in U \\cap W\\} = \\{\\vec 0\\}$) and onto (as $U + W = V$),
so $U \\times W \\cong U \\oplus W$.
"

NewTheorem LinearAlgebraGame.pair_eq_zero_iff injective_iff_map_eq_zero LinearMap.coprod_apply Submodule.subtype_apply eq_neg_of_add_eq_zero_left Submodule.mem_sup
DisabledTactic simp norm_num
TheoremTab "Subspaces"
