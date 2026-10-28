import Game.Metadata
import Game.Ch3a

World "Isomorphisms"
Level 1
Title "Dilations"

Introduction "
An **isomorphism** $f : V \\to W$ (Hefferon Definition Three.I.1.3) is a *correspondence*
(one-to-one and onto) that preserves the structure:
$f(\\vec u + \\vec v) = f(\\vec u) + f(\\vec v)$ and $f(r\\vec v) = r f(\\vec v)$.
An isomorphism from a space to itself is an **automorphism** (Definition 1.7).

The **dilation** $d_s(\\vec v) = s\\vec v$ obviously preserves $+$ and $\\cdot$
(that is `smul_add` and `smul_comm`). The real content is that for $s \\neq 0$ it is a
correspondence. Prove both halves, written exactly as Hefferon defines them:

* one-to-one: $s\\vec u = s\\vec v \\implies \\vec u = \\vec v$;
* onto: every $\\vec w$ is $s\\vec v$ for some $\\vec v$.
"

namespace LinearAlgebraGame

/-- For $s \neq 0$ the dilation $\vec v \mapsto s\vec v$ is one-to-one and onto. -/
Statement {V : Type*} [AddCommGroup V] [Module ℝ V] (s : ℝ) (hs : s ≠ 0) :
    (∀ u v : V, s • u = s • v → u = v) ∧ (∀ w : V, ∃ v, s • v = w) := by
  Hint "Both halves rest on undoing $s$: multiply by $s⁻¹$."
  constructor
  · intro u v h
    Hint "Idea: $\\vec u = s⁻¹(s\\vec u) = s⁻¹(s\\vec v) = \\vec v$."
    Hint (hidden := true) "A `calc` chain says exactly that."
    Hint (hidden := true) "`calc {u} = s⁻¹ • (s • {u}) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]`, then
    `_ = s⁻¹ • (s • {v}) := by rw [{h}]`, then back down to `{v}`."
    calc u = s⁻¹ • (s • u) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = s⁻¹ • (s • v) := by rw [h]
      _ = v := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
  · intro w
    Hint "Which $\\vec v$ does the dilation send to $\\vec w$?"
    Hint (hidden := true) "`use s⁻¹ • {w}`, then `rw [smul_smul, mul_inv_cancel₀ hs, one_smul]`."
    use s⁻¹ • w
    rw [smul_smul, mul_inv_cancel₀ hs, one_smul]

end LinearAlgebraGame

Conclusion "
So every nonzero dilation is an automorphism. (For $s = 0$ it is neither one-to-one nor onto
unless $V = \\{\\vec 0\\}$.) In Lean, an isomorphism $V \\to W$ is an element of the type
`V ≃ₗ[ℝ] W`; we meet those next.
"

NewTheorem mul_inv_cancel₀

DisabledTactic simp norm_num
TheoremTab "Isomorphisms"
