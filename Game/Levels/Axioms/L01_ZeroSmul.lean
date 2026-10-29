import Game.Metadata
import Game.Ch2a

World "Axioms"
Level 1
Title "Zero times anything"

Introduction "
A vector space is a set $V$ with $+$ and $\\cdot$ satisfying Hefferon's ten conditions
(Definition Two.I.1.1). From now on statements begin like this:

`{V : Type*} [AddCommGroup V] [Module ℝ V]`

Read it as **\"let $V$ be a real vector space\"**. `V : Type*` says $V$ is some collection of
objects (the vectors). `[AddCommGroup V]` says $V$ has a $+$, a $\\vec 0$ and negatives obeying
conditions (2)–(5); `[Module ℝ V]` says real numbers can multiply vectors, obeying (7)–(10).
Nothing else is known about $V$, so a theorem proved here holds in *every* vector space —
in particular in Chapter One's $\\mathbb{R}^n$, which is `Fin n → ℝ` (and in the spaces of
functions, polynomials and matrices you will meet next).

Each condition has a Lean name (closure, (1) and (6), is automatic: `v + w` and `r • v` are
again in `V`):

| Hefferon | statement | Lean name |
|---|---|---|
| (2) | $\\vec v + \\vec w = \\vec w + \\vec v$ | `add_comm v w` |
| (3) | $(\\vec v + \\vec w) + \\vec u = \\vec v + (\\vec w + \\vec u)$ | `add_assoc v w u` |
| (4) | $\\vec v + \\vec 0 = \\vec v$ (and $\\vec 0 + \\vec v = \\vec v$) | `add_zero v` (`zero_add v`) |
| (5) | $-\\vec v + \\vec v = \\vec 0$ (and $\\vec v + -\\vec v = \\vec 0$) | `neg_add_cancel v` (`add_neg_cancel v`) |
| (7) | $(r + s)\\vec v = r\\vec v + s\\vec v$ | `add_smul r s v` |
| (8) | $r(\\vec v + \\vec w) = r\\vec v + r\\vec w$ | `smul_add r v w` |
| (9) | $(rs)\\vec v = r(s\\vec v)$ | `mul_smul r s v`; read backwards: `smul_smul r s v` |
| (10) | $1\\vec v = \\vec v$ | `one_smul ℝ v` |

They enter your inventory as you need them (the rest of the table by level 8). (`one_smul` must be told which scalars are
meant, so its first argument is `ℝ`: `one_smul ℝ v : (1 : ℝ) • v = v`.) Your inventory now holds just the conditions this
proof needs, plus one cancellation law. There is no automation.

Our first theorem is Lemma Two.I.1.16 (1): $0 \\cdot \\vec v = \\vec 0$.
It is *not* one of the axioms; we must earn it.
"

namespace LinearAlgebraGame

/-- For every vector $\vec v$, $0 \cdot \vec v = \vec 0$. -/
Statement zero_smul_eq_zero {V : Type*} [AddCommGroup V] [Module ℝ V] (v : V) :
    (0 : ℝ) • v = 0 := by
  Hint "Idea: $0 = 0 + 0$. What does that say about $0 \\cdot v$?"
  Hint (hidden := true) "So $0 \\cdot v + 0 \\cdot v = 0 \\cdot v + \\vec 0$. State that with `have`, then cancel."
  Hint (hidden := true) "`have h : (0:ℝ) • {v} + (0:ℝ) • {v} = (0:ℝ) • {v} + 0`"
  have h : (0:ℝ) • v + (0:ℝ) • v = (0:ℝ) • v + 0 := by
    Hint (hidden := true) "Rewrite the left side with `← add_smul`, then `add_zero` twice."
    rw [← add_smul, add_zero, add_zero]
  Hint (hidden := true) "Cancel $0 \\cdot v$ on the left of both sides of `{h}`."
  exact add_left_cancel h

end LinearAlgebraGame

Conclusion "
That is exactly the textbook proof, line for line. From now on `zero_smul_eq_zero` is in
your inventory.
"

DisabledTactic norm_num simp
DisabledTheorem zero_smul
TheoremTab "Vector spaces"
NewTheorem add_left_cancel add_smul add_zero
