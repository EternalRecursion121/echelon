import GameServer
import Game.Lib

/-! Documentation for every tactic the game uses. Kept in one place so that worlds never
define the same doc twice. A tactic is *unlocked* in a level with `NewTactic`; it is only
documented here. -/

/-- `exact h` closes the goal using a term `h` whose type is exactly the goal. -/
TacticDoc exact
/-- `rw [h]` rewrites the goal with the equation `h : a = b` (replacing `a` by `b`).
`rw [← h]` rewrites right-to-left; `rw [h] at h'` rewrites a hypothesis. -/
TacticDoc rw
/-- `nth_rw n [h]` rewrites only the `n`-th occurrence. -/
TacticDoc nth_rw
/-- `norm_num` proves goals about explicit numerals (`2 + 2 = 4`, `(1 : ℝ) ≠ 2`);
`norm_num at h` simplifies a hypothesis. `norm_num [lemmas]` also uses the given lemmas.
Some worlds switch it off when it would do the interesting work for you. -/
TacticDoc norm_num
/-- `constructor` splits a goal `P ∧ Q` (or `P ↔ Q`) into separate goals. -/
TacticDoc constructor
/-- `obtain ⟨a, b⟩ := h` takes apart a hypothesis `h : P ∧ Q` or `h : ∃ x, P x`. -/
TacticDoc obtain
/-- `use a` proves `∃ x, P x` by supplying `a`, leaving `P a` to prove. -/
TacticDoc use
/-- `intro h` moves an assumption into the context: for goals `P → Q`, `¬ P`, `∀ x, …`. -/
TacticDoc intro
/-- `left` / `right` choose which side of a goal `P ∨ Q` to prove. -/
TacticDoc left
/-- See `left`. -/
TacticDoc right
/-- `rcases h with h1 | h2` splits `h : P ∨ Q` into cases; `rcases h with ⟨a, b⟩` takes
apart `∧` and `∃`. -/
TacticDoc rcases
/-- `ext i` reduces an equation between vectors (or matrices: `ext i j`, functions,
subspaces: `ext v`) to one component or element. -/
TacticDoc ext
/-- `fin_cases i` splits a goal about `i : Fin n` into one goal per value `0, …, n-1`. -/
TacticDoc fin_cases
/-- `have h : P := proof` adds a new fact; `have h := f a` specialises `f` to `a`. -/
TacticDoc «have»
/-- `calc a = b := by … _ = c := by …` proves a chain of equalities (or inequalities), each
step with its own justification. -/
TacticDoc «calc»
/-- `linear_combination e` proves an equation by adding up hypotheses: for example
`linear_combination h₂ - 3 * h₁`. Checks that goal − e is an identity (by `ring`). -/
TacticDoc linear_combination
/-- `rowop h : new_row := e` performs one Gaussian row operation: `e` combines equations as
in `linear_combination` (e.g. `h₂ - 3 * h₁` is −3ρ₁ + ρ₂). You write the new row; Lean checks
it, and the new row replaces `h`. -/
TacticDoc rowop
/-- `linarith` proves linear (in)equalities that follow from the hypotheses. -/
TacticDoc linarith
/-- `nlinarith` is `linarith` that also multiplies hypotheses together (for squares). -/
TacticDoc nlinarith
/-- `positivity` proves goals of the form `0 < e`, `0 ≤ e`, `e ≠ 0` from the shape of `e`. -/
TacticDoc positivity
/-- `ring` proves equalities in commutative algebra (`(a+b)^2 = a^2 + 2*a*b + b^2`). -/
TacticDoc ring
/-- `field_simp` clears denominators (given that they are nonzero); usually followed by
`ring`. -/
TacticDoc field_simp
/-- `module` proves equalities in a vector space by normalising both sides as linear
combinations (`a • u + b • (u + v) = (a + b) • u + b • v`). -/
TacticDoc «module»
/-- `simp` simplifies the goal with a large set of standard lemmas; `simp [h]` also uses
`h`; `simp only [lemmas]` uses only the given lemmas; `simp at h` simplifies `h`. -/
TacticDoc simp
/-- `apply f` reduces the goal to the hypotheses of `f` (works backwards). -/
TacticDoc apply
/-- `refine ⟨?_, ?_⟩` builds a term with holes `?_` that become new goals. -/
TacticDoc refine
/-- `exfalso` replaces the goal by `False` (to prove anything from a contradiction). -/
TacticDoc exfalso
/-- `by_contra h` assumes the negation of the goal as `h` and asks for `False`. -/
TacticDoc by_contra
/-- `by_cases h : P` splits into the case `h : P` and the case `h : ¬ P`. -/
TacticDoc by_cases
/-- `induction n with | zero => … | succ n ih => …` proves a statement for all natural
numbers. -/
TacticDoc induction
/-- `specialize h a` replaces `h : ∀ x, P x` by `h : P a`. -/
TacticDoc specialize
/-- `unfold f` replaces a defined name `f` by its definition. -/
TacticDoc unfold
/-- `omega` proves (in)equalities about natural numbers and integers. -/
TacticDoc omega
/-- `decide` proves a statement by evaluating it, when it is a finite check. -/
TacticDoc decide
/-- `trivial` closes simple goals such as `True`. -/
TacticDoc trivial
/-- `symm` turns a goal `a = b` into `b = a`. -/
TacticDoc symm
/-- `push_cast` moves casts (`↑`) outwards and simplifies them. -/
TacticDoc push_cast
/-- `eval_det` computes the determinant of a concrete matrix `!![…]`. A power tool, unlocked
once you have computed small determinants by hand. -/
TacticDoc eval_det
/-- `funext x` proves two functions equal by proving they agree at every `x`. -/
TacticDoc funext
/-- `congr 1` reduces `f a = f b` to `a = b`. -/
TacticDoc congr
/-- `subst h` substitutes a variable defined by `h : x = e` everywhere. -/
TacticDoc subst
/-- `contradiction` closes the goal if the hypotheses are contradictory in an obvious way. -/
TacticDoc contradiction
/-- `exact?` searches the library for a lemma that closes the goal. Never unlocked. -/
TacticDoc «exact?»
/-- `aesop` is a general-purpose automatic prover. Never unlocked. -/
TacticDoc aesop
/-- `rintro ⟨a, b⟩` is `intro` followed by `rcases`: it introduces and takes apart in one step. -/
TacticDoc rintro
/-- `choose f hf using h` turns `h : ∀ x, ∃ y, P x y` into a function `f` with `hf : ∀ x, P x (f x)`. -/
TacticDoc choose
/-- `match_scalars` reduces an equation between linear combinations of the same vectors to
equations between their coefficients. -/
TacticDoc match_scalars
/-- `show P` restates the goal in an equivalent (definitionally equal) form `P`. -/
TacticDoc «show»
