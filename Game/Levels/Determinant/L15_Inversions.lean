import Game.Levels.Determinant.L14_IntegerSolution

World "Determinant"
Level 15
Title "Swaps and inversions"

-- @sheet 9 Q1
/-! @answer
Let $P_\phi$ have $m$ inversions. If $m > 0$, some *adjacent* pair of rows is out of order
(otherwise the rows would be sorted and $\phi$ would be the identity). Swapping that
adjacent pair removes exactly that one inversion and changes no other pair's relative
order, so the count drops to $m-1$. Repeating (bubble sort) reaches the identity in exactly
$m$ adjacent swaps. Corollary 4.5 says that *every* sequence of swaps taking $P_\phi$ to the
identity has length of the same parity as $m$. If non-adjacent swaps are allowed the route
can be much shorter than $m$ (e.g. the reversal of $1,\dots,n$ has $\binom n2$ inversions but
needs only $\lfloor n/2\rfloor$ swaps) — only the parity is fixed, not the length.
-/
Introduction "
**Problem Sheet 9, Question 1.** Show that there is a way to row swap a permutation
matrix with $m$ inversions to the identity in exactly $m$ steps. Contrast this with
Corollary 4.5 on page 349.

*This is an explain level.* The key step of the argument is: **every permutation
$\\sigma \\ne 1$ has an adjacent swap that lowers the number of inversions by exactly one.**
Lean checks this exhaustively for all $24$ permutations of $4$ elements; `decide` does the
checking. Then, inside your proof, write the general argument (induction on $m$) and the
contrast with Corollary 4.5 as a comment block starting `-- Explain:`.

Here `inversions σ` counts pairs $i < j$ with $\\sigma(j) < \\sigma(i)$, and
`Equiv.swap i.castSucc i.succ` swaps positions $i$ and $i+1$.
"

namespace LinearAlgebraGame

/-- Every non-identity permutation of four elements has an adjacent swap that lowers its
number of inversions by exactly one. -/
Statement : ∀ σ : Equiv.Perm (Fin 4), σ ≠ 1 →
    ∃ i : Fin 3, inversions (σ * Equiv.swap i.castSucc i.succ) + 1 = inversions σ := by
  Hint "There are only $24$ permutations of four elements, so the claim can be checked case
  by case — by the machine. Then add your `-- Explain:` comment with the general argument."
  Hint (hidden := true) "`decide` runs the finite check."
  Hint (hidden := true) "Model explanation: if $\\sigma \\ne 1$ some adjacent pair is
  inverted; swapping it removes exactly that inversion, so by induction $m$ adjacent swaps
  reach the identity. Corollary 4.5 only fixes the *parity* of the number of swaps: with
  arbitrary swaps you can often do it in fewer than $m$ steps, but never in a number of
  steps of the other parity."
  decide

end LinearAlgebraGame

Conclusion "
Repeating the step $m$ times sorts the permutation: $m$ adjacent swaps, exactly. Corollary
4.5 only says that any route has length $\\equiv m \\pmod 2$.
"

NewDefinition LinearAlgebraGame.inversions

TheoremTab "Det"
