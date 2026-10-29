import Game.Metadata
import Game.Ch1

World "Puzzles"
Level 1
Title "Arbuzoids"

-- @sheet 1 Q13
/-! @answer
**Never.** Write a state as $(R, G, B)$. Every meeting changes the counts by
$(-1,-1,+2)$, $(-1,+2,-1)$ or $(+2,-1,-1)$, so $R - G$ changes by $0$ or $\pm 3$: the value of
$R - G \bmod 3$ is invariant (a linear invariant over $\mathbb Z/3$). Initially
$R - G = 13 - 15 = -2 \equiv 1 \pmod 3$. If all were blue then $R = G = 0$ and
$R - G \equiv 0$. So they can never all become blue.
-/
Introduction "
**Problem Sheet 1, Question 13 (optional).** There's a planet inhabited by arbuzoids. Those
creatures are found in three colours: red, green and blue. There are 13 red arbuzoids, 15
green ones, and 17 blue. When two differently coloured arbuzoids meet, they both change to
the third colour. Can they ever all become blue at the same time?

A state is a triple (red, green, blue) of integers. `Meet s t` is one meeting, and
`Reachable s t` means some finite sequence of meetings leads from `s` to `t`. All blue means
the state $(0, 0, 45)$. Use linear algebra: find a quantity that no meeting changes.

`x % 3` is the remainder of the integer `x` on division by 3. New:
`Int.add_mul_emod_self_left a b c : (a + b * c) % b = a % b` — adding a multiple of 3 does not
change the remainder.
"

namespace LinearAlgebraGame

/-- The arbuzoids can never all be blue. -/
Statement : ¬ Reachable (13, 15, 17) (0, 0, 45) := by
  intro h
  Hint "Look at red − green modulo 3. Prove it stays the same along every sequence of meetings."
  Hint (hidden := true) "`have key : ∀ s, Reachable (13, 15, 17) s → (s.1 - s.2.1) % 3 = 1 := by`
  then `intro s hs` and `induction hs with` `| refl => …` `| tail _ hstep ih => …`."
  have key : ∀ s, Reachable (13, 15, 17) s → (s.1 - s.2.1) % 3 = 1 := by
    intro s hs
    induction hs with
    | refl => norm_num
    | tail _ hstep ih =>
      Hint (hidden := true) "Split the last meeting into its three kinds:
      `rcases hstep with ⟨r, g, b, _, _⟩ | ⟨r, g, b, _, _⟩ | ⟨r, g, b, _, _⟩ <;> simp only at ih ⊢`.
      In each case write the new red − green as the old one plus a multiple of 3, e.g.
      `have e : r - 1 - (g + 2) = r - g + 3 * (-1) := by ring`, then
      `rw [e, Int.add_mul_emod_self_left]` and `exact ih`."
      rcases hstep with ⟨r, g, b, _, _⟩ | ⟨r, g, b, _, _⟩ | ⟨r, g, b, _, _⟩ <;> simp only at ih ⊢
      · have e : r - 1 - (g - 1) = r - g := by ring
        rw [e]
        exact ih
      · have e : r - 1 - (g + 2) = r - g + 3 * (-1) := by ring
        rw [e, Int.add_mul_emod_self_left]
        exact ih
      · have e : r + 2 - (g - 1) = r - g + 3 * 1 := by ring
        rw [e, Int.add_mul_emod_self_left]
        exact ih
  have h1 := key _ h
  Hint (hidden := true) "`norm_num at h1`"
  norm_num at h1

end LinearAlgebraGame

Conclusion "**Answer: never** — red − green is $1$ mod $3$ forever, but all-blue needs $0$."

NewDefinition LinearAlgebraGame.Meet LinearAlgebraGame.Reachable
TheoremTab "Puzzles"
NewTheorem Int.add_mul_emod_self_left refl
