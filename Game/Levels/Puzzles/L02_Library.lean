import Game.Levels.Puzzles.L01_Arbuzoids

World "Puzzles"
Level 2
Title "The library"

-- @sheet 4 Q12
/-! @answer
Encode subscriber $i$ by the vector $\vec v_i \in \mathbb R^n$ with a $1$ in position $b$ iff
$i$ reads book $b$. These are $n+1$ vectors in $\mathbb R^n$, so they are linearly dependent:
$\sum_i c_i \vec v_i = \vec 0$ with some $c_i \ne 0$. Let $I = \{i : c_i > 0\}$ and
$J = \{i : c_i < 0\}$ (disjoint). Then $\sum_{i\in I} c_i\vec v_i = \sum_{i\in J}(-c_i)\vec v_i$;
both sides have nonnegative entries, and entry $b$ is positive exactly when some subscriber in
the set reads book $b$. So $I$ and $J$ read exactly the same books. Both are nonempty: some
$c_i \ne 0$, so one of them is nonempty, and its subscribers read at least one book, which
then must be read by someone in the other set.
**Edge case:** the hypothesis that every subscriber reads at least one book is needed. With
$n = 1$ and subscribers reading $\emptyset$ and $\{1\}$ the only nonempty disjoint sets are
the two singletons, which read different books.
-/
Introduction "
**Problem Sheet 4, Question 12 (optional).** A library has $n$ books and $n + 1$
subscribers. Each subscriber reads some subset of books from the library. Prove that there
must exist two disjoint nonempty sets of subscribers who read exactly the same books (that
is, the union of the books read by the subscribers is the same for both sets).

**An added hypothesis.** As stated the claim is false: with one book and two subscribers, one
reading nothing and one reading the book, the only disjoint nonempty sets are the two
singletons, and they read different books. So we assume every subscriber reads at least one
book (`hne`). Raise this in your tutorial!

Subscriber $i$ reads `reads i`, a finite set of books. The linear algebra: `bookVec reads i` is
$i$'s 0/1 reading vector in $\\mathbb R^n$; `exists_relation` gives a nontrivial relation among
these $n+1$ vectors, and `balance` (granted) says the subscribers with positive coefficient read
the same books as those with negative coefficient. Your job: choose the two sets and show they
are disjoint and nonempty.
"

namespace LinearAlgebraGame

/-- Two disjoint nonempty sets of subscribers read exactly the same books. -/
Statement (n : ℕ) (reads : Fin (n + 1) → Finset (Fin n)) (hne : ∀ i, (reads i).Nonempty) :
    ∃ I J : Finset (Fin (n + 1)), I.Nonempty ∧ J.Nonempty ∧ Disjoint I J ∧
      I.biUnion reads = J.biUnion reads := by
  Hint "Get the dependence relation and the balance between its positive and negative parts."
  Hint (hidden := true) "`obtain ⟨c, hc, hrel⟩ := exists_relation (bookVec reads)` and
  `have hbal := balance reads c hrel`."
  obtain ⟨c, hc, hrel⟩ := exists_relation (bookVec reads)
  have hbal := balance reads c hrel
  Hint (strict := true) "A set of subscribers reads some book iff it is nonempty (everyone reads something)."
  Hint (strict := true) (hidden := true) "`have e : ∀ s : Finset (Fin (n + 1)), (s.biUnion reads).Nonempty ↔ s.Nonempty := by`
  `intro s`, `rw [Finset.biUnion_nonempty]`, `constructor`, …"
  have e : ∀ s : Finset (Fin (n + 1)), (s.biUnion reads).Nonempty ↔ s.Nonempty := by
    intro s
    rw [Finset.biUnion_nonempty]
    constructor
    · intro h
      obtain ⟨x, hx, _⟩ := h
      exact ⟨x, hx⟩
    · intro h
      obtain ⟨x, hx⟩ := h
      exact ⟨x, hx, hne x⟩
  Hint (strict := true) (hidden := true) "So the positive part is nonempty iff the negative part is:
  `have key : … ↔ … := by rw [← e, ← e, hbal]`."
  have key : (Finset.univ.filter (fun i => 0 < c i)).Nonempty ↔
      (Finset.univ.filter (fun i => c i < 0)).Nonempty := by
    rw [← e, ← e, hbal]
  Hint (strict := true) (hidden := true) "Some coefficient is nonzero: `obtain ⟨i, hi⟩ := Function.ne_iff.mp hc`."
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  refine ⟨Finset.univ.filter (fun i => 0 < c i), Finset.univ.filter (fun i => c i < 0),
    ?_, ?_, ?_, hbal⟩
  · Hint (hidden := true) "`rcases hi.lt_or_gt with h | h`: in one case use `key`, in the other
    `⟨i, Finset.mem_filter.mpr ⟨by simp, h⟩⟩` directly."
    rcases hi.lt_or_gt with h | h
    · exact key.mpr ⟨i, Finset.mem_filter.mpr ⟨by simp, h⟩⟩
    · exact ⟨i, Finset.mem_filter.mpr ⟨by simp, h⟩⟩
  · rcases hi.lt_or_gt with h | h
    · exact ⟨i, Finset.mem_filter.mpr ⟨by simp, h⟩⟩
    · exact key.mp ⟨i, Finset.mem_filter.mpr ⟨by simp, h⟩⟩
  · Hint (hidden := true) "`exact Finset.disjoint_filter.mpr (fun j _ h1 h2 => by linarith)`"
    exact Finset.disjoint_filter.mpr (fun j _ h1 h2 => by linarith)

end LinearAlgebraGame

Conclusion "Linear dependence, split by sign, gives the two sets."

NewDefinition LinearAlgebraGame.bookVec
NewTheorem LinearAlgebraGame.exists_relation LinearAlgebraGame.balance Finset.biUnion_nonempty Function.ne_iff Finset.disjoint_filter Ne.lt_or_gt Finset.mem_filter
