import Game.Levels.Puzzles.L02_ReadSomething

World "Puzzles"
Level 3
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
are disjoint and nonempty; the last level, `biUnion_reads_nonempty`, connects \"reads some
book\" with \"nonempty\".

`Finset.univ.filter (fun i => 0 < c i)` is the set $\\{i : c_i > 0\\}$; membership is
`Finset.mem_filter` (and `Finset.mem_univ i : i ∈ Finset.univ`). An entry of the zero vector
shows as `0 i`; `Pi.zero_apply` turns it into `0`. An underscore `_` stands for an argument you do not need to name
(e.g. `fun j _ h1 h2 => …`) or one Lean can fill in itself.
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
  Hint (strict := true) "If one of the two sets is nonempty, its subscribers read some book, so
  the other set reads that book too — and is nonempty."
  Hint (strict := true) (hidden := true) "So the positive part is nonempty iff the negative part is:
  `have key : … ↔ … := by rw [← biUnion_reads_nonempty n reads hne, ← biUnion_reads_nonempty n reads hne, hbal]`."
  have key : (Finset.univ.filter (fun i => 0 < c i)).Nonempty ↔
      (Finset.univ.filter (fun i => c i < 0)).Nonempty := by
    rw [← biUnion_reads_nonempty n reads hne, ← biUnion_reads_nonempty n reads hne, hbal]
  Hint (strict := true) (hidden := true) "Some coefficient is nonzero: `obtain ⟨i, hi⟩ := Function.ne_iff.mp hc`."
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hc
  Hint (hidden := true) "`{hi}` shows `0 i`: entry `i` of the zero vector. `rw [Pi.zero_apply] at {hi}`
  makes it `c i ≠ 0`."
  rw [Pi.zero_apply] at hi
  refine ⟨Finset.univ.filter (fun i => 0 < c i), Finset.univ.filter (fun i => c i < 0),
    ?_, ?_, ?_, hbal⟩
  · Hint (hidden := true) "`rcases hi.lt_or_gt with h | h`: in one case use `key`, in the other
    `⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩` directly."
    rcases hi.lt_or_gt with h | h
    · exact key.mpr ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
  · rcases hi.lt_or_gt with h | h
    · exact ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
    · exact key.mp ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_univ i, h⟩⟩
  · Hint (hidden := true) "`exact Finset.disjoint_filter.mpr (fun j _ h1 h2 => by linarith)`"
    exact Finset.disjoint_filter.mpr (fun j _ h1 h2 => by linarith)

end LinearAlgebraGame

Conclusion "Linear dependence, split by sign, gives the two sets."

NewDefinition LinearAlgebraGame.bookVec
NewTheorem LinearAlgebraGame.biUnion_reads_nonempty LinearAlgebraGame.exists_relation LinearAlgebraGame.balance Function.ne_iff Finset.disjoint_filter Ne.lt_or_gt Finset.mem_filter
