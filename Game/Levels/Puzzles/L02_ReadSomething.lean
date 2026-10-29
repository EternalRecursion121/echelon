import Game.Levels.Puzzles.L01_Arbuzoids

World "Puzzles"
Level 2
Title "Everyone reads something"

Introduction "
A warm-up for the next puzzle (Sheet 4 Q12). A library has $n$ books and $n+1$ subscribers;
subscriber $i$ reads `reads i`, a finite set of books, and we assume **everyone reads at least
one book** (`hne`). For a set `s` of subscribers, `s.biUnion reads` is the set of all books
read by someone in `s`.

**Prove:** a set of subscribers reads some book exactly when the set is nonempty.

`Finset.biUnion_nonempty : (s.biUnion t).Nonempty ↔ ∃ x ∈ s, (t x).Nonempty`, and
`s.Nonempty` means `∃ x, x ∈ s`.
"

namespace LinearAlgebraGame

/-- If every subscriber reads a book, a set of subscribers reads some book iff it is nonempty. -/
Statement biUnion_reads_nonempty (n : ℕ) (reads : Fin (n + 1) → Finset (Fin n))
    (hne : ∀ i, (reads i).Nonempty) (s : Finset (Fin (n + 1))) :
    (s.biUnion reads).Nonempty ↔ s.Nonempty := by
  Hint "Both directions: a reader of some book is a member of `s`; a member of `s` reads
  something by `hne`."
  Hint (hidden := true) "`rw [Finset.biUnion_nonempty]`, then `constructor`."
  rw [Finset.biUnion_nonempty]
  constructor
  · Hint (hidden := true) "`intro h`, `obtain ⟨x, hx, _⟩ := h`, `exact ⟨x, hx⟩`."
    intro h
    obtain ⟨x, hx, _⟩ := h
    exact ⟨x, hx⟩
  · Hint (hidden := true) "`intro h`, `obtain ⟨x, hx⟩ := h`, `exact ⟨x, hx, hne x⟩`."
    intro h
    obtain ⟨x, hx⟩ := h
    exact ⟨x, hx, hne x⟩

end LinearAlgebraGame

Conclusion "Without `hne` only one direction would survive — keep an eye on that hypothesis."

NewTheorem Finset.biUnion_nonempty
TheoremTab "Puzzles"
