import Game.Levels.ChangeOfBasis.L05_EquivalentRank

World "ChangeOfBasis"
Level 6
Title "The block identity normal form"

Introduction "
**Boss.** Hefferon Theorem Three.V.2.7: every $m\\times n$ matrix of rank $k$ is matrix
equivalent to the block matrix
$$\\begin{pmatrix} I_k & 0 \\\\ 0 & 0 \\end{pmatrix}$$
(`blockId m n k`). Together with the last level: two matrices are equivalent iff they have
the same rank.

The dimension-counting heart of the proof is granted as `exists_bases_blockId`: there are bases
$B$ of $\\mathbb R^n$ and $D$ of $\\mathbb R^m$ with respect to which $\\vec x \\mapsto H\\vec x$ is
represented by the block identity (send a basis of a complement of the null space to a basis of
the range, and the null space to zero). Your job is the change of basis: turn those bases into
$P$ and $Q$. Also granted:
* `exists_cob_from B hB`: a nonsingular $Q$ with $Q = \\mathrm{Rep}_{B,\\mathcal E}(\\mathrm{id})$;
* `exists_cob_to D hD`: a nonsingular $P$ with $P = \\mathrm{Rep}_{\\mathcal E,D}(\\mathrm{id})$;
* `isRep_mulVecLin H`: $H = \\mathrm{Rep}_{\\mathcal E,\\mathcal E}(\\vec x \\mapsto H\\vec x)$.
"

namespace LinearAlgebraGame

/-- Every matrix of rank $k$ is equivalent to the block identity of size $k$. -/
Statement {m n : ℕ} (H : Matrix (Fin m) (Fin n) ℝ) : MatEquiv H (blockId m n H.rank) := by
  Hint "Start from the granted good bases $B$, $D$, then build the two change-of-basis matrices."
  Hint (hidden := true) "`obtain ⟨B, D, hB, hD, hrep⟩ := exists_bases_blockId H`."
  obtain ⟨B, D, hB, hD, hrep⟩ := exists_bases_blockId H
  Hint "Now the two change-of-basis matrices."
  obtain ⟨Q, hQ, hQrep⟩ := exists_cob_from B hB
  obtain ⟨P, hP, hPrep⟩ := exists_cob_to D hD
  refine ⟨P, Q, hP, hQ, ?_⟩
  Hint "Both $PHQ$ and the block identity represent $\\vec x \\mapsto H\\vec x$ with respect to $B$, $D$. Representations are unique."
  Hint (hidden := true) "Arrow diagram: $B \\xrightarrow\{\\mathrm\{id}} \\mathcal E \\xrightarrow\{H} \\mathcal E
  \\xrightarrow\{\\mathrm\{id}} D$. Compose the three representations with `isRep_comp`."
  Hint (hidden := true) "`have h := isRep_comp (isRep_comp {hQrep} (isRep_mulVecLin H)) {hPrep}`"
  have h := isRep_comp (isRep_comp hQrep (isRep_mulVecLin H)) hPrep
  Hint (hidden := true) "`rw [LinearMap.comp_id, LinearMap.id_comp, ← Matrix.mul_assoc] at h`;
  now both `{hrep}` and `h` represent the same map with respect to $B, D$."
  rw [LinearMap.comp_id, LinearMap.id_comp, ← Matrix.mul_assoc] at h
  exact isRep_unique hD hrep h

end LinearAlgebraGame

Conclusion "
Matrix equivalence classes are classified by rank: an $m\\times n$ matrix is equivalent to
exactly one $\\begin{pmatrix} I_k & 0 \\\\ 0 & 0\\end{pmatrix}$, namely the one with $k$ = its rank.
"

NewDefinition LinearAlgebraGame.blockId
NewTheorem LinearAlgebraGame.exists_bases_blockId LinearAlgebraGame.exists_cob_from LinearAlgebraGame.exists_cob_to LinearAlgebraGame.isRep_mulVecLin
DisabledTheorem Matrix.exists_rank_normal_form
TheoremTab "Change of basis"
