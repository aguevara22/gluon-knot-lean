namespace SM.SoftDuplication

noncomputable section
variable {n : ℕ} [NeZero n]

/-- The concrete old-section ordered triple is the previously defined old triple. -/
theorem startingOld_triple_eq (s : Fin n) (T : IncreasingBoundaryTriple n) :
    OrderedBoundaryTransport.triple (startingOldEmbedding s) T = oldTriple s T := by
  apply triple_ext <;> rfl

/-- The actual alternate section omits A, including at either endpoint. -/
theorem startingTail_ne_A (s k : Fin n) : startingTailEmbedding s k ≠ A s :=
  Fin.succAbove_ne (A s) k

/-- A tail image cannot contain both occurrences because it contains no A. -/
theorem startingTail_triple_plain (s : Fin n) (T : IncreasingBoundaryTriple n) :
    ¬ tripleContainsBoth s (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) := by
  intro h
  rcases h.1 with h | h | h
  · exact startingTail_ne_A s T.lower h
  · exact startingTail_ne_A s T.middle h
  · exact startingTail_ne_A s T.upper h

/-- Collapse recovers every actual tail triple, with no caller-supplied section. -/
theorem collapse_startingTail_triple (s : Fin n) (T : IncreasingBoundaryTriple n)
    (hplain : ¬ tripleContainsBoth s
      (OrderedBoundaryTransport.triple (startingTailEmbedding s) T)) :
    collapseTriple s (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) hplain = T := by
  apply triple_ext
  · exact collapse_startingTail s T.lower
  · exact collapse_startingTail s T.middle
  · exact collapse_startingTail s T.upper

/-- Every actual old-image gate has the exact core array value. -/
theorem tripleLift_startingOld {R : Type*} (s : Fin n) (H0 : TripleArray n R)
    (t : Fin n → R) (T : IncreasingBoundaryTriple n) :
    tripleLift s H0 t (OrderedBoundaryTransport.triple (startingOldEmbedding s) T) = H0 T := by
  rw [startingOld_triple_eq, tripleLift_oldTriple]

/-- Every actual tail-image gate has the exact core array value. -/
theorem tripleLift_startingTail {R : Type*} (s : Fin n) (H0 : TripleArray n R)
    (t : Fin n → R) (T : IncreasingBoundaryTriple n) :
    tripleLift s H0 t (OrderedBoundaryTransport.triple (startingTailEmbedding s) T) = H0 T := by
  rw [tripleLift_plain s H0 t _ (startingTail_triple_plain s T),
    collapse_startingTail_triple]

end
end SM.SoftDuplication
