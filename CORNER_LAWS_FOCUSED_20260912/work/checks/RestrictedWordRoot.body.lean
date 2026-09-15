namespace SM

noncomputable section
variable {n : ℕ} [NeZero n]

/-- Close the actual contiguous boundary word on J. Residue zero labels its
last vertex, so the edge at root zero runs from the last vertex to the first. -/
def restrictedWordTuple (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    LabelledTuple (J.leaves + 1) :=
  fun j => boundaryWord P g (J.globalPosition ⟨(j - 1).val, ZMod.val_lt _⟩)

theorem restrictedWord_boundary (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (k : Fin (J.leaves + 1)) :
    boundaryWord (restrictedWordTuple P g J) 0 k = boundaryWord P g (J.globalPosition k) := by
  unfold boundaryWord restrictedWordTuple boundaryIndex
  have hz : (0 + (k.val : ZMod (J.leaves + 1)) + 1) - 1 = (k.val : ZMod (J.leaves + 1)) := by ring
  simp only [hz, ZMod.val_natCast_of_lt k.isLt]
  rfl

theorem restrictedWord_first_vertex (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    restrictedWordTuple P g J 1 = boundaryWord P g J.left := by
  unfold restrictedWordTuple
  apply congrArg (boundaryWord P g)
  apply Fin.ext
  simp [BoundaryInterval.globalPosition]

theorem restrictedWord_last_vertex (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    restrictedWordTuple P g J 0 = boundaryWord P g J.right := by
  unfold restrictedWordTuple
  apply congrArg (boundaryWord P g)
  apply Fin.ext
  have hj := J.increasing
  change J.left.val < J.right.val at hj
  change J.left.val + (0 - 1 : ZMod (J.leaves + 1)).val = J.right.val
  rw [zero_sub, ZMod.val_neg_one]
  unfold BoundaryInterval.leaves
  omega

/-- The chosen local root is exactly the physical closing edge required by
the source: from a_j to a_i, with that directed displacement. -/
theorem restrictedWord_closing_edge (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n) :
    edge (restrictedWordTuple P g J) 0 = boundaryWord P g J.left - boundaryWord P g J.right := by
  simp only [edge, zero_add, restrictedWord_first_vertex, restrictedWord_last_vertex]

theorem BoundaryInterval.lift_fullInterval (J : BoundaryInterval n) (hJ : 2 ≤ J.leaves) :
    J.liftInterval (fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)) = J := by
  apply BoundaryInterval.eq_of_endpoints
  · apply Fin.ext
    simp [BoundaryInterval.liftInterval, BoundaryInterval.globalPosition, fullBoundaryInterval]
  · apply Fin.ext
    have hj := J.increasing
    change J.left.val < J.right.val at hj
    simp only [BoundaryInterval.liftInterval, BoundaryInterval.globalPosition, fullBoundaryInterval]
    unfold BoundaryInterval.leaves
    omega

variable {R : Type*} [CommRing R] [Invertible (2 : R)]

/-- Local geometric samples are exactly restrictions of the same physical
chirotope entries. No geometric genericity assumption is needed for this identity. -/
theorem geometricBoundaryArray_restrictedWord (P : LabelledTuple n) (g : ZMod n)
    (J : BoundaryInterval n) :
    geometricBoundaryArray (R := R) (restrictedWordTuple P g J) 0 =
      restrictTripleArray J (geometricBoundaryArray P g) := by
  funext t
  simp only [restrictTripleArray, geometricBoundaryArray, chi]
  change ((SignType.sign (det
    (boundaryWord (restrictedWordTuple P g J) 0 t.middle - boundaryWord (restrictedWordTuple P g J) 0 t.upper)
    (boundaryWord (restrictedWordTuple P g J) 0 t.lower - boundaryWord (restrictedWordTuple P g J) 0 t.upper)) : ℤ) : R) = _
  rw [restrictedWord_boundary, restrictedWord_boundary, restrictedWord_boundary]
  rfl

/-- Full source nonleaf restriction clause: whenever the closed endpoint word
satisfies G1, its tree coefficient at the physical closing root is exactly the
J coordinate of the original far-only output. No global G1 is added as a premise. -/
theorem farOnlyOutput_restricted_tree (P : LabelledTuple n) (g : ZMod n) (J : BoundaryInterval n)
    (hJ : 2 ≤ J.leaves) (hP : G1 (restrictedWordTuple P g J)) :
    farOnlyOutput (geometricBoundaryArray (R := R) P g) J =
      (treeCoefficient (restrictedWordTuple P g J) hP 0 (by omega : 3 ≤ J.leaves + 1) : R) := by
  let K := fullBoundaryInterval (by omega : 3 ≤ J.leaves + 1)
  have hr := congrFun (farOnlyOutput_restrict J (geometricBoundaryArray (R := R) P g)) K
  change farOnlyOutput (geometricBoundaryArray P g) (J.liftInterval K) =
    farOnlyOutput (restrictTripleArray J (geometricBoundaryArray P g)) K at hr
  rw [J.lift_fullInterval hJ, ← geometricBoundaryArray_restrictedWord P g J] at hr
  exact hr.trans (treeCoefficient_farOnly (restrictedWordTuple P g J) hP 0 (by omega)).symm

end
end SM
