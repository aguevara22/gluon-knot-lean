import MarkedCursorBoundary
import OriginalSuffixSurjective
import ProcessedArcSubsegmentTrace
import PLAdjacentSubsegmentJoint
set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits SmoothingCornerGeometry
attribute [local instance] Classical.propDecidable
namespace MarkedParentTrace

/-- The actual stored root has its original ancestry whenever one actual old
arc is given. This also applies to histories with no remaining crossing. -/
theorem boundary_root_origin {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (a : Fin t.1.nArc) (A : Fin s.1.nArc) (ha : h.arcOrigin a=some A) :
    h.arcOrigin (markedOrbitRoot t a)=some (markedOrbitRoot s A) := by
  induction h with
  | nil s =>
    have he : a=A := Option.some.inj ha
    subst A
    rfl
  | @cons s u t step tail ih =>
    cases hx : tail.arcOrigin a with
    | none => simp only [MarkedParentTrace.arcOrigin,hx,Option.none_bind] at ha;cases ha
    | some b =>
      have hb : step.arcOrigin b=some A := by
        simpa only [MarkedParentTrace.arcOrigin,hx,Option.some_bind] using ha
      change (tail.arcOrigin (markedOrbitRoot t a)).bind step.arcOrigin = _
      rw [ih a b hx,Option.some_bind]
      exact step.arcOrigin_root b A

variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (a : Fin t.1.nArc) (B : CursorBoundary t (visitPosition t.2.1 a))
include h a B

/-- Every actual arc beyond an arbitrary cursor boundary has an old ancestor. -/
theorem boundary_suffix_has_origin (i : Fin (markedSuffixSize t a)) :
    ∃ A : Fin s.1.nArc, h.arcOrigin (markedSuffixArc t a i)=some A := by
  cases hx : h.arcOrigin (markedSuffixArc t a i) with
  | some A => exact ⟨A,rfl⟩
  | none =>
    have hm := h.arcOrigin_none_marked _ hx
    exact (B.future_not_marked _ (by rw [markedSuffixArc_visitPosition];omega) hm).elim

/-- Ancestry is chosen only after its existence has been proved. -/
def boundaryOriginalArc (i : Fin (markedSuffixSize t a)) : Fin s.1.nArc :=
  Classical.choose (h.boundary_suffix_has_origin a B i)

theorem boundaryOriginalArc_spec (i : Fin (markedSuffixSize t a)) :
    h.arcOrigin (markedSuffixArc t a i)=some (h.boundaryOriginalArc a B i) :=
  Classical.choose_spec (h.boundary_suffix_has_origin a B i)

def boundaryOrigin : Fin s.1.nArc :=
  h.boundaryOriginalArc a B ⟨0,markedSuffixSize_pos t a⟩

theorem boundaryOrigin_spec : h.arcOrigin a=some (h.boundaryOrigin a B) := by
  have hh := h.boundaryOriginalArc_spec a B ⟨0,markedSuffixSize_pos t a⟩
  rw [markedSuffixArc_zero] at hh
  exact hh

theorem boundaryOriginalArc_successor (i j : Fin (markedSuffixSize t a))
    (hij : j.val=i.val+1) :
    s.1.continuation (h.boundaryOriginalArc a B i)=h.boundaryOriginalArc a B j :=
  h.arcOrigin_continuation _ _ _ _ (markedSuffixArc_successor t a i j hij)
    (h.boundaryOriginalArc_spec a B i) (h.boundaryOriginalArc_spec a B j)

theorem boundaryOriginalArc_ne_root (i : Fin (markedSuffixSize t a)) (hi : 0 < i.val) :
    h.boundaryOriginalArc a B i ≠ markedOrbitRoot s (h.boundaryOrigin a B) := by
  intro he
  have hs := h.boundaryOriginalArc_spec a B i
  rw [he] at hs
  have hr := h.boundary_root_origin a (h.boundaryOrigin a B) (h.boundaryOrigin_spec a B)
  have hh := h.arcOrigin_some_injective _ _ _ hs hr
  have hp := congrArg (visitPosition t.2.1) hh
  rw [markedSuffixArc_visitPosition,markedOrbitRoot_visitPosition] at hp
  omega

theorem boundaryOriginalArc_visitPosition (i : Fin (markedSuffixSize t a)) :
    visitPosition s.2.1 (h.boundaryOriginalArc a B i)=
      visitPosition s.2.1 (h.boundaryOrigin a B)+i.val := by
  have H : ∀ k (hk : k<markedSuffixSize t a),
      visitPosition s.2.1 (h.boundaryOriginalArc a B ⟨k,hk⟩)=
        visitPosition s.2.1 (h.boundaryOrigin a B)+k := by
    intro k
    induction k with
    | zero => intro hk;rfl
    | succ k ih =>
      intro hk
      have hk' : k<markedSuffixSize t a := by omega
      have hs := h.boundaryOriginalArc_successor a B ⟨k,hk'⟩ ⟨k+1,hk⟩ rfl
      have hn : s.1.continuation (h.boundaryOriginalArc a B ⟨k,hk'⟩) ≠
          (s.2.1.baseArc (componentOf s.1.continuation (h.boundaryOriginalArc a B ⟨k,hk'⟩))).val := by
        rw [hs]
        change h.boundaryOriginalArc a B ⟨k+1,hk⟩ ≠ markedOrbitRoot s _
        rw [markedOrbitRoot_eq s _ (h.boundaryOrigin a B)]
        exact h.boundaryOriginalArc_ne_root a B ⟨k+1,hk⟩ (Nat.succ_pos _)
      rw [← hs,visitPosition_continuation_of_ne_root s.1 s.2.1 _ hn,ih hk']
      omega
  exact H i.val i.isLt

/-- The ancestral word reaches the actual original root: no original tail arc
has silently disappeared in a past smoothing. -/
theorem boundaryOriginalArc_length :
    markedSuffixSize t a=markedSuffixSize s (h.boundaryOrigin a B) := by
  let i : Fin (markedSuffixSize t a) :=
    ⟨markedSuffixSize t a-1,by have := markedSuffixSize_pos t a;omega⟩
  have hr := h.boundary_root_origin a (h.boundaryOrigin a B) (h.boundaryOrigin_spec a B)
  have hs := h.arcOrigin_continuation _ _ _ _ (markedSuffixArc_last_continuation t a)
    (h.boundaryOriginalArc_spec a B i) hr
  have hp := h.boundaryOriginalArc_visitPosition a B i
  have hl := marked_visitPosition_of_continuation_root s (h.boundaryOrigin a B)
    (h.boundaryOriginalArc a B i) hs
  have hm := markedSuffixSize_pos t a
  change visitPosition s.2.1 (h.boundaryOriginalArc a B i) =
    visitPosition s.2.1 (h.boundaryOrigin a B)+(markedSuffixSize t a-1) at hp
  change markedSuffixSize t a=markedOrbitSize s (h.boundaryOrigin a B)-
    visitPosition s.2.1 (h.boundaryOrigin a B)
  omega

/-- Every actual future position is precisely the same original future position. -/
theorem boundaryOriginalArc_eq_original (i : Fin (markedSuffixSize t a)) :
    h.boundaryOriginalArc a B i=markedSuffixArc s (h.boundaryOrigin a B)
      (Fin.cast (h.boundaryOriginalArc_length a B) i) := by
  apply marked_visitPosition_injective s
  rw [h.boundaryOriginalArc_visitPosition a B i,markedSuffixArc_visitPosition]
  rfl

/-- Complete original suffix, not merely an injection or a retained subset. -/
theorem boundaryOriginalArc_range (e : Fin s.1.nArc) :
    (∃ i,h.boundaryOriginalArc a B i=e) ↔
      visitPosition s.2.1 (h.boundaryOrigin a B) ≤ visitPosition s.2.1 e := by
  constructor
  · rintro ⟨i,rfl⟩;rw [h.boundaryOriginalArc_visitPosition a B i];omega
  · intro he
    obtain ⟨j,hj⟩ := (markedSuffixArc_range s (h.boundaryOrigin a B) e).mpr he
    let i := Fin.cast (h.boundaryOriginalArc_length a B).symm j
    refine ⟨i,?_⟩
    rw [h.boundaryOriginalArc_eq_original a B i]
    exact hj
/-- Literal subsegment coordinates of every actual future arc. -/
theorem boundaryOriginalArc_subsegment (i : Fin (markedSuffixSize t a)) :
    ∃ u v : ℝ, 0≤u ∧ u<v ∧ v≤1 ∧
      t.1.vertexPoint (t.1.arcSource (markedSuffixArc t a i)) =
        affinePoint (s.1.vertexPoint (s.1.arcSource (h.boundaryOriginalArc a B i)))
          (s.1.vertexPoint (s.1.arcTarget (h.boundaryOriginalArc a B i))) u ∧
      t.1.vertexPoint (t.1.arcTarget (markedSuffixArc t a i)) =
        affinePoint (s.1.vertexPoint (s.1.arcSource (h.boundaryOriginalArc a B i)))
          (s.1.vertexPoint (s.1.arcTarget (h.boundaryOriginalArc a B i))) v :=
  h.arcOrigin_subsegment _ _ (h.boundaryOriginalArc_spec a B i)

/-- Every interior joint of the complete actual tail is the original joint. -/
theorem boundaryOriginalArc_shared_vertex (i j : Fin (markedSuffixSize t a))
    (hij : j.val=i.val+1) :
    t.1.vertexPoint (t.1.arcTarget (markedSuffixArc t a i)) =
      s.1.vertexPoint (s.1.arcTarget (h.boundaryOriginalArc a B i)) ∧
    t.1.vertexPoint (t.1.arcSource (markedSuffixArc t a j)) =
      s.1.vertexPoint (s.1.arcSource (h.boundaryOriginalArc a B j)) := by
  obtain ⟨u,v,hu,huv,hv,hes,het⟩ := h.boundaryOriginalArc_subsegment a B i
  obtain ⟨r,z,hr,hrz,hz,hfs,hft⟩ := h.boundaryOriginalArc_subsegment a B j
  have hstep := markedSuffixArc_successor t a i j hij
  have hinc := t.1.continuation_incidence (markedSuffixArc t a i)
  rw [hstep] at hinc
  have hab := h.boundaryOriginalArc_successor a B i j hij
  have hshared : t.1.vertexPoint (t.1.arcTarget (markedSuffixArc t a i)) =
      affinePoint (s.1.vertexPoint (s.1.arcSource (h.boundaryOriginalArc a B j)))
        (s.1.vertexPoint (s.1.arcTarget (h.boundaryOriginalArc a B j))) r := by
    rw [hinc]
    exact hfs
  have hjoint := adjacent_subsegment_joint s.1
    (h.boundaryOriginalArc a B i) (h.boundaryOriginalArc a B j) hab _ v r
    (lt_of_le_of_lt hu huv) hv hr (lt_of_lt_of_le hrz hz) het hshared
  refine ⟨hjoint,?_⟩
  rw [← hinc,hjoint]
  have hi := s.1.continuation_incidence (h.boundaryOriginalArc a B i)
  rw [hab] at hi
  exact congrArg s.1.vertexPoint hi

end MarkedParentTrace
end DirectGLSSW.HOMFLY
