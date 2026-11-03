import DaughterGapInterior
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn EventSegmentGeometry
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
include hroot

/-- The first-return chain skips no original event on its physical carrier
between its initial and terminal parameters. -/
theorem gap_event_of_parameter (c : CornerCoord q hq.g2 S root) (x : PolygonEvent q)
    (he : polygonEventEdge q x = polygonEventEdge q (orbitEventAt q hq.g2 S root c.val))
    (hlo : polygonEventParameter q (orbitEventAt q hq.g2 S root c.val) ≤ polygonEventParameter q x)
    (hhi : polygonEventParameter q x < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three
      (lastDartStart q hq.g2 S root c)) :
    ∃ k : ℕ, k < cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val ∧
      x = (DartPerm q hq.g2 S ^ k) (orbitEventAt q hq.g2 S root c.val) := by
  letI := polygonEventOrder q hq.g2
  let start := orbitEventAt q hq.g2 S root c.val
  let d := cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val
  let f (j : ℕ) := (DartPerm q hq.g2 S ^ j) start
  obtain ⟨hd,_,_,_,_,hno⟩ := cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hroot c
  let J : Finset (Fin d) := Finset.univ.filter (fun j => polygonEventParameter q (f j.val) ≤ polygonEventParameter q x)
  have hJ : J.Nonempty := ⟨⟨0,hd⟩,by simpa [J,f] using hlo⟩
  let j := J.max' hJ
  have hjmem : j∈J := Finset.max'_mem J hJ
  have hj : polygonEventParameter q (f j.val) ≤ polygonEventParameter q x := (Finset.mem_filter.mp hjmem).2
  have hjedge : polygonEventEdge q (f j.val) = polygonEventEdge q start :=
    (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot c j.val j.isLt).1
  have hp : polygonEventParameter q x = polygonEventParameter q (f j.val) := by
    by_contra hne
    have hlt : polygonEventParameter q (f j.val) < polygonEventParameter q x := lt_of_le_of_ne hj (Ne.symm hne)
    let y := polygonEventSuccessor q hq.g2 (f j.val)
    have heq : polygonEventEdge q x = polygonEventEdge q (f j.val) := he.trans hjedge.symm
    rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three (f j.val) with hs | hs
    · have hyx : y ≤ x := hs.2.2 x heq hlt
      have hp_le : polygonEventParameter q y ≤ polygonEventParameter q x := by
        by_contra hh
        have hxlt : x<y := (polygonEvent_sameEdge_lt_iff q hq.g2 x y (heq.trans hs.1.symm)).mpr (lt_of_not_ge hh)
        exact (not_lt_of_ge hyx) hxlt
      by_cases hnext : j.val+1<d
      · have hn : ¬retainedCorner q S (DartPerm q hq.g2 S (f j.val)) := by
          simpa [f,pow_succ',Equiv.Perm.mul_apply] using hno (j.val+1) (by omega) hnext
        have hterm : ¬retainedCorner q S y := by
          intro ht
          apply hn
          exact (pairing_preserves_retained q S _).mpr ht
        have hstep : f (j.val+1)=y := by
          change (DartPerm q hq.g2 S ^ (j.val+1)) start = y
          rw [pow_succ',Equiv.Perm.mul_apply]
          exact pairing_fixes_noncorner q S _ hterm
        have hmem : (⟨j.val+1,hnext⟩ : Fin d)∈J := by
          apply Finset.mem_filter.mpr
          exact ⟨Finset.mem_univ _,by simpa only [hstep] using hp_le⟩
        have hh := Finset.le_max' J _ hmem
        change j.val+1≤j.val at hh
        omega
      · have hjlast : j.val=d-1 := by have := j.isLt;omega
        have hz : f j.val=lastDartStart q hq.g2 S root c := by rw [hjlast];rfl
        have hu := (polygonEventSuccessorTerminalParameter_spec q hq.g2 hq.size_ge_three (f j.val)).1 hs.1
        have hhi' : polygonEventParameter q x < polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three (f j.val) := by
          simpa only [hz] using hhi
        rw [hu] at hhi'
        exact (not_lt_of_ge hp_le) hhi'
    · exact (not_lt_of_ge (hs.2 x heq)) hlt
  refine ⟨j.val,j.isLt,?_⟩
  exact polygonEventKey_injective q hq.g2 (Prod.ext (he.trans hjedge.symm) hp)
end DirectGLSSW.DaughterClosedContainment
