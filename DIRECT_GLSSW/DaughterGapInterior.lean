import DaughterInteriorCarrier
import Mathlib.Tactic.FieldSimp
set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.DaughterClosedContainment
open DaughterFirstReturn EventSegmentGeometry
variable {n : ℕ} (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (S : Finset (PolygonCrossing q)) (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
include hroot

theorem gap_parameter_step (c : CornerCoord q hq.g2 S root) (k : ℕ)
    (hk : k+1 < cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val) :
    polygonEventParameter q ((DartPerm q hq.g2 S ^ k) (orbitEventAt q hq.g2 S root c.val)) <
      polygonEventParameter q ((DartPerm q hq.g2 S ^ (k+1)) (orbitEventAt q hq.g2 S root c.val)) := by
  let start := orbitEventAt q hq.g2 S root c.val
  let x := (DartPerm q hq.g2 S ^ k) start
  obtain ⟨_,_,_,_,_,hno⟩ := cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hroot c
  have hn : ¬ retainedCorner q S (DartPerm q hq.g2 S x) := by
    simpa [x,pow_succ',Equiv.Perm.mul_apply] using hno (k+1) (by omega) hk
  have ht : ¬ retainedCorner q S (polygonEventSuccessor q hq.g2 x) := by
    intro h
    apply hn
    exact (pairing_preserves_retained q S _).mpr h
  have hs : DartPerm q hq.g2 S x = polygonEventSuccessor q hq.g2 x :=
    pairing_fixes_noncorner q S _ ht
  have hd : (DartPerm q hq.g2 S ^ (k+1)) start = polygonEventSuccessor q hq.g2 x := by
    simpa [x,pow_succ',Equiv.Perm.mul_apply] using hs
  change polygonEventParameter q x < polygonEventParameter q ((DartPerm q hq.g2 S ^ (k+1)) start)
  rw [hd]
  rcases polygonEventSuccessor_sameEdge_next_or_nextAnchor q hq.g2 hq.size_ge_three x with he | he
  · exact he.2.1
  · exact (ht (by rw [he.1];exact True.intro)).elim

theorem gap_parameter_mono (c : CornerCoord q hq.g2 S root) (j : ℕ)
    (hj : j < cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val)
    (i : ℕ) (hij : i ≤ j) :
    polygonEventParameter q ((DartPerm q hq.g2 S ^ i) (orbitEventAt q hq.g2 S root c.val)) ≤
      polygonEventParameter q ((DartPerm q hq.g2 S ^ j) (orbitEventAt q hq.g2 S root c.val)) := by
  induction j with
  | zero =>
    have hi : i=0 := by omega
    subst i
    exact le_rfl
  | succ j ih =>
    by_cases he : i=j+1
    · subst i;exact le_rfl
    · exact (ih (by omega) (by omega)).trans
        (le_of_lt (gap_parameter_step q hq S root hroot c j hj))

/-- Each strict finite first-return offset is a genuine strict physical
interior point of the corresponding sharp daughter side. -/
theorem gap_event_in_daughter_interior
    (i : Fin (Fintype.card (CornerCoord q hq.g2 S root))) (k : ℕ)
    (hk0 : 0 < k)
    (hk : k < cornerGap q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val
      (cornerSuccessor q hq.g2 S root (cornerEnumeration q hq.g2 S root i)).val) :
    edgeInterior (daughterVertex q hq.g2 S root) i
      (polygonEventPoint q ((DartPerm q hq.g2 S ^ k)
        (orbitEventAt q hq.g2 S root (cornerEnumeration q hq.g2 S root i).val))) := by
  let c := cornerEnumeration q hq.g2 S root i
  let start := orbitEventAt q hq.g2 S root c.val
  let d := cornerGap q hq.g2 S root c.val (cornerSuccessor q hq.g2 S root c).val
  let z := lastDartStart q hq.g2 S root c
  let x := (DartPerm q hq.g2 S ^ k) start
  let e := polygonEventEdge q start
  let u := polygonEventSuccessorTerminalParameter q hq.g2 hq.size_ge_three z
  obtain ⟨hd,hnext,_,hpoint,_,_⟩ := cornerSuccessor_is_firstReturn q hq.g2 S hq.size_ge_three root hroot c
  have hk' : k<d := hk
  have hm : d-1<d := by omega
  have hpref := orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot c (d-1) hm
  have hzedge : polygonEventEdge q z = e := hpref.1
  have hxedge : polygonEventEdge q x = e :=
    (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot c k hk).1
  have hlow : polygonEventParameter q start < polygonEventParameter q x := by
    have hle := (orbitPrefix_edge_parameter q hq.g2 S hq.size_ge_three root hroot c (k-1) (by omega)).2
    have hlt := gap_parameter_step q hq S root hroot c (k-1) (by omega)
    rw [Nat.sub_add_cancel hk0] at hlt
    exact hle.trans_lt hlt
  have hhigh : polygonEventParameter q x < u := by
    have hle := gap_parameter_mono q hq S root hroot c (d-1) hm k (by omega)
    exact hle.trans_lt (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three z).1
  have hs : daughterVertex q hq.g2 S root i =
      affinePoint (q e) (q (cyclicSuccessor e)) (polygonEventParameter q start) :=
    polygonEventPoint_eq_affine q start
  have ht : daughterVertex q hq.g2 S root (cyclicSuccessor i) =
      affinePoint (q e) (q (cyclicSuccessor e)) u := by
    change polygonEventPoint q (orbitEventAt q hq.g2 S root
      (cornerEnumeration q hq.g2 S root (cyclicSuccessor i)).val) = _
    rw [cornerEnumeration_successor,←hnext,hpoint]
    simpa only [hzedge] using
      (polygonEventSuccessor_positive_elementary_step q hq.g2 hq.size_ge_three z).2.2.2.1
  have hx : polygonEventPoint q x =
      affinePoint (q e) (q (cyclicSuccessor e)) (polygonEventParameter q x) := by
    simpa only [hxedge] using polygonEventPoint_eq_affine q x
  have hden : 0 < u-polygonEventParameter q start := sub_pos.mpr (hlow.trans hhigh)
  refine ⟨(polygonEventParameter q x-polygonEventParameter q start)/(u-polygonEventParameter q start),
    div_pos (sub_pos.mpr hlow) hden,?_,?_⟩
  · exact (div_lt_one hden).mpr (by linarith)
  · change polygonEventPoint q x = _
    rw [hs,ht,hx]
    ext <;> simp [affinePoint] <;> field_simp [ne_of_gt hden] <;> ring
end DirectGLSSW.DaughterClosedContainment
