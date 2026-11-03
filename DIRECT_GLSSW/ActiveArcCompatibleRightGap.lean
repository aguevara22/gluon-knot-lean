import ActiveArcRightVisitPrefix
import ActiveArcFilteredPrefixGap
import ActiveArcChildAuxiliary
import ActiveArcEventSideOfVisitInterval

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW PermutationOrbits RetainedWords SingletonWords Split Cursor
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (hAux : Primitive.ClosedAuxiliary q hR)
variable (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
  PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S})
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
include hAux

/-- The actual right crossing visit lies in precisely the retained gap at
the last index of the child prefix. The index and both strict physical
orders are derived from the full event splice, not assumed. -/
theorem compatible_right_visit_gap :
    let U : Primitive.Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let k := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length-1
    ∃ (hk : 0<k) (hkn : k+1<openCount q hR U.val),
      (eventOrder q hR.noTriple).lt
        (pairing q U.val (cornerEvent q hR U.val (start q) ⟨k,by change k<openCount q hR U.val;exact Nat.lt_of_succ_lt hkn⟩))
        (Sum.inr (c,true)) ∧
      (eventOrder q hR.noTriple).lt (Sum.inr (c,true))
        (cornerEvent q hR U.val (start q) ⟨k+1,hkn⟩) := by
  intro U k
  let m := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
    (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length
  have hQ := child_auxiliaryGenericity q hR c hc hcut hAux S.val S.property (Sum.inl 0)
  have hm3 : 3≤m := by
    simpa only [m,DaughterFirstReturn.daughterPointList,List.length_ofFn] using hQ.size_ge_three
  have hlen := congrArg List.length (unselected_open_pointWord_splice q hR c hc hcut S.val T.val)
  simp only [List.length_ofFn,List.length_cons,List.length_append,List.length_tail] at hlen
  change openCount q hR U.val = (m-1)+(openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1)+1 at hlen
  have hparent := open_count_ge_two (parent q c hcut) (regular_parent q hR c hcut) T.val
  have hmM : m<openCount q hR U.val := by omega
  obtain ⟨j,hje,hm⟩ := exists_right_visit_prefix_count q hR c hc hcut S.val T.val
  have hj : ¬retained q U.val (eventAt q hR U.val (start q) j) := by
    rw [hje]
    exact cut_not_mem_pieceSelections q hR c hc hcut S.val T.val
  have horder := open_gap_of_filtered_prefix_count q hR U.val j hj m (by omega) hmM hm
  rw [hje] at horder
  have hk : 0<k := by change 0<m-1;omega
  have hkn : k+1<openCount q hR U.val := by change m-1+1<_;omega
  have hkm : k+1=m := by change m-1+1=m;exact Nat.sub_add_cancel (by omega)
  refine ⟨hk,hkn,horder.1,?_⟩
  simpa only [hkm] using horder.2

/-- Genuine physical crossed-side incidence and transversality at the exact
child-prefix split index, with the finite gap hypotheses fully discharged. -/
theorem compatible_genuine_crossed_side :
    let U : Primitive.Support q hR := ⟨pieceSelections q hR c hc hcut S.val T.val,
      (pieceSelections_nonalternating_iff q hR c hc hcut S.val T.val).mpr ⟨S.property,T.property⟩⟩
    let k := (DaughterFirstReturn.daughterPointList (child q hR c hc.1 hcut)
      (child_noTriple q hR c hc.1 hcut) S.val (Sum.inl 0)).length-1
    ∃ (hk : 0<k) (hkn : k+1<openCount q hR U.val),
      (∃ s : ℝ, 0<s ∧ s<1 ∧ Primitive.eventOpenWord q hR U c 0 =
        affinePoint (Primitive.eventOpenWord q hR U c k) (Primitive.eventOpenWord q hR U c (k+1)) s) ∧
      planarDet (Primitive.eventOpenWord q hR U c 1-Primitive.eventOpenWord q hR U c 0)
        (Primitive.eventOpenWord q hR U c (k+1)-Primitive.eventOpenWord q hR U c k) ≠ 0 := by
  intro U k
  obtain ⟨hk,hkn,hv0,hv1⟩ := compatible_right_visit_gap q hR c hc hcut hAux S T
  exact ⟨hk,hkn,Primitive.eventOpenWord_genuine_side_of_right_visit_interval q hR c hc U
    (cut_not_mem_pieceSelections q hR c hc hcut S.val T.val) k hk hkn hv0 hv1⟩

end DirectGLSSW.ActiveArc.CompatibleWords
