import OpenCurrentGenuineBoundary
import PositiveLiftFirstEncounter
import DirectGLSSW.ExtendedReturnLocalCaps
import DirectGLSSW.HorizontalShortEdge

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW
open EndpointEventGeometry

private theorem finite_noncollinear_of_core (W : ℕ → PlanarPoint ℝ) (N : ℕ)
    (hcore : ShortEdgeSignStability.CoreHGeneric W N) :
    cyclicNoncollinear (fun i : Fin (N+1) => W i.val) := by
  intro i j k hij hjk hik
  exact ExtendedReturnLocalCaps.bounded_hdet_ne_of_distinct W N hcore
    i.val j.val k.val (by omega) (by omega) (by omega)
    (by intro h; exact hij (Fin.ext h))
    (by intro h; exact hjk (Fin.ext h))
    (by intro h; exact hik (Fin.ext h))

/-- The same genuine boundary current formula together with its canonical
first physical branch's positive-lift over/under signs. The crossing is
constructed in the pre-event finite word, not in the nongeneric event word. -/
theorem exists_genuine_boundary_polygon_jump_positive
    (hRI : GLSSWRootIndependence) (W : ℕ → PlanarPoint ℝ)
    (N k : ℕ) (hKN : k<N) (s : ℝ) (hs0 : 0<s) (hs1 : s<1)
    (hcross : W 0=affinePoint (W k) (W (k+1)) s)
    (htrans : planarDet (W 1-W 0) (W (k+1)-W k)≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠k+1) → polygonHDet W a b d≠0)
    (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) (-ε)) N ∧
      (OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (W 1-W 0) ε)) 0 N -
        OpenMarkedCurrent.entry (polygonSignArray (moveEndpoint W (W 1-W 0) (-ε))) 0 N =
      scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k)) *
        polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ *
        OpenMarkedCurrent.entry
          (polygonSignArray (fun i => if i=0 then W 0 else W (k+i))) 0 (N-k)) ∧
      let pre := fun i : Fin (N+1) => moveEndpoint W (W 1-W 0) (-ε) i.val
      ∃ C : PolygonCrossing pre,
        C.val.1.val=0 ∧ C.val.2.val=k ∧ crossingPoint pre C=W 0 ∧
        toLex (polygonEventKey pre (Sum.inr (C,false))) <
          toLex (polygonEventKey pre (Sum.inr (C,true))) ∧
        (scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k))=1 ↔
          crossingOver pre C=C.val.1) ∧
        (scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k))=-1 ↔
          crossingUnder pre C=C.val.1) := by
  obtain ⟨ρ,hρ,hρ1,hjump⟩ := exists_genuine_boundary_polygon_jump hRI W N k hKN s
    hs0 hs1 hcross htrans hisolated hQ
  refine ⟨ρ,hρ,hρ1,?_⟩
  intro ε he her
  obtain ⟨hplus,hminus,hvalue⟩ := hjump ε he her
  refine ⟨hplus,hminus,hvalue,?_⟩
  let v := W 1-W 0
  let pre := fun i : Fin (N+1) => moveEndpoint W v (-ε) i.val
  have hk : 2≤k := by have hsize := hQ.size_ge_three; omega
  have hN : 3≤N+1 := by omega
  have hden : 0<1+ε := by linarith
  let e : Fin (N+1) := ⟨0,by omega⟩
  let f : Fin (N+1) := ⟨k,by omega⟩
  have hsucc0 : (cyclicSuccessor e).val=1 := by
    change (0+1+0)%(N+1)=1
    exact Nat.mod_eq_of_lt (by omega)
  have hsucck : (cyclicSuccessor f).val=k+1 := by
    change (k+1+0)%(N+1)=k+1
    simpa using Nat.mod_eq_of_lt (by omega : k+1<N+1)
  have hpre0 : pre e=W 0+(-ε) • v := by
    simp [pre,e,moveEndpoint]
  have hpre1 : pre (cyclicSuccessor e)=W 1 := by
    change moveEndpoint W v (-ε) (cyclicSuccessor e).val=W 1
    rw [hsucc0]
    simp [moveEndpoint]
  have hpref : pre f=W k := by
    simp [pre,f,moveEndpoint,show k≠0 by omega]
  have hpreK : pre (cyclicSuccessor f)=W (k+1) := by
    change moveEndpoint W v (-ε) (cyclicSuccessor f).val=W (k+1)
    rw [hsucck]
    simp [moveEndpoint,show k+1≠0 by omega]
  have hfirst : edgeInterior pre e (W 0) := by
    refine ⟨ε/(1+ε),div_pos he hden,(div_lt_one hden).mpr (by linarith),?_⟩
    change W 0=affinePoint (pre e) (pre (cyclicSuccessor e)) (ε/(1+ε))
    rw [hpre0,hpre1]
    apply Prod.ext <;> simp [v,affinePoint] <;> field_simp <;> ring
  have hsecond : edgeInterior pre f (W 0) := by
    refine ⟨s,hs0,hs1,?_⟩
    change W 0=affinePoint (pre f) (pre (cyclicSuccessor f)) s
    rw [hpref,hpreK]
    exact hcross
  let C : PolygonCrossing pre := ⟨(e,f),by
    refine ⟨?_,W 0,hfirst,hsecond⟩
    change 0<k
    omega⟩
  have hpre : cyclicNoncollinear pre := finite_noncollinear_of_core _ N hminus
  have hpoint : crossingPoint pre C=W 0 :=
    (crossingPoint_eq_of_mem hN pre hpre C (W 0) hfirst hsecond).symm
  have htfirst : cyclicTangent pre e=(1+ε) • v := by
    unfold cyclicTangent
    rw [hpre1,hpre0]
    apply Prod.ext <;> simp [v] <;> ring
  have htsecond : cyclicTangent pre f=W (k+1)-W k := by
    unfold cyclicTangent
    rw [hpreK,hpref]
  have hdet : planarDet (cyclicTangent pre e) (cyclicTangent pre f)=
      (1+ε)*planarDet (W 1-W 0) (W (k+1)-W k) := by
    rw [htfirst,htsecond]
    simp [planarDet,v]
    ring
  have hsign : scalarSignValue (planarDet (cyclicTangent pre e) (cyclicTangent pre f))=
      scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k)) := by
    rw [hdet]
    exact HorizontalShortEdge.scalarSignValue_positive_mul _ _ hden
  have hclass := HOMFLY.PolygonDrawingBridge.polygonCrossing_firstVisit_overUnder_sign
    pre hN hpre C
  change (_=1 ↔ crossingOver pre C=e) ∧ (_=-1 ↔ crossingUnder pre C=e) at hclass
  rw [hsign] at hclass
  refine ⟨C,rfl,rfl,hpoint,?_,hclass.1,hclass.2⟩
  exact HOMFLY.PolygonDrawingBridge.polygonCrossing_lowerVisit_key_before_upperVisit pre C


end DirectGLSSW
