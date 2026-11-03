import ExposedCursorFilter
import ResizedPhysicalSuffix
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ExposedChart
attribute [local instance] Classical.propDecidable
open ExposedOpenPrimitive
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hq : CyclicGeneric q) (he : LeftExposed q 0)
include hq he

/-- Actual original event avoidance implies absence of the corresponding
critical parameter in the original opening; no Regular conclusion is assumed. -/
theorem original_event_avoidance_cut_parameter (e : Fin (n+2)) (a : ℕ) (hea : e.val=a+1)
    (θ : ℝ) (hno : ∀z : PolygonEvent q, polygonEventEdge q z=e → polygonEventParameter q z≠θ) :
    ∀d : Crossing (cutArc q 0), d.val.1.val=a → leftParameter (cutArc q 0) d≠θ := by
  intro d hd
  let z : PolygonEvent q := Sum.inr (visitEquiv q 0 hq he (d,false))
  have hz : polygonEventEdge q z=e := by
    change crossingVisitEdge q (visitEquiv q 0 hq he (d,false))=e
    rw [visitEquiv_edge]
    apply Fin.ext
    rw [zero_edgeLabel_val,hea]
    change d.val.1.val+1=a+1
    omega
  have hp : polygonEventParameter q z=leftParameter (cutArc q 0) d :=
    visitEquiv_parameter q 0 hq he (d,false)
  exact hp ▸ hno z hz

theorem exposed_suffix_regular (a b : ℕ) (hs : a+b=n) (e : Fin (n+2)) (hea : e.val=a+1)
    (θ : ℝ) (h0 : 0≤θ) (h1 : θ<1)
    (hno : ∀z : PolygonEvent q, polygonEventEdge q z=e → polygonEventParameter q z≠θ) :
    Regular (Cursor.moveStart (Split.suffixWord (cutArc q 0) a b hs) θ) :=
  Split.suffixWord_moveStart_regular (cutArc q 0) (cutArc_regular q 0 hq) a b hs θ h0 h1
    (original_event_avoidance_cut_parameter q hq he e a hea θ hno)

end DirectGLSSW.ActiveArc.ExposedChart
