import ActiveArcSuffix
import ActiveArcSupportNonalternation
import ActiveArcParentParameters
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.Split
open DirectGLSSW ActiveArc Nonalternation Primitive DirectGLSSW.FiniteCycleOrder
attribute [local instance] Classical.propDecidable

variable {b : ℕ} (q : Fin (1+b+2) → PlanarPoint ℝ)

/-- The suffix crossing correspondence is onto when the removed first edge has
no actual crossing. -/
def firstEdgeFreeCrossingEquiv (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) :
    Crossing (suffix q) ≃ Crossing q := by
  apply Equiv.ofBijective (suffixCrossingToOriginal q)
  constructor
  · exact suffixCrossingToOriginal_injective q
  · intro d
    apply (suffixCrossing_range q d).2
    have hn := hfree d
    have hval : d.val.1.val ≠ 0 := by
      intro hz
      apply hn
      exact Fin.ext hz
    omega

theorem firstEdgeFreeCrossingEquiv_label (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (d : Crossing (suffix q)) :
    (firstEdgeFreeCrossingEquiv q hfree d).val.1.val=d.val.1.val+1 := by
  simp [firstEdgeFreeCrossingEquiv,suffixCrossingToOriginal,edge]
  omega

theorem firstEdgeFreeCrossingEquiv_otherLabel (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (d : Crossing (suffix q)) :
    (firstEdgeFreeCrossingEquiv q hfree d).val.2.val=d.val.2.val+1 := by
  simp [firstEdgeFreeCrossingEquiv,suffixCrossingToOriginal,edge]
  omega

theorem firstEdgeFreeCrossingEquiv_point (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d : Crossing (suffix q)) :
    crossingPoint q (firstEdgeFreeCrossingEquiv q hfree d)=crossingPoint (suffix q) d :=
  suffixCrossingToOriginal_point q hR d

theorem firstEdgeFreeCrossingEquiv_leftParameter (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d : Crossing (suffix q)) :
    leftParameter q (firstEdgeFreeCrossingEquiv q hfree d)=leftParameter (suffix q) d := by
  exact suffixCrossingToOriginal_leftParameter q hR d

theorem firstEdgeFreeCrossingEquiv_rightParameter (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d : Crossing (suffix q)) :
    rightParameter q (firstEdgeFreeCrossingEquiv q hfree d)=rightParameter (suffix q) d := by
  exact suffixCrossingToOriginal_rightParameter q hR d

theorem firstEdgeFreeCrossingEquiv_visitParameter (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d : Crossing (suffix q)) (side : Bool) :
    visitParameter q (firstEdgeFreeCrossingEquiv q hfree d,side)=
      visitParameter (suffix q) (d,side) := by
  cases side
  · simp [visitParameter,firstEdgeFreeCrossingEquiv_leftParameter q hfree hR d]
  · simp [visitParameter,firstEdgeFreeCrossingEquiv_rightParameter q hfree hR d]

theorem firstEdgeFreeCrossingEquiv_visitOrder (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d e : Crossing (suffix q)) (s t : Bool) :
    (eventOrder q hR.noTriple).lt (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,s))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e,t)) ↔
    (eventOrder (suffix q) (regular_suffix q hR).noTriple).lt
      (Sum.inr (d,s)) (Sum.inr (e,t)) := by
  letI : LinearOrder (Event q) := eventOrder q hR.noTriple
  letI : LinearOrder (Event (suffix q)) := eventOrder (suffix q) (regular_suffix q hR).noTriple
  rw [event_lt_iff q hR.noTriple, event_lt_iff (suffix q) (regular_suffix q hR).noTriple]
  have htagd : (visitEdge q (firstEdgeFreeCrossingEquiv q hfree d,s)).val =
      (visitEdge (suffix q) (d,s)).val+1 := by
    cases s <;> simp [visitEdge,firstEdgeFreeCrossingEquiv,suffixCrossingToOriginal,edge] <;> omega
  have htage : (visitEdge q (firstEdgeFreeCrossingEquiv q hfree e,t)).val =
      (visitEdge (suffix q) (e,t)).val+1 := by
    cases t <;> simp [visitEdge,firstEdgeFreeCrossingEquiv,suffixCrossingToOriginal,edge] <;> omega
  have hpd := firstEdgeFreeCrossingEquiv_visitParameter q hfree hR d s
  have hpe := firstEdgeFreeCrossingEquiv_visitParameter q hfree hR e t
  simp only [edgeTag,parameter]
  change (visitEdge q (firstEdgeFreeCrossingEquiv q hfree d,s)).val <
      (visitEdge q (firstEdgeFreeCrossingEquiv q hfree e,t)).val ∨
      (visitEdge q (firstEdgeFreeCrossingEquiv q hfree d,s)).val =
        (visitEdge q (firstEdgeFreeCrossingEquiv q hfree e,t)).val ∧
        visitParameter q (firstEdgeFreeCrossingEquiv q hfree d,s) <
          visitParameter q (firstEdgeFreeCrossingEquiv q hfree e,t) ↔
    (visitEdge (suffix q) (d,s)).val < (visitEdge (suffix q) (e,t)).val ∨
      (visitEdge (suffix q) (d,s)).val=(visitEdge (suffix q) (e,t)).val ∧
        visitParameter (suffix q) (d,s)<visitParameter (suffix q) (e,t)
  rw [htagd,htage,hpd,hpe]
  simp only [Nat.add_lt_add_iff_right, Nat.add_right_cancel_iff]

theorem firstEdgeFreeCrossingEquiv_between (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (d e f : Crossing (suffix q)) (s t u : Bool) :
    between q hR (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,s))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e,t))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree f,u)) ↔
    between (suffix q) (regular_suffix q hR) (Sum.inr (d,s))
      (Sum.inr (e,t)) (Sum.inr (f,u)) := by
  letI : LinearOrder (Event q) := eventOrder q hR.noTriple
  letI : LinearOrder (Event (suffix q)) := eventOrder (suffix q) (regular_suffix q hR).noTriple
  unfold between
  change strictCyclicBetween _ _ _ ↔ strictCyclicBetween _ _ _
  have hde := firstEdgeFreeCrossingEquiv_visitOrder q hfree hR d e s t
  have hef := firstEdgeFreeCrossingEquiv_visitOrder q hfree hR e f t u
  have hfd := firstEdgeFreeCrossingEquiv_visitOrder q hfree hR f d u s
  simp only [strictCyclicBetween,hde,hef,hfd]

theorem firstEdgeFreeCrossingEquiv_nonalternating_map_iff
    (hfree : ∀ d : Crossing q, d.val.1 ≠ 0) (hR : Regular q)
    (S : Finset (Crossing (suffix q))) :
    Nonalternating q hR (Finset.map (firstEdgeFreeCrossingEquiv q hfree).toEmbedding S) ↔
      Nonalternating (suffix q) (regular_suffix q hR) S := by
  constructor
  · intro h d hd e he hde
    have hdm : firstEdgeFreeCrossingEquiv q hfree d ∈
        Finset.map (firstEdgeFreeCrossingEquiv q hfree).toEmbedding S :=
      Finset.mem_map.mpr ⟨d,hd,rfl⟩
    have hem : firstEdgeFreeCrossingEquiv q hfree e ∈
        Finset.map (firstEdgeFreeCrossingEquiv q hfree).toEmbedding S :=
      Finset.mem_map.mpr ⟨e,he,rfl⟩
    have hde' : firstEdgeFreeCrossingEquiv q hfree d ≠ firstEdgeFreeCrossingEquiv q hfree e :=
      fun hh => hde ((firstEdgeFreeCrossingEquiv q hfree).injective hh)
    have hh := h _ hdm _ hem hde'
    have h1 := firstEdgeFreeCrossingEquiv_between q hfree hR d e d false false true
    have h2 := firstEdgeFreeCrossingEquiv_between q hfree hR d e d false true true
    change (between q hR (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,false))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e,false))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,true)) ↔
      between q hR (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,false))
        (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e,true))
        (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d,true))) at hh
    simpa only [h1,h2] using hh
  · intro h d hd e he hde
    rcases Finset.mem_map.mp hd with ⟨d₀,hd₀,rfl⟩
    rcases Finset.mem_map.mp he with ⟨e₀,he₀,rfl⟩
    have hde' : d₀≠e₀ := fun hh => hde (congrArg (firstEdgeFreeCrossingEquiv q hfree) hh)
    have hh := h d₀ hd₀ e₀ he₀ hde'
    have h1 := firstEdgeFreeCrossingEquiv_between q hfree hR d₀ e₀ d₀ false false true
    have h2 := firstEdgeFreeCrossingEquiv_between q hfree hR d₀ e₀ d₀ false true true
    change (between q hR (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d₀,false))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e₀,false))
      (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d₀,true)) ↔
      between q hR (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d₀,false))
        (Sum.inr (firstEdgeFreeCrossingEquiv q hfree e₀,true))
        (Sum.inr (firstEdgeFreeCrossingEquiv q hfree d₀,true)))
    rw [h1,h2]
    exact hh

def firstEdgeFreeSupportEquiv (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) :
    Primitive.Support (suffix q) (regular_suffix q hR) ≃ Primitive.Support q hR :=
  Equiv.subtypeEquiv (Equiv.finsetCongr (firstEdgeFreeCrossingEquiv q hfree)) (by
    intro S
    change Nonalternating (suffix q) (regular_suffix q hR) S ↔
      Nonalternating q hR (Finset.map (firstEdgeFreeCrossingEquiv q hfree).toEmbedding S)
    exact (firstEdgeFreeCrossingEquiv_nonalternating_map_iff q hfree hR S).symm)

theorem firstEdgeFreeSupportEquiv_card (hfree : ∀ d : Crossing q, d.val.1 ≠ 0)
    (hR : Regular q) (S : Primitive.Support (suffix q) (regular_suffix q hR)) :
    (firstEdgeFreeSupportEquiv q hfree hR S).val.card=S.val.card := by
  simp [firstEdgeFreeSupportEquiv,Equiv.subtypeEquiv,Equiv.finsetCongr]

end DirectGLSSW.ActiveArc.Split
