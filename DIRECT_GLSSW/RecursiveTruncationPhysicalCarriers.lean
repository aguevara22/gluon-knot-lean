import RecursivePhysicalCarrierTransport

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.ExposedChart TruncationDirection ShortEdgeCyclicAdapter

/-- Cutting at the newly inserted edge leaves precisely the old physical
carriers. This is pure geometry: no genericity, size or smallness premise. -/
theorem truncated_cut_physical_carriers {n : ℕ}
    (q : Fin (n+1) → PlanarPoint ℝ) (a p : Fin (n+1))
    (hp : cyclicSuccessor p=a) (scale ε : ℝ) :
    Function.Injective (fun i : Fin (n+1) => collapseFin a (edgeLabel a.castSucc i)) ∧
      ∀ i : Fin (n+1),
        lineValue (polygonCarrierCoordinates q (collapseFin a (edgeLabel a.castSucc i)))
          (cutArc (truncateCyclicCorner q a p scale ε) a.castSucc i.castSucc)=0 ∧
        lineValue (polygonCarrierCoordinates q (collapseFin a (edgeLabel a.castSucc i)))
          (cutArc (truncateCyclicCorner q a p scale ε) a.castSucc i.succ)=0 := by
  constructor
  · intro i j he
    apply edgeLabel_injective a.castSucc
    apply truncatedCarrierLabel_injective a
    simp only [truncatedCarrierLabel,if_neg (edgeLabel_ne_deleted a.castSucc i),
      if_neg (edgeLabel_ne_deleted a.castSucc j)]
    exact congrArg Fin.castSucc he
  · intro i
    change lineValue (polygonCarrierCoordinates q (collapseFin a (edgeLabel a.castSucc i)))
      (truncateCyclicCorner q a p scale ε (cyclicVertexEquiv a.castSucc i.castSucc))=0 ∧
      lineValue (polygonCarrierCoordinates q (collapseFin a (edgeLabel a.castSucc i)))
      (truncateCyclicCorner q a p scale ε (cyclicVertexEquiv a.castSucc i.succ))=0
    rw [edgeLabel_successor]
    exact truncated_old_carrier_incidence q a p hp scale ε _ (edgeLabel_ne_deleted a.castSucc i)

end DirectGLSSW.CyclicCarrierClearing

