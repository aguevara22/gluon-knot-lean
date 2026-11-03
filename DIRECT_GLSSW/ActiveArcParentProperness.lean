import ActiveArcParentIntersections
import OpenCarrierChain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))

/-- The actual retained parent triple has a nonzero polynomial numerator witness;
all carrier admissibility follows from its actual nonalternating support. -/
theorem parent_triple_numerator_witness
    (i j k : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    ∃ L : Fin (a+b+1) ⊕ Unit → CarrierLine,
      carrierTripleNumerator
        (L (parentCarrierChain q hR c hcut T i.castSucc)) (L (parentCarrierChain q hR c hcut T i.succ))
        (L (parentCarrierChain q hR c hcut T j.castSucc)) (L (parentCarrierChain q hR c hcut T j.succ))
        (L (parentCarrierChain q hR c hcut T k.castSucc)) (L (parentCarrierChain q hR c hcut T k.succ))≠0 :=
  OpenCarrierChain.triple_numerator_nonzero_witness (parentCarrierChain q hR c hcut T)
    (parentCarrierChain_injective q hR c hcut T) i j k hij hjk hik

/-- Dense carrier-coordinate exclusion for every three distinct actual retained parent labels. -/
theorem parent_triple_numerator_dense
    (i j k : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))
    (hij : i≠j) (hjk : j≠k) (hik : i≠k) :
    Dense {L : Fin (a+b+1) ⊕ Unit → CarrierLine |
      carrierTripleNumerator
        (L (parentCarrierChain q hR c hcut T i.castSucc)) (L (parentCarrierChain q hR c hcut T i.succ))
        (L (parentCarrierChain q hR c hcut T j.castSucc)) (L (parentCarrierChain q hR c hcut T j.succ))
        (L (parentCarrierChain q hR c hcut T k.castSucc)) (L (parentCarrierChain q hR c hcut T k.succ))≠0} :=
  OpenCarrierChain.triple_numerator_nonzero_dense (parentCarrierChain q hR c hcut T)
    (parentCarrierChain_injective q hR c hcut T) i j k hij hjk hik

/-- On the original source-G1 chart the numerator vanishes exactly when the literal
actual retained parent triple is collinear. This is not pointwise nonvanishing. -/
theorem parent_triple_numerator_zero_iff (hG1 : cyclicNoncollinear q)
    (i j k : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    carrierTripleNumerator
      (parentChartLines q (parentCarrierChain q hR c hcut T i.castSucc)) (parentChartLines q (parentCarrierChain q hR c hcut T i.succ))
      (parentChartLines q (parentCarrierChain q hR c hcut T j.castSucc)) (parentChartLines q (parentCarrierChain q hR c hcut T j.succ))
      (parentChartLines q (parentCarrierChain q hR c hcut T k.castSucc)) (parentChartLines q (parentCarrierChain q hR c hcut T k.succ))=0 ↔
    planarDet
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T j-
       Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)
      (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T k-
       Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i)=0 := by
  have hi := parent_vertex_intersection q hR c hcut T hG1 i
  have hj := parent_vertex_intersection q hR c hcut T hG1 j
  have hk := parent_vertex_intersection q hR c hcut T hG1 k
  rw [carrierTripleNumerator_zero_iff _ _ _ _ _ _ hi.1 hj.1 hk.1,hi.2,hj.2,hk.2]

end DirectGLSSW.ActiveArc.OpenCarrier
