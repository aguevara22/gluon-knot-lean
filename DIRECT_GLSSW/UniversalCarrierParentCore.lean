import UniversalCarrierConsumers
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.RetainedWords ActiveArc.Primitive ActiveArc.OpenCarrier

private theorem universal_chain_sorted {α : Type*} [DecidableEq α] {m : ℕ}
    (L : α → CarrierLine) (hL : UniversalLocus L)
    (f : Fin (m+1) → α) (hf : Function.Injective f)
    (i j k : Fin m) (hij : i.val < j.val) (hjk : j.val < k.val) :
    carrierTripleNumerator (L (f i.castSucc)) (L (f i.succ))
      (L (f j.castSucc)) (L (f j.succ)) (L (f k.castSucc)) (L (f k.succ))≠0 :=
  hL _ _ _ (properPairs_consecutive f hf i j k hij hjk)

/-- Every actual cut-parent open word is already generic at its new root.
The original supplied family retains the incoming carrier at that root. -/
theorem parent_all_support_core_of_supplied {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hcut : c.val.2.val=a)
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
    (hU : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨a+b+1,by omega⟩)=0) :
    ∀ T : Support (parent q c hcut) (regular_parent q hR c hcut),
      ShortEdgeSignStability.CoreHGeneric
        (rootedPolygonWord (OpenVertex _ _ T) (openLast _ _ T.val))
        (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val-1) := by
  intro T
  let P := parent q c hcut
  let hP := regular_parent q hR c hcut
  let f := parentCarrierChain q hR c hcut T
  have hd (v : Fin (openCount P hP T.val)) : lineDenominator (L (f v.castSucc)) (L (f v.succ))≠0 := by
    apply hT
    intro he
    have hh := congrArg Fin.val (parentCarrierChain_injective q hR c hcut T he)
    simp only [Fin.coe_castSucc,Fin.val_succ] at hh
    omega
  have hx (v : Fin (openCount P hP T.val)) :=
    parent_vertex_supplied_line_intersection q hR c hcut T L hinc hterminal v (hd v)
  intro i j k hij hjk hkN hz
  change k ≤ openCount P hP T.val - 1 at hkN
  have hiN : i < openCount P hP T.val := by omega
  have hjN : j < openCount P hP T.val := by omega
  have hkN' : k < openCount P hP T.val := by omega
  let I : Fin (openCount P hP T.val) := ⟨i,hiN⟩
  let J : Fin (openCount P hP T.val) := ⟨j,hjN⟩
  let K : Fin (openCount P hP T.val) := ⟨k,hkN'⟩
  have hn := universal_chain_sorted L hU f (parentCarrierChain_injective q hR c hcut T)
    I J K hij hjk
  apply hn
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hd I) (hd J) (hd K)).2
  rw [hx I,hx J,hx K]
  have hwi := openCurrent_word P hP T i hiN
  have hwj := openCurrent_word P hP T j hjN
  have hwk := openCurrent_word P hP T k hkN'
  have he : planarDet (OpenVertex P hP T J-OpenVertex P hP T I)
      (OpenVertex P hP T K-OpenVertex P hP T I)=
      -polygonHDet (rootedPolygonWord (OpenVertex P hP T) (openLast P hP T.val)) i j k := by
    unfold polygonHDet
    rw [hwi,hwj,hwk]
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  exact he.trans (by rw [hz,neg_zero])
end DirectGLSSW.UniversalCarrierDomain

