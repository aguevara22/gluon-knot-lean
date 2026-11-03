import UniversalCarrierConsumers
import PhysicalCornerSuppliedLines
set_option autoImplicit false
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart ActiveArc ActiveArc.Cursor ActiveArc.Split
open ActiveArc.RetainedWords ActiveArc.Primitive ActiveArc.OpenCarrier

/-- Every actual positive-drop suffix retained word is generic on the SAME
universal supplied family, with no crossing-count/nonempty-crossing assumption. -/
theorem corner_word_core_of_supplied {N M d : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (h : N=d+M) (hd : 0 < d) (hQ : Regular q)
    (L : Fin (N+1) ⊕ Unit → CarrierLine)
    (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (N+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨N+1,by omega⟩)=0) :
    ∀ U : Support (dropWord q h) (dropWord_regular q h hQ),
      ShortEdgeSignStability.CoreHGeneric
        (rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val))
        (openCount (dropWord q h) (dropWord_regular q h hQ) U.val-1) := by
  intro U
  let p := cornerCarrierPair q h hQ U
  obtain ⟨hcard,hinj,hcommon⟩ := cornerCarrierPair_data q h hd hQ U
  have hne (v) : (p v).1≠(p v).2 := by
    intro he
    have hh := hcard v
    change ({(p v).1,(p v).2} : Finset (Fin (N+1) ⊕ Unit)).card=2 at hh
    simp only [he,Finset.pair_eq_singleton,Finset.card_singleton] at hh
    omega
  have hden (v) : lineDenominator (L (p v).1) (L (p v).2)≠0 := hT _ _ (hne v)
  have hx (v) := corner_pair_supplied_intersection q h hd hQ U L hinc hterminal v (hden v)
  intro i j k hij hjk hkN hz
  have hiN : i < openCount (dropWord q h) (dropWord_regular q h hQ) U.val := by omega
  have hjN : j < openCount (dropWord q h) (dropWord_regular q h hQ) U.val := by omega
  have hkN' : k < openCount (dropWord q h) (dropWord_regular q h hQ) U.val := by omega
  let I : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val) := ⟨i,hiN⟩
  let J : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val) := ⟨j,hjN⟩
  let K : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val) := ⟨k,hkN'⟩
  have hp : ProperPairs (p I) (p J) (p K) :=
    ⟨hne I,hne J,hne K,
      fun he => (ne_of_lt hij) (congrArg Fin.val (hinj he)),
      fun he => (ne_of_lt hjk) (congrArg Fin.val (hinj he)),
      fun he => (ne_of_lt (lt_trans hij hjk)) (congrArg Fin.val (hinj he)),
      hcommon I J K hij hjk⟩
  apply hL (p I) (p J) (p K) hp
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hden I) (hden J) (hden K)).2
  rw [hx I,hx J,hx K]
  have hwi := openCurrent_word (dropWord q h) (dropWord_regular q h hQ) U i hiN
  have hwj := openCurrent_word (dropWord q h) (dropWord_regular q h hQ) U j hjN
  have hwk := openCurrent_word (dropWord q h) (dropWord_regular q h hQ) U k hkN'
  have he : planarDet (OpenVertex _ _ U J-OpenVertex _ _ U I)
      (OpenVertex _ _ U K-OpenVertex _ _ U I)=
      -polygonHDet (rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val)) i j k := by
    unfold polygonHDet
    rw [hwi,hwj,hwk]
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  exact he.trans (by rw [hz,neg_zero])

/-- Exact short-first-edge projector far-sign interface, produced from the
same supplied original family. The arbitrary prefix is unused by indices 1,k,j. -/
theorem corner_far_of_supplied {N M d : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (h : N=d+M) (hd : 0 < d) (hQ : Regular q)
    (L : Fin (N+1) ⊕ Unit → CarrierLine)
    (hL : UniversalLocus L) (hT : PairTransverse L)
    (hinc : ∀ e : Fin (N+1), lineValue (L (Sum.inl e)) (q e.castSucc)=0 ∧
      lineValue (L (Sum.inl e)) (q e.succ)=0)
    (hterminal : lineValue (L (Sum.inr ())) (q ⟨N+1,by omega⟩)=0) :
    ∀ U : Support (dropWord q h) (dropWord_regular q h hQ),
      ∀ (x : PlanarPoint ℝ) (k j : ℕ), 1 < k → k < j →
        j≤openCount (dropWord q h) (dropWord_regular q h hQ) U.val →
        polygonHDet (fun i => if i=0 then x else
          rootedPolygonWord (OpenVertex _ _ U) (openLast _ _ U.val) (i-1)) 1 k j≠0 := by
  intro U x k j hk hkj hjN
  have hh := corner_word_core_of_supplied q h hd hQ L hL hT hinc hterminal U
    0 (k-1) (j-1) (by omega) (by omega) (by omega)
  simpa only [polygonHDet,if_neg (by omega : (1:ℕ)≠0),if_neg (by omega : k≠0),
    if_neg (by omega : j≠0),Nat.sub_self] using hh
end DirectGLSSW.UniversalCarrierDomain


