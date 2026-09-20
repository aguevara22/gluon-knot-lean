

/-! # R176W2 — the assembler's section (`r176a_`, 2026-09-15): the mirrored (14)-bridge

The OUTER unit found the frozen Prop `r176_outer_carriers_L` false at `y = lift v'` (R176W2_OUTER_REPORT §2) and
replaced it by the proved split `r176o_outer_carriers_L_corrected`, whose `v'`-half carries the mirrored data
`r176o_OuterDataL'` (children exchanged: `K_A = liftBlock (retained Λ₁)`, `K_B = liftBlock (retained Λ₂) ∪ {lift u'}`).
Its replayed composition `r176o_extreme_transport_of_curl_mixed` therefore needs, besides `r176s_curl_removal`
(CURL: `r176c_curl_removal_proof`) and `r176_mixed_bridge` (MIXED: `r176m_mixed_bridge_proof`), the mirrored bridge
`r176o_mixed_bridge'`.  MIXED's count `r176m_bridge_count` is symmetric in the two children (`W₁`, `W₂` are only
counted), so the mirrored bridge is MIXED's event-level proof with `W₁ := retained Λ₂`, `W₂ := retained Λ₁`
(`hW₁ := O.subA`, `hW₂ := O.subB`) — the two `card` summands of `hcount` exchange places and `linarith` closes as before.
Nothing above is modified; the only new name is `r176a_mixed_bridge'_proof`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

section R176A_Assembly

/-- **The mirrored (14)-bridge** `r176o_mixed_bridge'` (the Prop left open by the OUTER unit): `r176m_mixed_bridge_proof`
with the roles of `Λ₁`/`Λ₂` exchanged in the call of `r176m_bridge_count` (`W₁ := retained Λ₂` via `O.subA`,
`W₂ := retained Λ₁` via `O.subB`, against `O.KA_eq : K_A = liftBlock (retained Λ₁)`,
`O.KB_eq : K_B = liftBlock (retained Λ₂) ∪ {r}`, `O.r_not`). -/
theorem r176a_mixed_bridge'_proof : r176o_mixed_bridge' := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q a b c
    hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf y hy O
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side (as in `r176l_portDataRest_case1`)
  have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
  have hop' : OppositeSides E t' t := by
    unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
  have hXL : ExactTriangleVisitOrders (E.curve t') (E.curve t) a b c hs' :=
    gu2_exact_of_eq hs' habc.symm (hL.gauss_words t' t ht' ht hop' hs')
  have hGL : CarrierGeometry (E.curve t') :=
    CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ hS'
  have hjT : crossingTransport hs j ∈ transportSupport hs (Q ∪ {j}) :=
    (mem_transportSupport_iff hs _ j).mpr (Finset.mem_union_right _ (Finset.mem_singleton_self j))
  -- the successor facts of case 1
  have hρa : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (r176l_ua (u := crossingTransport hs u) huac)) =
      Sum.inr (visitOn (crossingTransport hs j) a (s176_mem_left hjab)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_a
      (fun w hw => (s176_nb_a hs' hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u)
        hjab huac w hw).1)
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSfI : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    CV.geoIndependent_of_mem_Ind _ hSf
  -- the children and the `L`-side count
  obtain ⟨hlt_c, hρc⟩ := r176l_lt_c_of_indep hn (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hSfI hnb_c
  have hC := r176l_children_case1 (geomAt E t' ht'.1) hT
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc
    hjT hu' hv' hρa hρb hρc hSfI
  have hcard := r176l_card_retained (geomAt E t' ht'.1) (r176l_subset_Sf _ _ _) hC
  have hsel := r176l_selectedPart_card (geomAt E t' ht'.1)
    (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hbc
    (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc hu' hv'
  -- the count on the lift
  have hcount : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) hS'
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y)
      (r176s_DA_i _ y O.v₀ O.hv₀) (r176s_DA_j _ y O.v₀ O.hv₀) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) + 2 =
      ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) :=
    r176m_bridge_count hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ hS')
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y O.v₀ O.hv₀ _ _ O.subA O.subB
      O.r O.KA_eq O.KB_eq O.r_not
  have hcard' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs u) (v := crossingTransport hs v) hvbc)).card : ℤ) +
      ((geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) +
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
        (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
          (v := crossingTransport hs v) hvbc)
        (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
          (u := crossingTransport hs u) huac)).card : ℤ) + 2 := by
    rw [hsel] at hcard
    have h := (Nat.cast_inj (R := ℤ)).mpr hcard
    push_cast at h
    exact h
  linarith

/-- **Row 176 in the row shape `RowShape @ExtremeTransportData`** (RALedgers' fixed shape of an X₁-dependent R row),
unconditional: `r176o_extreme_transport_of_curl_mixed` (OUTER's replay of `r176_extreme_transport_of_curl_outer_mixed`
on the corrected outer carriers) with its three hypotheses discharged — `r176s_curl_removal` by CURL's
`r176c_curl_removal_proof`, `r176o_mixed_bridge'` by `r176a_mixed_bridge'_proof`, `r176_mixed_bridge` by MIXED's
`r176m_mixed_bridge_proof`.  The row theorem `RProof.extreme_transport` (FIXED name, the siblings' binder form) is
this statement instantiated. -/
theorem r176a_extreme_transport_rowShape : RowShape @ExtremeTransportData :=
  r176o_extreme_transport_of_curl_mixed r176c_curl_removal_proof r176a_mixed_bridge'_proof
    r176m_mixed_bridge_proof

end R176A_Assembly

end

end RProof
