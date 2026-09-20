

/-! # R176_Assembled — the assembler's composition section (2026-09-15)

Everything above this line is `Site_176.lean` (frozen, 4143 lines) followed by the three unit appendices
`R176_HSUCC` (`r176h_`, §I–§K), `R176_SMOOTH` (`r176s_`, §R1–§R5) and `R176_LEDGER` (`r176l_`, §L0–§L5),
byte-identical to the unit files.  This section (all names `r176_`) connects them; companion report
`R176_ASSEMBLY_REPORT.md`.

* §X1 the open geometric Prop of row 176 in the LEDGER's coordinates: `r176_OuterDataL` = SMOOTH's
  `r176s_OuterData` with the two outer carriers FIXED to the LEDGER's children `Λ₁ = owner_{Sf} (v', c)`
  (`r176l_L1`, the kinked `B`-component) and `Λ₂ = owner_{Sf} (u', a)` (`r176l_L2`, the clean `A`-component)
  at `Sf = r176l_Sf S' u' v'`; the black box `r176_outer_carriers_L` carries the FULL event binders
  (`hcomp`, `habc`, `hu hv hju hjv huv`, `hSf`, `hlt_a`) a geometric prover needs.
* §X2 the (14)-bridge `r176_mixed_bridge` (`2ℓ` = the number of mask-`uv` survivors) — the one clause of the
  LEDGER's `r176l_SmoothData` that neither unit proves.
* §X3 the connector `r176_smoothData_of`: the LEDGER's `r176l_SmoothData` from SMOOTH's constructions
  (`r176s_DA`, `r176s_DA_smooth`, `r176s_DA_componentCount`, `r176s_DA_i/j/ij`, `r176s_knotRestrictIso_i/j`,
  `r176s_homfly_of_liftBlock`, `r176s_homfly_of_liftBlock_curl`) from `r176_OuterDataL`, the curl black box
  `r176s_curl_removal` and the mixed bridge.
* §X4 the LEDGER's event-level chain replayed against the connector (`r176_portDataRest_case1`, `_labelled`,
  `_of_uniform`: bodies byte-identical except the `hsmooth` call) and the weak interface under `wind(S) ≠ 0`
  with HSUCC's port (`r176_est_port_relation_weak_uniform_of_curl_outer_mixed`).
* §X5 the consumer split on `wind(S) = 0` (both row terms vanish — `rowTerm_of_mem_Ind`, `GT_wind_eq`), so the
  corrected interface `r176l_est_port_relation_weak_uniform` suffices for the RA ledger
  (`r176_est_row_H_weak_uniform` … `r176_est_ledger_weak_uniform`): the "RALedgers change" of
  R176_LEDGER_REPORT §3, made here on the draft copies.
* §X6 the row: `r176_extreme_transport_of_curl_outer_mixed : RowShape @ExtremeTransportData` from exactly the
  three open Props and the library's `CV.carrierSlotFloor`; the `hrest`-only forms with `hF` discharged; and the
  SMOOTH-route composition `r176_extreme_transport_of_curl_outer_ledger` (from `r176s_outer_carriers` and
  `r176s_ledger`). -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section R176Compose

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-! ## §X1. The outer carriers of `S_full` in the LEDGER's coordinates -/

/-- **The outer-carrier data of row 176 with the LEDGER's children** — SMOOTH's `r176s_OuterData` (§R5) with
`Λ_B := r176l_L1 = owner_{Sf} (v', c)` (the kinked `B`-component, `Λ₁` of `s176_PortDataRest`) and
`Λ_A := r176l_L2 = owner_{Sf} (u', a)` (the clean `A`-component, `Λ₂`) at the full support `Sf = r176l_Sf S' u' v'`
(the LEDGER's classical-`insert` form): an occurrence `v₀` of `y`, the kink `r`, the retained sets of the two
children inside that of `q₀'`, and the identification of the two arc crossing sets of `ρ = D₊.record` at `v₀`
with the chords of the children (`KA_eq`, `KB_eq`, `r_not`, `r_curl`).  The remaining GEOMETRIC obligation of
row 176 (R176_SMOOTH_REPORT §2.2). -/
structure r176_OuterDataL (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing) where
  /-- the occurrence of `y` from which the arc `A` carries the clean component -/
  v₀ : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Visit
  hv₀ : v₀.1 = y
  /-- the retained set of the clean child `Λ₂ = owner_{Sf} (u', a)` lies in that of `q₀'` -/
  subA : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the retained set of the kinked child `Λ₁ = owner_{Sf} (v', c)` lies in that of `q₀'` -/
  subB : geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) ⊆
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
  /-- the crossings on the arc `A = (v₀ → τ v₀)` are the chords of `Λ₂` -/
  KA_eq : r176s_KA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac))
  /-- the kink (the lift of the third triangle crossing) -/
  r : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.Crossing
  /-- the crossings on the arc `B = (τ v₀ → v₀)` are the chords of `Λ₁` plus the kink -/
  KB_eq : r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀ =
    CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc)) ∪ {r}
  r_not : r ∉ CV.liftBlock hn (r176s_cgL hn ht') (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) (geoCarrierCrossings (geomAt E t' ht'.1) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc))
  /-- the kink's two occurrences are consecutive in `ρ|B` -/
  r_curl : ∃ (w : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.M) (hw : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.CrossKeep (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀) w),
    (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf w = r ∧
    (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings (r176s_KB (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record v₀)).succ ⟨w, hw⟩).1 = (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.pair w

/-- **The outer carriers exist, LEDGER's coordinates — BLACK BOX (OPEN; the remaining geometric obligation
of row 176)**: for every labelled case-1 configuration of the affected carrier `q₀'` on `L` (the binders of
`r176l_portDataRest_case1`: `K3` side `t`, empty side `t'`, labels `a b c` with `{a, b, c} = {e, f, g}`, the
selected corner `j' = {a, b}`, the two retained local crossings `u' = {a, c}`, `v' = {b, c}`, the orientation
`u' <_a j'`, `S_full` independent) and the lift `y` of either local crossing, `r176_OuterDataL` is nonempty.
Geometric content: R176_SMOOTH_REPORT §2.2 (the `geoSmoothingSuccessor` of `S_full` on the visits of `q₀'`,
`s176_corner_case1`, the forced order `v' <_c u'` = `r176l_lt_c_of_indep`, `r176s_arcA_iff_key` /
`r176s_crossKeep_KA_iff_key` to read the arcs on the parent).  Estimate ≈ 1.5–2.5k lines. -/
def r176_outer_carriers_L : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv'),
    Nonempty (r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)

/-! ## §X2. The (14)-bridge: `2ℓ` is the number of mask-`uv` survivors -/

/-- **The mixed crossings of `D_A` are the mask-`uv` survivors — BLACK BOX (OPEN)**: for the outer-carrier data
`O`, the mixed sign sum of the two components `i` (the `B`-class of `v₀`) and `j` (the `A`-class of `τ v₀`) of
`D_A = r176s_DA D₊ y` is the number of retained crossings of `q₀'` unselected in `S_full` with one visit on each
child (`r176l_mixedSet`).  Route: `r176l_mixedSignSum_eq_card` (every crossing of the positive lift is `+1`,
`geoPositiveLift_sign`; the smoothing keeps the other crossings and creates none) reduces it to a bijection of
the mixed crossings of `D_A` with `r176l_mixedSet`, through `r176s_smooth_comp_eq_pair_iff` /
`r176s_smooth_comp_eq_self_iff` (a crossing is mixed iff its two occurrences lie on different arcs) and the
parent-key reading `r176s_arcA_iff_key`.  Estimate ≈ 400–700 lines. -/
def r176_mixed_bridge : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c)
    (_habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) (u v : Crossing (E.curve t))
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (_hu : u.val ∈ triangleSupports e f g) (_hv : v.val ∈ triangleSupports e f g)
    (_hju : j ≠ u) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (_hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv')
    (O : r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y),
    mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)

/-! ## §X3. The connector: the LEDGER's `r176l_SmoothData` from SMOOTH's constructions -/

/-- **The LEDGER's smoothing data from SMOOTH's constructions**: `D_A = r176s_DA D₊ y` (the library smoothing),
`IsOrientedSmoothing` (`r176s_DA_smooth`), two components (`r176s_DA_componentCount`), the tags `i` (`B`-class of
`v₀`) and `j` (`A`-class of `τ v₀`) with `i ≠ j`, the exact owner map (9)/(9a) — `poly₁` for the kinked child
`Λ₁ = r176l_L1` through the record-level R-I black box and `r176s_knotRestrictIso_i`, `poly₂` for the clean child
`Λ₂ = r176l_L2` through `r176s_knotRestrictIso_j` and `CV.liftRestrictRecordIso` — and the (14)-bridge as a
hypothesis. -/
def r176_smoothData_of (hcurl : r176s_curl_removal) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {a b c : ZMod n} {u v : Crossing (E.curve t)} (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (O : r176_OuterDataL hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y)
    (hSf : (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) ∈ CV.Ind (geomAt E t' ht'.1))
    (hmixed : mixedSignSum (r176s_DA (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y) (r176s_DA_i (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) (r176s_DA_j (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) y O.v₀ O.hv₀) =
      ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac)).card : ℤ)) :
    r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) := by
  have hD1 : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).componentCount = 1 := geoPositiveLift_componentCount hn _ _ _
  refine
    { DA := r176s_DA _ y, smooth := r176s_DA_smooth _ y, two := r176s_DA_componentCount _ y hD1,
      i := r176s_DA_i _ y O.v₀ O.hv₀, j := r176s_DA_j _ y O.v₀ O.hv₀, ij := r176s_DA_ij _ y hD1 O.v₀ O.hv₀,
      poly₁ := ?_, poly₂ := ?_, mixed := hmixed }
  · -- (9a) the kinked child `Λ₁`: the record-level R-I removes the kink
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock_curl hcurl hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u)
        (v := crossingTransport hs v) hvbc) O.subB _ _ O.r O.KB_eq O.r_not O.r_curl
      ⟨r176s_knotRestrictIso_i _ _ hD1 O.v₀ O.hv₀⟩
  · -- (9) the clean child `Λ₂`
    rw [GT_groupedPoly_eq_homfly]
    exact r176s_homfly_of_liftBlock hn (r176s_cgL hn ht')
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (CV.geoIndependent_of_mem_Ind _ hSf) _ (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v)
        (u := crossingTransport hs u) huac) O.subA _ _ O.KA_eq
      ⟨r176s_knotRestrictIso_j _ _ hD1 O.v₀ O.hv₀⟩

/-! ## §X4. The LEDGER's event-level chain against the connector -/

/-- `r176l_portDataRest_case1` with the SMOOTH black box replaced by the connector `r176_smoothData_of` on the
open Props `r176_outer_carriers_L`, `r176s_curl_removal`, `r176_mixed_bridge` (body otherwise byte-identical). -/
theorem r176_portDataRest_case1 (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g}) {u v : Crossing (E.curve t)}
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu : u.val ∈ triangleSupports e f g) (hv : v.val ∈ triangleSupports e f g)
    (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left hjab)))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y) := by
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- the `L` side
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
  have hlt_b := (s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc hXL (j := crossingTransport hs j)
    (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT hu' hv').mp hlt_a
  have hρb : geoMarkSuccessor (geomAt E t' ht'.1) (Sum.inr (visitOn (crossingTransport hs j) b (s176_mem_right hjab))) =
      Sum.inr (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
    gu1_markSuccessor_eq_of_adjacent hn _ rfl hlt_b
      (fun w hw => (s176_nb_b hs' hab hac hbc hXL (j := crossingTransport hs j) (v := crossingTransport hs v)
        hjab hvbc w hw).1)
  have hnb_c := fun (w : Visit (E.curve t')) (hw : w.2.val = c) =>
    s176_nb_c hs' hab hac hbc hXL (u := crossingTransport hs u) (v := crossingTransport hs v) huac hvbc w hw
  -- the full support
  have hSf : GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) :=
    r176l_Sf_indep_event hL ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv
  have hSf' : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1) := (CV.mem_Ind_iff _ _).mpr hSf
  -- uniformity, carried
  obtain ⟨σ, hσ, huniH⟩ := (CV.wind_ne_zero_imp (geomAt E t ht.1) (Q ∪ {j}) hwind).2 q
  have huni := r176l_uniform_transport hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huniH
  -- regularity
  have hreg : ∀ (S : Finset (Crossing (E.curve t'))) (r : GeoComponent (geomAt E t' ht'.1) S),
      GeoIndependent (geomAt E t' ht'.1) S → CV.Regular (geoCornerPolygon (geomAt E t' ht'.1) S r) :=
    fun S r hind => CV.carrierPolygon_cvRegular hn (genericAt E t' ht'.1) ((CV.mem_Ind_iff _ _).mpr hind) r
  -- the ledger
  have LD := r176l_ledgerData_case1 hn (geomAt E t' ht'.1) hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hab hac hbc
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v) hjab huac hvbc hjT
    hu' hv' hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg
  -- the smoothing data: SMOOTH's constructions on the outer carriers, the curl removal, the mixed bridge
  obtain ⟨O⟩ := hout n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
    a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy
  have D := r176_smoothData_of hcurl hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q huac hvbc y O hSf'
    (hmixed n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
      a b c hab hac hbc habc u v hjab huac hvbc hu hv hju hjv huv hu' hv' hlt_a hSf' y hy O)
  -- (14): the writhe shift (7) and the `L`-side count
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have h7 := est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hcu hcv
    q howner_u
  have hcard := LD.card
  have hw : CV.groupedWrithe (genericAt E t ht.1) q =
      CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc) +
        CV.groupedWrithe (genericAt E t' ht'.1)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac) +
        ((r176l_mixedSet (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j}))
          (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
          (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
          (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac)).card : ℤ) := by
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hS'] at h7
    rw [CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf', CV.groupedWrithe_eq_card_geoCarrierCrossings _ hSf']
    have hc' : ((geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).card : ℤ) =
        _ := congrArg (fun m : ℕ => (m : ℤ)) hcard
    push_cast at hc'
    linarith
  -- (13)
  have hrot := r176l_rot_ledger hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    (hSf := hSf') hσ (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) hS hS' q) LD.rot_add
    LD.shape₁ LD.shape₂
  -- (12)
  have halt := r176l_alt_of_shape hn (genericAt E t' ht'.1) (hSf := hSf') hσ LD.shape₁ LD.shape₂
  exact ⟨r176l_portDataRest_of hn (genericAt E t ht.1) (genericAt E t' ht'.1) hS hS' q (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y D hw
    hrot halt.1 halt.2⟩

/-- `r176l_portDataRest_labelled` against `r176_portDataRest_case1` (body byte-identical). -/
theorem r176_portDataRest_labelled (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  obtain ⟨hv', -, -⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    hab hac hbc habc hjab huac hvbc hv hjv huv
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
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
  have hju' : crossingTransport hs u ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hju.symm
  have hjv' : crossingTransport hs v ≠ crossingTransport hs j := (crossingTransport hs).injective.ne hjv.symm
  have hcyc := s176_cyclic hn hGL hs' hT (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
    hab hac hbc hXL (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv'
  rcases lt_or_gt_of_ne (r176l_param_ne (geomAt E t' ht'.1) hju' (s176_mem_left huac) (s176_mem_left hjab)) with
    hlt | hgt
  · exact r176_portDataRest_case1 hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hab hac hbc
      habc hjab huac hvbc hu hv hju hjv huv hu' hv' hlt _ (Or.inl rfl)
  · -- case 2: relabel `(b, a, c), (j, v, u)`
    have hnlt : ¬ visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) <
        visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
      fun h => lt_asymm hgt (hcyc.mpr h)
    have hlt_b : visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) <
        visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) :=
      lt_of_le_of_ne (not_lt.mp hnlt) (r176l_param_ne (geomAt E t' ht'.1) hjv' (s176_mem_left hvbc) (s176_mem_right hjab))
    have habc' : ({b, a, c} : Finset (ZMod n)) = {e, f, g} := (Finset.insert_comm b a {c}).trans habc
    exact r176_portDataRest_case1 hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind
      (a := b) (b := a) (c := c) hab.symm hbc hac habc' (u := v) (v := u) (s176_pair_comm' hjab) hvbc huac hv hu hjv hju
      huv.symm hv' hu' hlt_b _ (Or.inr rfl)

/-- **The `hrest` obligation of row 176 under `wind(S) ≠ 0` from the open Props** — `r176l_portDataRest_of_uniform`
against `r176_portDataRest_labelled` (body byte-identical). -/
theorem r176_portDataRest_of_uniform (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0)
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) := by
  have h1 : (xPair hef').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inl rfl)
  have h2 : (xPair heg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl))
  have h3 : (xPair hfg').val ∈ triangleSupports e f g := (P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl))
  have n12 := P1.xPair_ef_ne_eg hef' heg' hfg'
  have n13 := P1.xPair_ef_ne_fg hef' heg' hfg'
  have n23 := P1.xPair_eg_ne_fg hef' heg' hfg'
  have key : ∀ {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
      (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
      (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
      (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')) :=
    fun {a b c} hab hac hbc habc hjab huac {v} hvbc hv hjv huv =>
      r176_portDataRest_labelled hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hu hju hu'
        hab hac hbc habc hjab huac (v := v) hvbc hv hjv huv
  have p_feg : ({f, e, g} : Finset (ZMod n)) = {e, f, g} := Finset.insert_comm f e {g}
  have p_egf : ({e, g, f} : Finset (ZMod n)) = {e, f, g} := congrArg (insert e) (Finset.pair_comm g f)
  have p_gef : ({g, e, f} : Finset (ZMod n)) = {e, f, g} :=
    (Finset.insert_comm g e {f}).trans (congrArg (insert e) (Finset.pair_comm g f))
  have p_fge : ({f, g, e} : Finset (ZMod n)) = {e, f, g} :=
    (congrArg (insert f) (Finset.pair_comm g e)).trans (Finset.insert_comm f e {g})
  have p_gfe : ({g, f, e} : Finset (ZMod n)) = {e, f, g} :=
    ((congrArg (insert g) (Finset.pair_comm f e)).trans (Finset.insert_comm g e {f})).trans
      (congrArg (insert e) (Finset.pair_comm g f))
  rcases GT_tri_cases t hef' heg' hfg' j hj with rfl | rfl | rfl <;>
    rcases GT_tri_cases t hef' heg' hfg' u hu with rfl | rfl | rfl
  · exact absurd rfl hju
  · exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl (v := xPair heg') rfl h2 n12 n23.symm
  · exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg') (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g) (Finset.pair_comm f g) (v := xPair hef') rfl h1
      n12.symm n13.symm
  · exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f) (v := xPair heg') (Finset.pair_comm e g) h2
      n23.symm n12
  · exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g) (Finset.pair_comm e g) (v := xPair hef')
      (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju


/-- **The weak interface of row 176 under `wind(S) ≠ 0` from exactly the open Props**: the record-level R-I
`r176s_curl_removal`, the outer carriers `r176_outer_carriers_L`, the (14)-bridge `r176_mixed_bridge`; the port
is HSUCC's `r176h_est_port_weak` (`hrec` CLOSED), the non-move data the LEDGER's chain through the connector. -/
theorem r176_est_port_relation_weak_uniform_of_curl_outer_mixed (hcurl : r176s_curl_removal)
    (hout : r176_outer_carriers_L) (hmixed : r176_mixed_bridge) : r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176_portDataRest_of_uniform hcurl hout hmixed hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg'
    hcomp hQ hfull hj q hwind hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- **The weak interface under `wind(S) ≠ 0` from the non-move port data alone, in the CORRECTED `hrest` form**
(the binders carry `hcomp`, `hu`, `hju` — R176_SMOOTH_REPORT §4 — and `wind(S) ≠ 0` — R176_LEDGER_REPORT §3). -/
theorem r176_est_port_relation_weak_uniform_of_rest
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
      CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
      ∀ (u : Crossing (E.curve t)) (_hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
        (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q
    hwind u hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-! ## §X5. The consumer split on `wind(S) = 0`: the corrected interface suffices for the RA ledger -/

/-- `s176_est_row_H_weak` (= `est_row_H`, RALedgers.lean:1514) with the interface under `wind(S) ≠ 0`: when
`wind(S) = 0` the selector is carried across the wall (`GT_wind_eq`) and both present rows are
`wind · ∏ Ω₁ = 0` (`rowTerm_of_mem_Ind`) — the printed "If the common singleton selector is zero, the matched
selector ledger already makes both terms in (2) zero"; when `wind(S) ≠ 0` the body is that of `est_row_H`.
This is the `est_row_H` split that R176_LEDGER_REPORT §3 asks of RALedgers, made on the draft copy. -/
theorem r176_est_row_H_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS := est_S_ind ht.1 hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  by_cases hwind : CV.wind (geomAt E t ht.1) (Q ∪ {j}) = 0
  · -- `wind(S) = 0`: the selector is carried, both row terms vanish
    have h0 : CV.wind (genericAt E t ht.1).crossingGeometry (Q ∪ {j}) = 0 := hwind
    have h0' : CV.wind (genericAt E t' ht'.1).crossingGeometry (transportSupport hs (Q ∪ {j})) = 0 := by
      rw [GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W]; exact h0
    rw [rowTerm_of_mem_Ind hn (genericAt E t ht.1) hS, rowTerm_of_mem_Ind hn (genericAt E t' ht'.1) hS', h0, h0',
      zero_mul, zero_mul]
  · -- `wind(S) ≠ 0`: `est_row_H` verbatim, the port relation at `hwind`
    refine est_rowTerm_eq_of_omega hn _ _ hS hS'
      (GT_wind_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W) (GT_carrierEquiv W) fun q => ?_
    obtain ⟨u, v, hu, hv, hju, hjv, huv⟩ := est_others hef' heg' hfg' hj
    obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
    have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
    by_cases hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q
    · -- the affected carrier: the port ledger (weak form)
      have hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv W q) :=
        (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mpr hq
      obtain ⟨u₁, -, -, hu₁', ⟨D⟩⟩ := hport n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
        hcomp Q hQ hfull j hj q hwind ⟨u, hu, hju.symm, hu'⟩
      exact s176_est_omega1_eq_of_port_weak hn _ _ hS hS' q _ _ hF D
        (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
        (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
    · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- `s176_est_row_weak` (= `est_row`) with the interface under `wind(S) ≠ 0` (byte-identical body). -/
theorem r176_est_row_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g)
    (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact r176_est_row_H_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := r176_est_row_H_weak_uniform hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- `s176_est_extremeTransportData_weak` (= `est_extremeTransportData`) with the interface under `wind(S) ≠ 0`. -/
theorem r176_est_extremeTransportData_weak_uniform (hF : CV.CarrierSlotFloor)
    (hport : r176l_est_port_relation_weak_uniform) (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) :
    ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    r176_est_row_weak_uniform hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end R176Compose

/-- **The RA ledger of row 176 from the interface under `wind(S) ≠ 0`** — `s176_est_ledger_weak` (= `est_ledger`)
with `s176_est_port_relation_weak` replaced by `r176l_est_port_relation_weak_uniform`; byte-identical body. -/
theorem r176_est_ledger_weak_uniform (hF : CV.CarrierSlotFloor) (hport : r176l_est_port_relation_weak_uniform) :
    RowShape @ExtremeTransportData := by
  intro n _ hn E e f g h3 h4e h4f h4g hE
  obtain ⟨δL, hδL, hδLr, hL⟩ := localization E e f g h3 h4e h4f h4g hE
  obtain ⟨δG, hδG, -, hGT⟩ := generic_table E e f g h3 h4e h4f h4g hE
  obtain ⟨δR, hδR, -, hR⟩ := AV_exists_eventRadius hE
  have hef : e ≠ f := AV_ne_of_remote h3.1
  have hfg : f ≠ g := AV_ne_of_remote h3.2.1
  have heg : e ≠ g := AV_ne_of_remote h3.2.2.1
  refine ⟨min δL (min δG δR), lt_min hδL (lt_min hδG hδR), (min_le_left _ _).trans hδLr, ?_⟩
  have hL' := F1.localizationData_mono (min_le_left δL (min δG δR)) hL
  have hGT' := SEL_genericTableData_mono ((min_le_right δL (min δG δR)).trans (min_le_left δG δR)) hGT
  have hR' := AV_eventRadius_mono ((min_le_right δL (min δG δR)).trans (min_le_right δG δR)) hR
  exact r176_est_extremeTransportData_weak_uniform hF hport hn hL' hGT' hR' hef heg hfg

/-- Sanity: the unconditional weak interface still gives the ledger through the split. -/
theorem r176_est_ledger_weak_uniform_of_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) :
    RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform hF (r176l_est_port_relation_weak_uniform_of_weak hport)

/-! ## §X6. The row -/

/-- **`R:extreme_transport` in the fixed row shape from exactly the three open Props of row 176** — the
record-level R-I `r176s_curl_removal`, the outer carriers `r176_outer_carriers_L`, the (14)-bridge
`r176_mixed_bridge` — with the floor `CV.carrierSlotFloor` (thm:carrierfloor (C), library) and the RII port
`hrec` closed by HSUCC.  Once the three Props are proved, `RProof.extreme_transport := r176_extreme_transport_of_curl_outer_mixed
<curl> <outer> <mixed>` (modulo F-176-1 and the port of the moves toolkit). -/
theorem r176_extreme_transport_of_curl_outer_mixed (hcurl : r176s_curl_removal) (hout : r176_outer_carriers_L)
    (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform CV.carrierSlotFloor
    (r176_est_port_relation_weak_uniform_of_curl_outer_mixed hcurl hout hmixed)

/-- The row from the corrected non-move port data alone (`hF` discharged by the library). -/
theorem r176_extreme_transport_of_rest_uniform
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
      (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
      CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
      ∀ (u : Crossing (E.curve t)) (_hu : u.val ∈ triangleSupports e f g) (_hju : j ≠ u)
        (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    RowShape @ExtremeTransportData :=
  r176_est_ledger_weak_uniform CV.carrierSlotFloor (r176_est_port_relation_weak_uniform_of_rest hrest)

/-- **The SMOOTH-route composition**: the unconditional weak interface from the record-level R-I, SMOOTH's
outer carriers `r176s_outer_carriers` (arbitrary `Λ_A, Λ_B` of `S_full = Q' ∪ {j', u', v'}`) and SMOOTH's ledger
black box `r176s_ledger` ((14), (13), (12) for them) — `r176s_est_port_relation_weak_of''` with its `hrec`
discharged by HSUCC.  NOTE (R176_LEDGER_REPORT §3): `r176s_ledger` asserts (13)/(12) also when `wind(S) = 0`,
where they can fail; the route to pursue is §X4–§X6 above. -/
theorem r176_est_port_relation_weak_of_curl_outer_ledger (hcurl : r176s_curl_removal)
    (hout : r176s_outer_carriers) (hled : r176s_ledger) : s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176s_portDataRest_of hcurl hout hled hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp
    hQ hfull hj q hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- The row along the SMOOTH route (same caveat). -/
theorem r176_extreme_transport_of_curl_outer_ledger (hcurl : r176s_curl_removal) (hout : r176s_outer_carriers)
    (hled : r176s_ledger) : RowShape @ExtremeTransportData :=
  s176_est_ledger_weak CV.carrierSlotFloor (r176_est_port_relation_weak_of_curl_outer_ledger hcurl hout hled)

end

end RProof
