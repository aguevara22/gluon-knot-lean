-- W3_Skeleton.lean — corner wave 3 (row 110 thm:C-S7), 2026-09-15: the four open declarations of Corner_Assembled.lean
-- (s7_sliding_law_at 8656-8668, s7_bigon_law_at 9816-9834, thm_C_S7_of / thm_C_S7_of_floor 10008-10039) VERBATIM on top of the
-- ported library (SM.CornerChainUnits = waves 1-2a, SM.CS7Sliding = wave 2b, SM.BigonDeletion = the moves toolkit,
-- SM.CarrierFloorRows = thm_floor), plus the row theorem. Units APPEND prefixed material and may replace ONLY the two `sorry`
-- bodies; statements, names and docstrings are frozen (audit A-110-1, AUTHOR_NOTES 20:46Z).
import SM.CornerChainUnits
import SM.CS7Sliding
import SM.BigonDeletion
import SM.CarrierFloorRows

namespace SM

open Link Carrier

attribute [local instance] Classical.propDecidable

noncomputable section

section VertexEdge

variable {n : ℕ} [NeZero n]

/-- The sliding branch (sm-4:300-406): relocation bijection `φ(x₋) = x₊`, the support bijection
eq. s7c:sliding-bijection with the halves, equal coefficient products eq. s7c:sliding-coefficients, and
the exact selector difference eq. s7c:sliding-selector-difference.  NO floor, NO singleton. -/
theorem s7_sliding_law_at (hn : 3 ≤ n) (g : WallGerm n) (M a : ZMod n) (h : g.SlidingAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


/-! ### Unit BLOCK (wave 3, prefix `s7k_`; PLAN_FINAL §3.3 bigon (2)-(3); serves U110-K `s7_bigon_law_at`):
the universal skein extraction on the ACTUAL positive lifts through the ported R-II site (SM.BigonDeletion:
`s7_switch_value_of_bigon`, no `RIIData` built here), the reading of the oriented smoothing `D_A` (known only
through the record clause of `exists_smoothing_record_visit`) by the two-component row (`s7h_`), the
identification of `D_A`'s two `knotRestrict`s with the half contact carriers' lifts REDUCED TO ABSTRACT GAUSS
RECORDS (`restrict_record`, `RecordIso.smooth`, `CB.positiveLiftRecordIso`: §K; likewise the R-II reduced record
through `Diagram.switchRecordIso`, `RecordIso.switch`: §L — so U110-A/B owe statements about crossing geometries
only, no geometry of `D_A`), the R-I AVOIDANCE
of the `ε = 0` curl `y` through mp:blocks (`curl_block_value`, `SM.blocks.writhe_additive`: the curl is a
single self crossing block of value `1` and writhe `+1`), the writhe / slot bookkeeping (eq. s7c:interlacing-slot,
s7c:noninterlacing-slot from `positiveLift_writhe_eq_carrierCrossingCount` + the crossing partition + the
rotation identities of `s7i_`), and the two extracted rows with the floor reads (sm-4:638-668 interlacing
`Ω_H − Ω_L = −ω₁ω₂`; 736-769 noninterlacing `Ω_H − Ω_L = 0`).

Design.  Everything is stated on FOUR carriers `q_H, q_L, q₁, q₂` of four generic polygons `P_H, P_L`
(the two side polygons, size `n`) and `P₁, P₂` (the halves, sizes `n₁, n₂`), with the geometric inputs of
units A/B/C/F/I as HYPOTHESES bundled in the Prop `s7k_ContactRowData` (the interface this block consumes;
each field names its supplier).  The smoothing `D_A` is a parameter with its record clause, so the consumer
may produce the `knotRestrict` identifications at the record level; the skein relation is transferred to
that `D_A` from the library's smoothing by `presentations`.  The floor `hF` enters ONLY through
`FloorTheoremData.slot_le_of_signed` at `q₁, q₂` (the printed reads sm-4:655-660, 765-769), the singleton
never (the one-newborn rows are U110-K's, sm-4:777-783).  No frozen statement is touched. -/

section S7KBlock

variable {n₁ n₂ : ℕ} [NeZero n₁] [NeZero n₂]

/-! #### A. The skein triple at the contact crossing, on the actual lifts, through the R-II site -/

/-- sm-4:600-606 on the actual lifts: `P (D_H^{sw x}) = H⁺_{L_L}` from a bigon site on the switched high
lift (`BigonData`, SM.BigonDeletion §1: the isolated contact disc `K`, the common over strand) and the
identification of its reduced record with the low lift's record (U110-A's persistent visit order through
`Record.restrictCrossings_switch`).  The R-II witness is produced by `exists_rii_deletion` inside
`s7_switch_value_of_bigon`; nothing geometric is built here. -/
theorem s7k_switch_value (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)) :
    SM.P ((positiveLift hn hPH SH qH hSH).switch x) = cornerHomfly hn hPL SL qL hSL := by
  rw [s7_switch_value_of_bigon _ x B _ hrec]
  unfold cornerHomfly
  exact P_eq_homfly _

/-- The skein relation at the contact crossing `x` of the high lift, read on ANY diagram `D_A` carrying the
record `D_H.record.smooth v` (the clause of `exists_smoothing_record_visit`): `H⁺_{L_H} = a⁻² P (D_H^{sw x}) +
a⁻¹ z P D_A`.  The library's smoothing `D₀` (`s7g_cornerHomfly_skein`) has the same record, so `P D₀ = P D_A`
by `presentations`. -/
theorem s7k_skein_on (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH) {SH : Finset (Crossing PH)}
    (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    cornerHomfly hn hPH SH qH hSH =
      R.aInv * R.aInv * SM.P ((positiveLift hn hPH SH qH hSH).switch x) + R.aInv * R.z * SM.P DA := by
  obtain ⟨D₀, -, -, ⟨ι₀⟩, hsk⟩ := s7g_cornerHomfly_skein hn hPH SH qH hSH x v hv
  obtain ⟨ιA⟩ := hrecA
  rw [hsk, presentations D₀ DA ⟨ι₀.trans ιA.symm⟩]

/-- **eq. s7c:universal-extraction on the actual lifts** (the shape `s7_universal_extraction` consumes, with
`F_H = H⁺_{L_H}`, `F_L = H⁺_{L_L}`, `F_A = P D_A`): `[a^{k−2} z⁰] H⁺_{L_H} = [a^k z⁰] H⁺_{L_L} + [a^{k−1} z⁻¹] P D_A`. -/
theorem s7k_extraction (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record))
    (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) (k : ℤ) :
    coeffAt (k - 2) 0 (cornerHomfly hn hPH SH qH hSH) =
      coeffAt k 0 (cornerHomfly hn hPL SL qL hSL) + coeffAt (k - 1) (-1) (SM.P DA) :=
  s7_universal_extraction _ _ _ k (by
    rw [s7k_skein_on hn hPH hSH qH x v hv DA hrecA, s7k_switch_value hn hPH hPL hSH hSL qH qL x B hrec])

/-- **The crossing partition `m_H = m_L + 2` is encoded in the bigon site** (no separate input): the reduced
record has two crossings fewer than `D_H^{sw x}` (`BigonData.reducedRecord_counts`), the switch keeps the
crossings, and the reduced record is `D_L`'s (`RecordIso.crossingCount_eq`, `card_carrierShadow_crossing`). -/
theorem s7k_count_of_site (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)) :
    carrierCrossingCount hn hPH SH qH = carrierCrossingCount hn hPL SL qL + 2 := by
  obtain ⟨ι⟩ := hrec
  have h1 := B.reducedRecord_counts.1
  rw [ι.crossingCount_eq, Diagram.record_crossingCount, Diagram.record_crossingCount] at h1
  have h2 : Fintype.card (positiveLift hn hPL SL qL hSL).Γ.Crossing = carrierCrossingCount hn hPL SL qL :=
    card_carrierShadow_crossing hn hPL SL qL hSL
  have h3 : Fintype.card ((positiveLift hn hPH SH qH hSH).switch x).Γ.Crossing =
      carrierCrossingCount hn hPH SH qH :=
    card_carrierShadow_crossing hn hPH SH qH hSH
  omega

/-! #### B. The counts on `D_A` (sm-4:496-533): two components, writhe `m_H − 1` -/

/-- `D_A` has two components (`positiveLift_componentCount`, `s7h_componentCount_of_smooth_iso`). -/
theorem s7k_DA_componentCount (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    DA.componentCount = 2 :=
  s7h_componentCount_of_smooth_iso _ DA (positiveLift_componentCount hn hPH SH qH hSH) v hrecA

/-- "the smoothed crossing `q` contributes one" (sm-4:651): `w(D_A) = m_H − 1` (every crossing of the lift is
positive; `positiveLift_writhe_eq_carrierCrossingCount`). -/
theorem s7k_DA_writhe (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))) :
    DA.writhe = (carrierCrossingCount hn hPH SH qH : ℤ) - 1 := by
  rw [s7h_writhe_of_smooth_iso _ DA v hrecA, positiveLift_sign, SignType.coe_one,
    positiveLift_writhe_eq_carrierCrossingCount]

/-! #### C. Reading a component of `D_A` through a record identification (U110-B's output shape) -/

/-- A record identification of a `knotRestrict` of `D_A` with a diagram `K` gives its value (`presentations`). -/
theorem s7k_component_value (DA : Diagram) (i : Fin DA.Γ.c) (K : Diagram)
    (h : Nonempty (RecordIso (DA.knotRestrict i).record K.record)) :
    SM.P (DA.knotRestrict i) = SM.P K :=
  presentations _ _ h

/-- … and its writhe (`RecordIso.writhe_eq`, `record_writhe`). -/
theorem s7k_component_writhe (DA : Diagram) (i : Fin DA.Γ.c) (K : Diagram)
    (h : Nonempty (RecordIso (DA.knotRestrict i).record K.record)) :
    (DA.knotRestrict i).writhe = K.writhe := by
  obtain ⟨ι⟩ := h
  rw [← (DA.knotRestrict i).record_writhe, ι.writhe_eq, K.record_writhe]

/-- The `ε = 1` reading of a component: its record is the record of the positive lift of a half contact
carrier `L` — value `H⁺_L` and writhe `m_L` (eq. s7c:component-polynomial / s7c:component-data). -/
theorem s7k_component_lift {m : ℕ} [NeZero m] (hm : 3 ≤ m) {Q : LabelledTuple m} (hQ : Generic Q)
    {T : Finset (Crossing Q)} (hT : IsDecomposition hm hQ T) (q : Component hm hQ T) (DA : Diagram)
    (i : Fin DA.Γ.c) (h : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hm hQ T q hT).record)) :
    SM.P (DA.knotRestrict i) = cornerHomfly hm hQ T q hT ∧
      (DA.knotRestrict i).writhe = (carrierCrossingCount hm hQ T q : ℤ) := by
  refine ⟨?_, ?_⟩
  · rw [s7k_component_value DA i _ h]
    unfold cornerHomfly
    exact P_eq_homfly _
  · rw [s7k_component_writhe DA i _ h, positiveLift_writhe_eq_carrierCrossingCount]

/-! #### D. The R-I avoidance (sm-4:857-866 read at the record level, WAVE1 §7 / U_S7G §0): the curl `y` of
component 1 at `ε = 0` is a single self crossing BLOCK of the record — value `1` (lc:single-crossing), writhe
`+1` — and the other blocks are the blocks of the half contact carrier's lift.  No `RIData` witness. -/

/-- The value of a diagram whose record has a one-crossing block `H₀` (the curl) equals the value of a
diagram whose record's blocks are the OTHER blocks (`curl_block_value` + `SM.blocks.product`, the block
correspondence `e` with equal block values).  With `D = D_A.knotRestrict 1`, `D' = positiveLift` of the
one-dissent half contact carrier `L₁`, this is `Q₁ = H⁺_{L₁}` (eq. s7c:component-polynomial at `ε = 0`). -/
theorem s7k_curl_component_value (D : Diagram) (ρ : Record) (hD : Nonempty (RecordIso D.record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (x₀ : (C H₀).Γ.Crossing)
    (h1 : (C H₀).Γ.c = 1) (hx : ∀ y : (C H₀).Γ.Crossing, y = x₀)
    (D' : Diagram) (ρ' : Record) (hD' : Nonempty (RecordIso D'.record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (e : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (he : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, SM.P (C H.1) = SM.P (C' (e H))) :
    SM.P D = SM.P D' := by
  rw [curl_block_value ρ C hB D hD H₀ x₀ h1 hx, SM.blocks.product ρ' C' hB' D' hD']
  rw [Finset.prod_subtype (Finset.univ.erase H₀) (p := fun H => H ≠ H₀) (fun H => by simp)
    (fun H => SM.P (C H))]
  exact Fintype.prod_equiv e _ _ he

/-- The writhe companion: the curl block has writhe `+1` (a positive single crossing), the other blocks
match — `w(D) = w(D') + 1` (eq. s7c:pre-curl-writhe `w(component₁(D_A)) = w₁ + 1`; `SM.blocks.writhe_additive`). -/
theorem s7k_curl_component_writhe (D : Diagram) (ρ : Record) (hD : Nonempty (RecordIso D.record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (hw₀ : (C H₀).writhe = 1)
    (D' : Diagram) (ρ' : Record) (hD' : Nonempty (RecordIso D'.record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (e : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (he : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, (C H.1).writhe = (C' (e H)).writhe) :
    D.writhe = D'.writhe + 1 := by
  rw [SM.blocks.writhe_additive ρ C hB D hD, SM.blocks.writhe_additive ρ' C' hB' D' hD',
    ← Finset.add_sum_erase Finset.univ _ (Finset.mem_univ H₀), hw₀, add_comm]
  congr 1
  rw [Finset.sum_subtype (Finset.univ.erase H₀) (p := fun H => H ≠ H₀) (fun H => by simp)
    (fun H => (C H).writhe)]
  exact Fintype.sum_equiv e _ _ he

/-! #### E. The slot bookkeeping (def:C `d_Q = 1 − m_Q − |r_Q|`; sm-4:629-632, 665-670, 758-762) -/

/-- `k_H = k_L − 2` from the crossing partition `m_H = m_L + 2` (U110-A/F: `X(P₊) ∆ X(P₋) = {x, y}`) and the
full rotation through the wall `R_H = R_L` (eq. s7c:full-rotation, U110-I `s7i_full_rotation_germ`). -/
theorem s7k_high_slot (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (qH : Component hn hPH SH)
    (qL : Component hn hPL SL)
    (hm : carrierCrossingCount hn hPH SH qH = carrierCrossingCount hn hPL SL qL + 2)
    (hR : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|) :
    cornerSlot hn hPH SH qH = cornerSlot hn hPL SL qL - 2 := by
  unfold cornerSlot
  rw [hm, hR]
  push_cast
  ring

/-- **eq. s7c:interlacing-slot** on `D_A`: `k_L + 2ℓ = k₁ + k₂` from `w(D_A) = m_H − 1`, the writhe partition
`w(D_A) = w(D_A|ᵢ) + w(D_A|ⱼ) + 2ℓ`, the component writhes `m₁, m₂`, `m_H = m_L + 2` and `R_L = R₁ + R₂`. -/
theorem s7k_interlacing_slot (DA : Diagram) (i j : Fin DA.Γ.c) (h2 : DA.componentCount = 2) (hij : i ≠ j)
    {mH mL m₁ m₂ : ℕ} {RL R₁ R₂ : ℤ} (hwA : DA.writhe = (mH : ℤ) - 1)
    (hw₁ : (DA.knotRestrict i).writhe = (m₁ : ℤ)) (hw₂ : (DA.knotRestrict j).writhe = (m₂ : ℤ))
    (hm : mH = mL + 2) (hR : RL = R₁ + R₂) :
    (1 - (mL : ℤ) - RL) + twoLinking DA i j = (1 - (m₁ : ℤ) - R₁) + (1 - (m₂ : ℤ) - R₂) := by
  have h := s7h_writhe_two_component DA i j h2 hij
  rw [hwA, hw₁, hw₂] at h
  subst hm
  push_cast at h ⊢
  omega

/-- **eq. s7c:noninterlacing-slot** on `D_A`: `k₁ + k₂ − (k_L + 2ℓ) = 2`, i.e. `k_L + 2ℓ = K − 2`, with component
`i` carrying the curl (`w(D_A|ᵢ) = m₁ + 1`, eq. s7c:pre-curl-writhe) and `R₁ + R₂ − R_L = −1`
(eq. s7c:noninterlacing-rotation). -/
theorem s7k_noninterlacing_slot (DA : Diagram) (i j : Fin DA.Γ.c) (h2 : DA.componentCount = 2) (hij : i ≠ j)
    {mH mL m₁ m₂ : ℕ} {RL R₁ R₂ : ℤ} (hwA : DA.writhe = (mH : ℤ) - 1)
    (hw₁ : (DA.knotRestrict i).writhe = (m₁ : ℤ) + 1) (hw₂ : (DA.knotRestrict j).writhe = (m₂ : ℤ))
    (hm : mH = mL + 2) (hR : R₁ + R₂ - RL = -1) :
    (1 - (m₁ : ℤ) - R₁) + (1 - (m₂ : ℤ) - R₂) - ((1 - (mL : ℤ) - RL) + twoLinking DA i j) = 2 := by
  have h := s7h_writhe_two_component DA i j h2 hij
  rw [hwA, hw₁, hw₂] at h
  subst hm
  push_cast at h ⊢
  omega

/-! #### F. The coefficient difference through the two-component row (sm-4:638-651, 736-742) -/

/-- **The extracted difference `Ω_H − Ω_L` before the slot substitution**, in the carriers' vocabulary
(`cornerCoefficient = [a^{d_Q} z⁰] H⁺_Q`): with `k_H = k_L − 2`, the skein extraction at `k = k_L` and the
two-component row on `D_A` (`s7h_extraction_two_component`) give
`Ω_H − Ω_L = [a^{k_L+2ℓ−2} z⁰](Q₁Q₂) − [a^{k_L+2ℓ} z⁰](Q₁Q₂)` with `Q_i = P (D_A|ᵢ)` read as `f₁, f₂`. -/
theorem s7k_coefficient_difference (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hrec : Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record))
    (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (i j : Fin DA.Γ.c) (hij : i ≠ j) (hslot : cornerSlot hn hPH SH qH = cornerSlot hn hPL SL qL - 2)
    {f₁ f₂ : R} (hf₁ : SM.P (DA.knotRestrict i) = f₁) (hf₂ : SM.P (DA.knotRestrict j) = f₂) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      coeffAt (cornerSlot hn hPL SL qL + twoLinking DA i j - 2) 0 (f₁ * f₂) -
        coeffAt (cornerSlot hn hPL SL qL + twoLinking DA i j) 0 (f₁ * f₂) := by
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hrecA
  have hext := s7k_extraction hn hPH hPL hSH hSL qH qL x v hv B hrec DA hrecA (cornerSlot hn hPL SL qL)
  have h := s7h_extraction_two_component DA i j h2 hij hext
  rw [hf₁, hf₂] at h
  rw [cornerCoefficient_eq_coeffAt, cornerCoefficient_eq_coeffAt, hslot]
  exact h

/-! #### G. The floor reads (sm-4:655-668, 765-769) — `hF` enters here and only here -/

/-- `H⁺_L` has no negative `z`-exponent (lp:core `knot_support` on the one-component lift). -/
theorem s7k_cornerHomfly_z_nonneg (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) (d k : ℤ)
    (h : coeffAt d k (cornerHomfly hn hP S q hS) ≠ 0) : 0 ≤ k := by
  unfold cornerHomfly at h
  rw [← P_eq_homfly] at h
  obtain ⟨j, hj⟩ := P_knot_support _ (positiveLift_componentCount hn hP S q hS) d k h
  omega

/-- **The interlacing floor read** (sm-4:655-668): at the two UNIFORM half contact carriers the floor gives
`k_i ≤ mindeg_a H⁺_{L_i}`, and `s7_corner_product` reads `[a^{K−2}](f₁f₂) = 0`, `[a^K](f₁f₂) = ω₁ω₂`. -/
theorem s7k_interlacing_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ - 2) 0
        (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 ∧
      coeffAt (cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) 0
        (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) =
      cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂ :=
  s7_corner_product (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁) (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂)
    (hF.slot_le_of_signed hn₁ P₁ hP₁ S₁ hS₁ q₁ hu₁) (hF.slot_le_of_signed hn₂ P₂ hP₂ S₂ hS₂ q₂ hu₂)
    (s7k_cornerHomfly_z_nonneg hn₁ hP₁ hS₁ q₁) (s7k_cornerHomfly_z_nonneg hn₂ hP₂ hS₂ q₂)

/-- **The noninterlacing floor read** (sm-4:765-769): at the two ONE-DISSENT half contact carriers both reads
`K − 4`, `K − 2` lie below the floor `K = k₁ + k₂` of the product (`coeffAt_mul_eq_zero_of_lt_floor`). -/
theorem s7k_noninterlacing_floor_read (hF : FloorTheoremData) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂)
    {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂)
    {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁)
    (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) (d : ℤ)
    (hd : d < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂) :
    coeffAt d 0 (cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂) = 0 :=
  coeffAt_mul_eq_zero_of_lt_floor (cornerHomfly_ne_zero hn₁ hP₁ S₁ q₁ hS₁)
    (cornerHomfly_ne_zero hn₂ hP₂ S₂ q₂ hS₂) (hF.slot_le_of_signed hn₁ P₁ hP₁ S₁ hS₁ q₁ hu₁)
    (hF.slot_le_of_signed hn₂ P₂ hP₂ S₂ hS₂ q₂ hu₂) hd

/-! #### H. The interface this block consumes (the geometric outputs of units A/B/C/F/I, as hypotheses) and
the two extracted rows -/

/-- **The contact data of one bigon contact carrier pair** — everything the extracted rows need about the
four carriers `L_H, L_L, L₁, L₂` (full contact carriers on the two sides; half contact carriers), per field:
the contact crossing `x` and the bigon site on the switched high lift with the reduced record identified with
the low lift's record (U110-F: the isolated contact disc, `same_over`; U110-A: the persistent visit order —
`s7_switch_value_of_bigon`'s inputs); the smoothing `D_A` with its record clause (produced by
`exists_smoothing_record_visit` / `s7g_cornerHomfly_skein`) and its two component indices; the crossing
partition `m_H = m_L + 2` is NOT a field — it follows from the site (`s7k_count_of_site`); the full rotation through the wall `R_H = R_L`
(U110-I `s7i_full_rotation_germ` on U110-A2's/F's family of the contact carrier).  The branch-dependent
fields (component identifications, `R`-identity, turn patterns) are in the two branch structures below. -/
structure s7k_ContactRowData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) : Prop where
  /-- the bigon site `{x, y}` on the switched high lift at the contact crossing `q = x`, whose reduced
  record is the low lift's record (sm-4:602-606; `s7k_reduced_iso_of_gauss` produces the second conjunct
  from its Gauss-record form) -/
  site : ∃ B : BigonData ((positiveLift hn hPH SH qH hSH).switch x),
    Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record)
  /-- eq. s7c:full-rotation `R_H = R_L` -/
  rotation : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|

/-- **The `ε = 1` (interlacing) branch data** on a smoothing `D_A` of the high lift at `x` (record clause):
component `i` is the positive lift of the half contact carrier `L₁` of the decomposition `T₁` of `λ₁`,
component `j` that of `L₂` (U110-B through `CB.positiveLiftRecordIso`, sm-4:800-835); `R_L = R₁ + R₂`
(U110-I `s7i_carrierRotationInt_interlacing` on U110-C's uniform patterns); both half contact carriers are
uniform (U110-C `s7c_uniform_halves_of_interlacing`, the floor's input). -/
structure s7k_InterlacingData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH) (hPL : Generic PL)
    {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)} (hSH : IsDecomposition hn hPH SH)
    (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH) (qL : Component hn hPL SL)
    (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁)
    (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)}
    (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (i j : Fin DA.Γ.c) : Prop where
  record : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))
  ne : i ≠ j
  comp₁ : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record)
  comp₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record)
  rotation : |carrierRotationInt hn hPL SL qL| =
    |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂|
  pattern₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁)
  pattern₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)

/-- **The `ε = 0` (noninterlacing) branch data**: component `i` of `D_A` carries the curl `y` — its value is
`H⁺_{L₁}` and its writhe `m₁ + 1` (through `s7k_curl_component_value` / `_writhe`, the block route, no R-I);
component `j` is the lift of `L₂`; `R₁ + R₂ − R_L = −1` (U110-I `s7i_carrierRotationInt_noninterlacing`);
both half contact carriers are one-dissent (U110-C `s7c_dissent_halves_of_noninterlacing`). -/
structure s7k_NoninterlacingData (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁} {P₂ : LabelledTuple n₂}
    (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)} {S₂ : Finset (Crossing P₂)}
    (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂) (q₁ : Component hn₁ hP₁ S₁)
    (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (i j : Fin DA.Γ.c) : Prop where
  record : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v))
  ne : i ≠ j
  curl_value : SM.P (DA.knotRestrict i) = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁
  curl_writhe : (DA.knotRestrict i).writhe = (carrierCrossingCount hn₁ hP₁ S₁ q₁ : ℤ) + 1
  comp₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record)
  rotation : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
    |carrierRotationInt hn hPL SL qL| = -1
  pattern₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁)
  pattern₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)

/-- **eq. s7c:interlacing-coefficient-result** (sm-4:638-668): `Ω_H − Ω_L = −ω₁ω₂` at an interlacing
contact carrier pair, from the contact data, the branch data and the floor. -/
theorem s7k_interlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (hc : s7k_ContactRowData hn hPH hPL hSH hSL qH qL x)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x) (DA : Diagram) (i j : Fin DA.Γ.c)
    (hb : s7k_InterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL =
      -(cornerCoefficient hn₁ hP₁ S₁ q₁ hS₁ * cornerCoefficient hn₂ hP₂ S₂ q₂ hS₂) := by
  obtain ⟨B, hrec⟩ := hc.site
  have hcount := s7k_count_of_site hn hPH hPL hSH hSL qH qL x B hrec
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hb.record
  obtain ⟨hf₁, hw₁⟩ := s7k_component_lift hn₁ hP₁ hS₁ q₁ DA i hb.comp₁
  obtain ⟨hf₂, hw₂⟩ := s7k_component_lift hn₂ hP₂ hS₂ q₂ DA j hb.comp₂
  have hslot := s7k_high_slot hn hPH hPL qH qL hcount hc.rotation
  have hdiff := s7k_coefficient_difference hn hPH hPL hSH hSL qH qL x v hv B hrec DA
    hb.record i j hb.ne hslot hf₁ hf₂
  have hK := s7k_interlacing_slot DA i j h2 hb.ne (s7k_DA_writhe hn hPH hSH qH v DA hb.record) hw₁ hw₂
    hcount hb.rotation
  have hK' : cornerSlot hn hPL SL qL + twoLinking DA i j =
      cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; exact hK
  obtain ⟨h0, hprod⟩ := s7k_interlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂
  rw [hdiff, hK', h0, hprod, zero_sub]

/-- **eq. s7c:noninterlacing-extraction, every returned row zero** (sm-4:736-769): `Ω_H − Ω_L = 0` at a
noninterlacing contact carrier pair, from the contact data, the branch data and the floor. -/
theorem s7k_noninterlacing_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (hc : s7k_ContactRowData hn hPH hPL hSH hSL qH qL x)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x) (DA : Diagram) (i j : Fin DA.Γ.c)
    (hb : s7k_NoninterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j) :
    cornerCoefficient hn hPH SH qH hSH - cornerCoefficient hn hPL SL qL hSL = 0 := by
  obtain ⟨B, hrec⟩ := hc.site
  have hcount := s7k_count_of_site hn hPH hPL hSH hSL qH qL x B hrec
  have h2 := s7k_DA_componentCount hn hPH hSH qH v DA hb.record
  obtain ⟨hf₂, hw₂⟩ := s7k_component_lift hn₂ hP₂ hS₂ q₂ DA j hb.comp₂
  have hslot := s7k_high_slot hn hPH hPL qH qL hcount hc.rotation
  have hdiff := s7k_coefficient_difference hn hPH hPL hSH hSL qH qL x v hv B hrec DA
    hb.record i j hb.ne hslot hb.curl_value hf₂
  have hK := s7k_noninterlacing_slot DA i j h2 hb.ne (s7k_DA_writhe hn hPH hSH qH v DA hb.record)
    hb.curl_writhe hw₂ hcount hb.rotation
  have hK' : cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ -
      (cornerSlot hn hPL SL qL + twoLinking DA i j) = 2 := by
    unfold cornerSlot; exact hK
  rw [hdiff, s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂ _
    (by omega), s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hb.pattern₁ hb.pattern₂ _
    (by omega), sub_zero]

/-! #### K. The component identifications at the RECORD level (what U110-B has to supply, with no geometry of
`D_A`): `D_A.knotRestrict i` has the record-level restriction of `D_A.record` to the circle `i`
(`restrict_record`), and `D_A.record ≅ (record D_H).smooth v ≅ (gaussRecord X_H).smooth (Φ v)` through the CB
record bridge `CB.positiveLiftRecordIso` — so each component of `D_A` is a restriction of the smoothing of the
ABSTRACT Gauss record of the contact carrier's self-crossings, and the identification with a half contact
carrier's lift is `((gaussRecord X_H).smooth w).restrict {c} ≅ gaussRecord X_{L_i}`, a statement about the
two crossing geometries (sm-4:496-533 "component 1 / component 2", 800-835). -/

/-- The record of a `knotRestrict` of `D_A` through any record identification `D_A.record ≅ ρ`: the
record-level restriction of `ρ` to the image circle (`Diagram.restrictRecordIso` + `RecordIso.restrict`). -/
theorem s7k_knotRestrict_record_iso (DA : Diagram) {ρ : Record} (ι : RecordIso DA.record ρ)
    (i : Fin DA.Γ.c) :
    Nonempty (RecordIso (DA.knotRestrict i).record (ρ.restrict {ι.e i})) := by
  refine ⟨(DA.restrictRecordIso {i} (Finset.singleton_nonempty i)).trans
    (ι.restrict {i} {ι.e i} fun c => ?_)⟩
  simp only [Finset.mem_singleton]
  exact ι.e.injective.eq_iff

/-- On the actual high lift `D_H = positiveLift q_H`: every component of `D_A` is a record-level restriction of
the smoothing of the abstract Gauss record `gaussRecord (cg P_H) X(L_H)` at the image occurrence of `v`. -/
theorem s7k_component_record_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (i : Fin DA.Γ.c) :
    ∃ c, Nonempty (RecordIso (DA.knotRestrict i).record
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).smooth
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrict {c})) := by
  obtain ⟨ι⟩ := hrecA
  exact ⟨_, s7k_knotRestrict_record_iso DA (ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)) i⟩

/-- **The component identification from its Gauss-record form**: if the restriction of the smoothed Gauss
record of `L_H` to the circle `c` is the Gauss record of the half contact carrier `L` (of the decomposition `T`
of the half `λ`), then `D_A.knotRestrict i` has the record of `L`'s positive lift — the field `comp₁ / comp₂`
of the branch data. -/
theorem s7k_component_iso_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (DA : Diagram)
    (ι : RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)) (i : Fin DA.Γ.c)
    {m : ℕ} [NeZero m] (hm : 3 ≤ m) {Q : LabelledTuple m} (hQ : Generic Q) {T : Finset (Crossing Q)}
    (hT : IsDecomposition hm hQ T) (q : Component hm hQ T)
    (hg : Nonempty (RecordIso
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).smooth
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrict
          {(ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)).e i})
      (CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q)))) :
    Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hm hQ T q hT).record) := by
  obtain ⟨κ⟩ := s7k_knotRestrict_record_iso DA (ι.trans ((CB.positiveLiftRecordIso hn hPH hSH qH).smooth v)) i
  obtain ⟨γ⟩ := hg
  exact ⟨κ.trans (γ.trans (CB.positiveLiftRecordIso hm hQ hT q).symm)⟩

/-! #### L. The R-II reduced record at the RECORD level (what U110-A has to supply): `B.reducedRecord` is
`(D_H^{sw x}).record.restrictCrossings B.keep`, and `(D_H^{sw x}).record ≅ (record D_H).switch v ≅
(gaussRecord X_H).switch (Φ v)` (`Diagram.switchRecordIso`, `RecordIso.switch`, `CB.positiveLiftRecordIso`), so the
reduced record is the switched abstract Gauss record of the contact carrier minus the image of the two
bigon crossings — and its identification with `D_L`'s record is `((gaussRecord X_H).switch w).restrictCrossings K
≅ gaussRecord X_{L_L}`, U110-A's persistent visit order on abstract Gauss records (sm-4:602-606). -/

/-- The image of a crossing set under a record isomorphism (crossings are occurrence pairs, `Finset.map Φ`). -/
def s7k_crossingImage {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) : Set ρ'.Crossing :=
  {c' | ∃ c ∈ X, c'.1 = c.1.map ι.Φ.toEmbedding}

/-- The occurrence-level condition of `CB.restrictCrossings_iso_of_recordIso` for the image set
(`RecordIso.crossingOf_eq`, `Finset.map_injective`). -/
theorem s7k_mem_crossingImage_iff {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) (v : ρ.M) :
    ρ.crossingOf v ∈ X ↔ ρ'.crossingOf (ι.Φ v) ∈ s7k_crossingImage ι X := by
  constructor
  · intro h
    exact ⟨_, h, by rw [ι.crossingOf_eq]⟩
  · rintro ⟨c, hc, hcv⟩
    rw [ι.crossingOf_eq] at hcv
    have hcv' : (ρ.crossingOf v).1.map ι.Φ.toEmbedding = c.1.map ι.Φ.toEmbedding := hcv
    have h1 : ρ.crossingOf v = c := Subtype.ext (Finset.map_injective _ hcv')
    rw [h1]; exact hc

/-- Restriction to a crossing set transports along a record isomorphism, onto the image set. -/
theorem s7k_restrictCrossings_iso {ρ ρ' : Record} (ι : RecordIso ρ ρ') (X : Set ρ.Crossing) :
    Nonempty (RecordIso (ρ.restrictCrossings X) (ρ'.restrictCrossings (s7k_crossingImage ι X))) :=
  CB.restrictCrossings_iso_of_recordIso ι X _ (s7k_mem_crossingImage_iff ι X)

/-- **The reduced record of a bigon site on the switched high lift is a restriction of the switched Gauss
record of `L_H`.** -/
theorem s7k_reducedRecord_iso_of_gauss (hn : 3 ≤ n) {PH : LabelledTuple n} (hPH : Generic PH)
    {SH : Finset (Crossing PH)} (hSH : IsDecomposition hn hPH SH) (qH : Component hn hPH SH)
    (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (hv : v.1 = x) (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x)) :
    Nonempty (RecordIso B.reducedRecord
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).switch
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrictCrossings
          (s7k_crossingImage (((positiveLift hn hPH SH qH hSH).switchRecordIso x v hv).trans
            ((CB.positiveLiftRecordIso hn hPH hSH qH).switch v)) B.keep))) :=
  s7k_restrictCrossings_iso _ B.keep

/-- **The field `reduced_iso` from its Gauss-record form**: if the switched Gauss record of `L_H` minus the
bigon crossings is the Gauss record of `L_L` (U110-A), then the reduced record is `D_L`'s record. -/
theorem s7k_reduced_iso_of_gauss (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (x : (positiveLift hn hPH SH qH hSH).Γ.Crossing)
    (v : (positiveLift hn hPH SH qH hSH).Γ.Visit) (hv : v.1 = x)
    (B : BigonData ((positiveLift hn hPH SH qH hSH).switch x))
    (hg : Nonempty (RecordIso
      (((CB.gaussRecord (CB.cg hn hPH) (carrierCrossings hn hPH SH qH)).switch
        ((CB.positiveLiftRecordIso hn hPH hSH qH).Φ v)).restrictCrossings
          (s7k_crossingImage (((positiveLift hn hPH SH qH hSH).switchRecordIso x v hv).trans
            ((CB.positiveLiftRecordIso hn hPH hSH qH).switch v)) B.keep))
      (CB.gaussRecord (CB.cg hn hPL) (carrierCrossings hn hPL SL qL)))) :
    Nonempty (RecordIso B.reducedRecord (positiveLift hn hPL SL qL hSL).record) := by
  obtain ⟨κ⟩ := s7k_reducedRecord_iso_of_gauss hn hPH hSH qH x v hv B
  obtain ⟨γ⟩ := hg
  exact ⟨κ.trans (γ.trans (CB.positiveLiftRecordIso hn hPL hSL qL).symm)⟩

/-! #### I. Constructors for the branch data from the outputs of U110-C/I and the mp:blocks curl route -/

/-- A one-crossing diagram whose crossing is positive has writhe `+1` (the curl block `y`: a positive self
crossing of the positive lift, kept by the smoothing). -/
theorem s7k_single_crossing_writhe (D : Diagram) (x₀ : D.Γ.Crossing) (hx : ∀ y : D.Γ.Crossing, y = x₀)
    (hpos : D.IsPositive x₀) : D.writhe = 1 := by
  unfold Diagram.writhe
  rw [Finset.sum_eq_single x₀ (fun y _ hy => absurd (hx y) hy) (fun h => absurd (Finset.mem_univ _) h),
    (D.isPositive_iff_sign_eq_one x₀).mp hpos, SignType.coe_one]

/-- **The interlacing branch data from U110-B's record identifications and U110-C/I's uniform patterns**:
the principal-turn-preserving corner correspondence `e`/`he` of the three contact carriers (U110-I's `he`,
which U110-B builds from "inherited corner edges are positive multiples", `s7i_principalTurn_eq_of_edges_pos_smul`)
and the three uniform patterns of sign `s₀` (`s7c_uniform_halves_of_interlacing` at a live selector) give
`R_L = R₁ + R₂` (`s7i_carrierRotationInt_interlacing`) and the floor's patterns. -/
theorem s7k_interlacingData_of_patterns (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (DA : Diagram) (i j : Fin DA.Γ.c)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (hij : i ≠ j)
    (h₁ : Nonempty (RecordIso (DA.knotRestrict i).record (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record))
    (h₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record))
    {j₀ : ZMod (ccpCornerCount hn hPL SL qL)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hPL SL qL) // i ≠ j₀})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hPL SL qL) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hall₁ : ∀ i, turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = s₀)
    (hall₂ : ∀ i, turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hPL SL qL) i = s₀) :
    s7k_InterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j :=
  ⟨hrecA, hij, h₁, h₂,
    s7i_carrierRotationInt_interlacing hn hPL hSL qL hn₁ hP₁ hS₁ q₁ hn₂ hP₂ hS₂ q₂ e he hs₀ hall₁ hall₂ hall,
    s7c_signedUniformOrOneDissent_of_forall _ hs₀ hall₁, s7c_signedUniformOrOneDissent_of_forall _ hs₀ hall₂⟩

/-- **The noninterlacing branch data through the mp:blocks curl route** (no `RIData`): component `i` of `D_A`
has a record `ρ` with a block supply `C` whose block `H₀` is a positive single crossing (the curl `y`), the
lift of the one-dissent half contact carrier `L₁` has a record `ρ'` with a block supply `C'`, and the other
blocks correspond (`e`, equal block values and writhes — the consumer supplies the same block diagrams on
both sides); component `j` is the lift of `L₂`; the one-dissent patterns and the principal-turn correspondence
give `R₁ + R₂ − R_L = −1` (`s7i_carrierRotationInt_noninterlacing`) and the floor's patterns
(`s7c_signedUniformOrOneDissent_of_dissent`). -/
theorem s7k_noninterlacingData_of_blocks (hn : 3 ≤ n) {PH PL : LabelledTuple n} (hPH : Generic PH)
    (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂) (v : (positiveLift hn hPH SH qH hSH).Γ.Visit)
    (DA : Diagram) (i j : Fin DA.Γ.c)
    (hrecA : Nonempty (RecordIso DA.record ((positiveLift hn hPH SH qH hSH).record.smooth v)))
    (hij : i ≠ j)
    -- the curl component through mp:blocks
    (ρ : Record) (hρ : Nonempty (RecordIso (DA.knotRestrict i).record ρ))
    (C : ρ.interlacementGraph.ConnectedComponent → Diagram) (hB : BlockSupply ρ C)
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (x₀ : (C H₀).Γ.Crossing)
    (h1 : (C H₀).Γ.c = 1) (hx : ∀ y : (C H₀).Γ.Crossing, y = x₀) (hpos : (C H₀).IsPositive x₀)
    (ρ' : Record) (hρ' : Nonempty (RecordIso (positiveLift hn₁ hP₁ S₁ q₁ hS₁).record ρ'))
    (C' : ρ'.interlacementGraph.ConnectedComponent → Diagram) (hB' : BlockSupply ρ' C')
    (eB : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀} ≃ ρ'.interlacementGraph.ConnectedComponent)
    (heP : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, SM.P (C H.1) = SM.P (C' (eB H)))
    (hew : ∀ H : {H : ρ.interlacementGraph.ConnectedComponent // H ≠ H₀}, (C H.1).writhe = (C' (eB H)).writhe)
    -- the second component
    (h₂ : Nonempty (RecordIso (DA.knotRestrict j).record (positiveLift hn₂ hP₂ S₂ q₂ hS₂).record))
    -- the turn patterns and the corner correspondence
    {j₀ : ZMod (ccpCornerCount hn hPL SL qL)} {j₁ : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁)}
    {j₂ : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂)}
    (e : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} ⊕
        {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} ≃
      {i : ZMod (ccpCornerCount hn hPL SL qL) // i ≠ j₀})
    (he : ∀ x, principalTurn (ccpCornerPolygon hn hPL SL qL) (e x).1 =
      Sum.elim (fun y : {i : ZMod (ccpCornerCount hn₁ hP₁ S₁ q₁) // i ≠ j₁} =>
          principalTurn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) y.1)
        (fun y : {i : ZMod (ccpCornerCount hn₂ hP₂ S₂ q₂) // i ≠ j₂} =>
          principalTurn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) y.1) x)
    {s₀ : SignType} (hs₀ : s₀ ≠ 0)
    (hj₁ : turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) j₁ = s₀)
    (hrest₁ : ∀ i, i ≠ j₁ → turn (ccpCornerPolygon hn₁ hP₁ S₁ q₁) i = -s₀)
    (hj₂ : turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) j₂ = s₀)
    (hrest₂ : ∀ i, i ≠ j₂ → turn (ccpCornerPolygon hn₂ hP₂ S₂ q₂) i = -s₀)
    (hall : ∀ i, turn (ccpCornerPolygon hn hPL SL qL) i = -s₀) :
    s7k_NoninterlacingData hn hPH hPL hSH hSL qH qL hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ v DA i j := by
  refine ⟨hrecA, hij, ?_, ?_, h₂,
    s7i_carrierRotationInt_noninterlacing hn hPL hSL qL hn₁ hP₁ hS₁ q₁ hn₂ hP₂ hS₂ q₂ e he hs₀ hj₁ hrest₁
      hj₂ hrest₂ hall,
    s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₁ (by rw [hj₁, neg_neg]) hrest₁,
    s7c_signedUniformOrOneDissent_of_dissent _ (s7c_neg_sign_ne_zero hs₀) j₂ (by rw [hj₂, neg_neg]) hrest₂⟩
  · rw [s7k_curl_component_value _ ρ hρ C hB H₀ x₀ h1 hx _ ρ' hρ' C' hB' eB heP]
    unfold cornerHomfly
    exact P_eq_homfly _
  · rw [s7k_curl_component_writhe _ ρ hρ C hB H₀ (s7k_single_crossing_writhe _ x₀ hx hpos) _ ρ' hρ' C' hB'
      eB hew, positiveLift_writhe_eq_carrierCrossingCount]

/-! #### J. The term shape U110-K consumes (eq. s7c:interlacing-selector / s7c:noninterlacing-selector with
the extracted rows; sm-4:669-676, 770-776) -/

/-- The interlacing TERM: with the selector law `wt(L*) = −s₀ wt(L₁) wt(L₂)` (`s7c_carrierWeight_interlacing`,
the same `wt(L*)` on both sides — the contact carrier's turns are constant through the wall) and the row
`Ω_H − Ω_L = −ω₁ω₂`, the contact carrier's contribution changes by `s₀ (wt(L₁) ω₁)(wt(L₂) ω₂)`. -/
theorem s7k_interlacing_term {wt wt₁ wt₂ ΩH ΩL ω₁ ω₂ : ℤ} {s₀ : SignType}
    (hwt : wt = -(s₀ : ℤ) * (wt₁ * wt₂)) (hrow : ΩH - ΩL = -(ω₁ * ω₂)) :
    wt * ΩH - wt * ΩL = (s₀ : ℤ) * ((wt₁ * ω₁) * (wt₂ * ω₂)) := by
  have : wt * ΩH - wt * ΩL = wt * (ΩH - ΩL) := by ring
  rw [this, hrow, hwt]; ring

/-- The noninterlacing TERM: `Ω_H − Ω_L = 0` kills the contact carrier's difference outright (whatever the
selector), and independently `s7c_carrierWeight_noninterlacing`'s `wt(L*) (wt(L₁) wt(L₂)) = 0` kills the
returned product row — both printed readings of "every returned row is zero" (sm-4:770-776). -/
theorem s7k_noninterlacing_term {wt wt₁ wt₂ ΩH ΩL ω₁ ω₂ : ℤ} (hrow : ΩH - ΩL = 0)
    (hwt : wt * (wt₁ * wt₂) = 0) :
    wt * ΩH - wt * ΩL = 0 ∧ wt * ((wt₁ * ω₁) * (wt₂ * ω₂)) = 0 := by
  refine ⟨?_, ?_⟩
  · have : wt * ΩH - wt * ΩL = wt * (ΩH - ΩL) := by ring
    rw [this, hrow, mul_zero]
  · have : wt * ((wt₁ * ω₁) * (wt₂ * ω₂)) = (wt * (wt₁ * wt₂)) * (ω₁ * ω₂) := by ring
    rw [this, hwt, zero_mul]

/-! #### M. Two further rows of the bigon branch in the term shape of eq. C-selector-form
(`wind S * cornerProduct S`, `C_X1.selector_form`): the one-newborn rows (sm-4:777-783, cb:singleton ENTERS)
and the contact triangle at `ε = 0` (sm-4:437-447, `corner_values_i`). -/

/-- **The one-newborn rows** (sm-4:777-783): a support whose carrier `q` owns a crossing `c` interlacing no
other crossing of `q` contributes `0` — if `q` is uniform, `c(q) = 0` by cb:singleton (`hsing.isolated_zero`);
otherwise its selector `wt(q) = 0` (`carrierWeight_eq_zero_of_not_uniform`).  For `T ∪ {x}` with the isolated
block `{y}` this is the printed sentence "the singleton block `{y}` … the row is zero". -/
theorem s7k_one_newborn_term_zero (hsing : CbSingletonData) (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S)
    (c : Crossing P) (hc : c ∈ carrierCrossings hn hP S q)
    (hiso : ∀ c' ∈ carrierCrossings hn hP S q, c' ≠ c → ¬ Interlaces hn hP c c') :
    wind hn hP S * cornerProduct hn hP S hS = 0 := by
  by_cases hu : CarrierUniform hn hP S q
  · have h0 : cornerCoefficient hn hP S q hS = 0 := hsing.isolated_zero n hn P hP S hS q hu c hc hiso
    unfold cornerProduct
    rw [Finset.prod_eq_zero (Finset.mem_univ q) h0, mul_zero]
  · unfold wind
    rw [Finset.prod_eq_zero (Finset.mem_univ q) (carrierWeight_eq_zero_of_not_uniform hn hP S q hu),
      zero_mul]

/-- **The contact triangle** (sm-4:437-447, eq. s7c:triangle-data): a crossing-free carrier with three
corners all of turn `−s₀` has `wt = s₀` (`s7c_carrierWeight_triangle`) and, being uniform and embedded,
`|rot| = 1`, `d = 0`, `c = 1` (`corner_values_i`, unconditional) — its factor in the `ε = 0` high-side term
is `wt · c = s₀`. -/
theorem s7k_triangle_factor (hn : 3 ≤ n) {P : LabelledTuple n} (hP : Generic P)
    {S : Finset (Crossing P)} (hS : IsDecomposition hn hP S) (q : Component hn hP S) {s₀ : SignType}
    (hs₀ : s₀ ≠ 0) (h3 : ccpCornerCount hn hP S q = 3)
    (hturn : ∀ j, turn (ccpCornerPolygon hn hP S q) j = -s₀) (hm : carrierCrossingCount hn hP S q = 0) :
    carrierWeight hn hP S q * cornerCoefficient hn hP S q hS = (s₀ : ℤ) ∧
      cornerSlot hn hP S q = 0 ∧ |carrierRotation hn hP S q| = 1 := by
  have hu : CarrierUniform hn hP S q := ⟨-s₀, s7c_neg_sign_ne_zero hs₀, hturn⟩
  obtain ⟨hrot, hslot, hc⟩ := corner_values_i hn hP hS q hu hm
  refine ⟨?_, hslot, hrot⟩
  rw [s7c_carrierWeight_triangle hn hP S q hs₀ h3 hturn, hc, mul_one]

/-- **The different-block alternative** (sm-4:785-813; eqs. s7c:different-low-slot / -high-slot): when both
newborns `x, y` are singleton blocks of the contact carrier, mp:blocks gives `H⁺_{L_H} = H⁺_{L_L} = f₁ f₂` (the
consumer's two hypotheses `hfH`, `hfL`, from `product_of_chain` / `curl_block_value` with the two one-crossing
blocks of value `1`), the writhes are `m_L = m₁ + m₂`, `m_H = m₁ + m₂ + 2`, the rotations `R₁ + R₂ − R_L = −1`,
`R_H = R_L`; then `k_L = K − 2`, `k_H = K − 4` (`s7i_different_slot`) and both reads lie below the floor `K` of
`f₁ f₂` at the one-dissent half contact carriers: `Ω_H = Ω_L = 0`. -/
theorem s7k_different_block_row (hF : FloorTheoremData) (hn : 3 ≤ n) {PH PL : LabelledTuple n}
    (hPH : Generic PH) (hPL : Generic PL) {SH : Finset (Crossing PH)} {SL : Finset (Crossing PL)}
    (hSH : IsDecomposition hn hPH SH) (hSL : IsDecomposition hn hPL SL) (qH : Component hn hPH SH)
    (qL : Component hn hPL SL) (hn₁ : 3 ≤ n₁) (hn₂ : 3 ≤ n₂) {P₁ : LabelledTuple n₁}
    {P₂ : LabelledTuple n₂} (hP₁ : Generic P₁) (hP₂ : Generic P₂) {S₁ : Finset (Crossing P₁)}
    {S₂ : Finset (Crossing P₂)} (hS₁ : IsDecomposition hn₁ hP₁ S₁) (hS₂ : IsDecomposition hn₂ hP₂ S₂)
    (q₁ : Component hn₁ hP₁ S₁) (q₂ : Component hn₂ hP₂ S₂)
    (hfH : cornerHomfly hn hPH SH qH hSH = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hfL : cornerHomfly hn hPL SL qL hSL = cornerHomfly hn₁ hP₁ S₁ q₁ hS₁ * cornerHomfly hn₂ hP₂ S₂ q₂ hS₂)
    (hmH : carrierCrossingCount hn hPH SH qH =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂ + 2)
    (hmL : carrierCrossingCount hn hPL SL qL =
      carrierCrossingCount hn₁ hP₁ S₁ q₁ + carrierCrossingCount hn₂ hP₂ S₂ q₂)
    (hR : |carrierRotationInt hn₁ hP₁ S₁ q₁| + |carrierRotationInt hn₂ hP₂ S₂ q₂| -
      |carrierRotationInt hn hPL SL qL| = -1)
    (hRH : |carrierRotationInt hn hPH SH qH| = |carrierRotationInt hn hPL SL qL|)
    (hu₁ : SignedUniformOrOneDissent (ccpCornerPolygon hn₁ hP₁ S₁ q₁))
    (hu₂ : SignedUniformOrOneDissent (ccpCornerPolygon hn₂ hP₂ S₂ q₂)) :
    cornerCoefficient hn hPH SH qH hSH = 0 ∧ cornerCoefficient hn hPL SL qL hSL = 0 := by
  have hkL : cornerSlot hn hPL SL qL < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; rw [hmL]; push_cast; omega
  have hkH : cornerSlot hn hPH SH qH < cornerSlot hn₁ hP₁ S₁ q₁ + cornerSlot hn₂ hP₂ S₂ q₂ := by
    unfold cornerSlot; rw [hmH, hRH]; push_cast; omega
  refine ⟨?_, ?_⟩
  · rw [cornerCoefficient_eq_coeffAt, hfH]
    exact s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ _ hkH
  · rw [cornerCoefficient_eq_coeffAt, hfL]
    exact s7k_noninterlacing_floor_read hF hn₁ hn₂ hP₁ hP₂ hS₁ hS₂ q₁ q₂ hu₁ hu₂ _ hkL

end S7KBlock

/-- The bigon branch (sm-4:407-874): two-newborn sector `B = (1−ε)J` (contact triangle: a crossing-free
uniform carrier, `corner_values_i`), universal skein extraction eq. s7c:universal-extraction (lp:core
skein, R-II deletion, oriented smoothing), lem:homflyrows two-component row, the rotation ledger, and the
two floor-dependent branches (interlacing: `Ω_H − Ω_L = −ω₁ω₂`; noninterlacing: every returned row zero,
the one-newborn rows by cb:singleton).  `a_floor` enters at the two half contact carriers (uniform for
`ε = 1`, one-dissent for `ε = 0`), read as carriers of the decompositions `T_i` of the generic halves
`λ_i` (sm-4:800-835); cb:singleton enters at the one-newborn rows (sm-4:777-783) — both printed
dependencies are explicit parameters. -/
theorem s7_bigon_law_at (hF : FloorTheoremData) (hsing : CbSingletonData) (hn : 3 ≤ n)
    (g : WallGerm n) (M a : ZMod n) (h : g.BigonAt M a)
    (h₁ : Generic (firstHalf g.center M a)) (h₂ : Generic (secondHalf g.center M a)) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1.1).2.1 h₂) := by
  sorry


end VertexEdge

/-- **Row 110, conditional on thm:floor AND cb:singleton** (the printed dependency list of
tools/claims.py; library material).  PROVED from the two branch leaves: the wall is of bigon or sliding
type (`vertexEdge_bigon_or_sliding`); both side parameters are moved below the branch radius by chamber
constancy along each side (`cornerStateSum_side_eq`). -/
theorem thm_C_S7_of (hF : FloorTheoremData) (hsing : CbSingletonData) : CS7Data := by
  refine ⟨?_⟩
  intro n _ hn g M a h h₁ h₂ tp tm
  obtain ⟨δ, hδ, hlaw⟩ : ∃ δ : ℝ, 0 < δ ∧ ∀ t : g.SideParameter, t.val < δ →
      cornerStateSum hn (g.sideTuple true t).property -
          cornerStateSum hn (g.sideTuple false t).property =
        (g.contactSign M a : ℤ) *
          (cornerStateSum (contactHalfSizes_bounds hn h.1).1.1 h₁ *
            cornerStateSum (contactHalfSizes_bounds hn h.1).2.1 h₂) := by
    rcases g.vertexEdge_bigon_or_sliding h with hb | hs
    · exact s7_bigon_law_at hF hsing hn g M a hb h₁ h₂
    · exact s7_sliding_law_at hn g M a hs h₁ h₂
  have hr := g.radius_pos
  let t : g.SideParameter := ⟨min δ g.radius / 2, by
    constructor
    · have := lt_min hδ hr; linarith
    · have := min_le_right δ g.radius; linarith⟩
  have ht : t.val < δ := by
    show min δ g.radius / 2 < δ
    have := min_le_left δ g.radius; linarith
  rw [cornerStateSum_side_eq hn g true tp t, cornerStateSum_side_eq hn g false tm t]
  exact hlaw t ht

/-- **Row 110, conditional on the floor alone** (the row theorem `SM.thm_C_S7 := thm_C_S7_of_floor
SM.thm_floor` once row 100 lands). -/
theorem thm_C_S7_of_floor (hF : FloorTheoremData) : CS7Data :=
  thm_C_S7_of hF (cb_singleton_of_floor hF)


/-- Row 110 thm:C-S7 (FIXED target name, axiom-policy.json): the assembly on thm:floor (row 100). -/
theorem thm_C_S7 : CS7Data := thm_C_S7_of_floor thm_floor

end

end SM
