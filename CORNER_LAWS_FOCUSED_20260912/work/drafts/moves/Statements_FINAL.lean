import SM.Smoothing
import SM.MarkedProducts
import SM.SingleCrossing
import CV.FullTwist
import RProof.GenericTransport

/-! # Statements_FINAL — the moves toolkit (D-RM-1): judge's decision, 2026-09-15

Companion of work/drafts/moves/PLAN_FINAL.md.  Winner: DESIGN_B (the vertex-run bigon deletion with
`Record.restrictCrossings` as the record clause, the record-level R-I avoidance, the switched-G11 core),
with grafts from DESIGN_A (§1b the record companions — the crossing count and writhe of the reduced
record, and the switch/restriction commutation that lets a consumer move `switch` past the deletion;
§3 the 176 ledger re-base stated as ONE lemma, `fulltwist_coefficient_of_port_weak`, PROVED).

Check: `cd work/lean && lake env lean ../drafts/moves/Statements_FINAL.lean`.

Every `sorry` is a LEAF of the unit decomposition of PLAN_FINAL.md §5 (frozen statement):
* `exists_rii_deletion` — the ONE geometric constructor (units U-M0 … U-M7);
* `exists_bigonData_of_triangle` — its `j = 1` specialisation (U-M7);
* `BigonData.reducedRecord_counts` — record companion (U-M6);
* `Record.restrictCrossings_switch` — record companion (U-M6);
* `G11_core_sw` — the RIII core on the switched positive diagram (Wave 3, row 177 (4)).
Everything else is PROVED from accepted declarations: the instantiation glue of the four consumers
(`s7_rii_witnesses`, `s7_switch_value_of_bigon`, `gsc_fulltwist_of_bigon`, `est_port_weak_of_bigon`,
`fulltwist_skein_of_port_weak`, `fulltwist_coefficient_of_port_weak`, `esc_rii_after_smoothing_of_bigons`,
`esc_switch_riii_of_chain`, `rii_deletion_counts`) and the two avoidance lemmas
(`two_component_row_of_recordIso`, `curl_block_value`).

Conventions: namespace `SM.Link`; `SM.P` is the skein polynomial of lp:core, `homfly` the literature
polynomial; `Record.restrictCrossings` (SM/MarkedProducts.lean:210) is the accepted first-return
restriction that KEEPS every circle — the record of a diagram minus a set of crossings. -/

namespace SM.Link

open SM

noncomputable section

/-! ## 1. The bigon site -/

/-- **A vertex-run bigon site.**  `j = 1`: the vertex–edge bigon (rows 110, 174, 176 — the path is
`M₀ → M₁ → M₂` through one vertex); `j = 2`: the corner-cut bigon of a smoothing output (row 177 (6),
the path `e-piece → arc → f-piece` through the two arc ends).  Multi-component: `s` may lie on any
component; the run lies on component `i`.  The region `K` (convex, compact) is the bigon disc of the
printed proofs (sm-4:618-620 "the isolated contact disc contains no other strand"): the entering
edge meets it in `[y, M₁]`, the exiting edge in `[M_j, z]`, the remote strand in `[y, z]`, the run
lies inside, every other edge is clear of it. -/
structure BigonData (D : Diagram) where
  /-- the component carrying the run -/
  i : Fin D.Γ.c
  /-- the label of the entering edge `e_in = (M₀, M₁)`; the run is `M₁ … M_j = P (a+1) … P (a+j)` -/
  a : ZMod (D.Γ.comp i).k
  /-- the run length -/
  j : ℕ
  hj : 1 ≤ j
  hk : j + 3 ≤ (D.Γ.comp i).k
  /-- the straight remote strand -/
  s : D.Γ.Strand
  /-- the two crossings of the bigon -/
  y : D.Γ.Crossing
  z : D.Γ.Crossing
  hy : y.val = {⟨i, a⟩, s}
  hz : z.val = {⟨i, a + (j : ZMod (D.Γ.comp i).k)⟩, s}
  /-- the run edges are crossing-free -/
  run_free : ∀ m : ℕ, 1 ≤ m → m < j → ∀ x : D.Γ.Crossing,
    (⟨i, a + (m : ZMod (D.Γ.comp i).k)⟩ : D.Γ.Strand) ∉ x.val
  /-- the entering and exiting edges do not cross each other (automatic for `j = 1`) -/
  no_io : ∀ x : D.Γ.Crossing,
    ¬ ((⟨i, a⟩ : D.Γ.Strand) ∈ x.val ∧ (⟨i, a + (j : ZMod (D.Γ.comp i).k)⟩ : D.Γ.Strand) ∈ x.val)
  /-- the common over strand (sm-3:1982-1984 "an empty ordinary bigon with one common over-strand") -/
  same_over : (D.overStrand y = s ∧ D.overStrand z = s) ∨ (D.overStrand y ≠ s ∧ D.overStrand z ≠ s)
  /-- the crossing parameters of `y`, `z` on the entering / exiting edge and on `s` -/
  ty : ℝ
  tz : ℝ
  tsy : ℝ
  tsz : ℝ
  hty : D.Γ.edgePt ⟨i, a⟩ ty = D.Γ.crossingPoint y
  htz : D.Γ.edgePt ⟨i, a + (j : ZMod (D.Γ.comp i).k)⟩ tz = D.Γ.crossingPoint z
  htsy : D.Γ.edgePt s tsy = D.Γ.crossingPoint y
  htsz : D.Γ.edgePt s tsz = D.Γ.crossingPoint z
  /-- the bigon region: convex, compact -/
  K : Set Plane
  K_convex : Convex ℝ K
  K_compact : IsCompact K
  /-- the run vertices lie in `K` (so the run edges do, by convexity) -/
  run_mem : ∀ m : ℕ, 1 ≤ m → m ≤ j → (D.Γ.comp i).P (a + (m : ZMod (D.Γ.comp i).k)) ∈ K
  /-- the entering edge meets `K` exactly in `[y, M₁]` -/
  in_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt ⟨i, a⟩ t ∈ K ↔ ty ≤ t)
  /-- the exiting edge meets `K` exactly in `[M_j, z]` -/
  out_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 →
    (D.Γ.edgePt ⟨i, a + (j : ZMod (D.Γ.comp i).k)⟩ t ∈ K ↔ t ≤ tz)
  /-- the remote strand meets `K` exactly in `[y, z]` -/
  s_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt s t ∈ K ↔ min tsy tsz ≤ t ∧ t ≤ max tsy tsz)
  /-- every other edge is clear of the closed region -/
  clear : ∀ u : D.Γ.Strand, u ≠ ⟨i, a⟩ → u ≠ ⟨i, a + (j : ZMod (D.Γ.comp i).k)⟩ → u ≠ s →
    (∀ m : ℕ, 1 ≤ m → m < j → u ≠ ⟨i, a + (m : ZMod (D.Γ.comp i).k)⟩) → Disjoint (D.Γ.seg u) K

namespace BigonData

variable {D : Diagram} (B : BigonData D)

/-- the record crossings retained by the deletion: everything but `y` and `z` -/
def keep : Set D.record.Crossing :=
  {c | c ≠ D.record.crossingOf (D.overVisit B.y) ∧ c ≠ D.record.crossingOf (D.overVisit B.z)}

/-- the target record: `D`'s record with the four visits of `y, z` deleted (first-return successor;
"the remaining diagram has the same complete decorated record", sm-4:600-606) -/
def reducedRecord : Record := D.record.restrictCrossings B.keep

/-- Sanity (`rfl`): the deletion keeps every circle — a Reidemeister move never changes the components. -/
theorem reducedRecord_componentCount : B.reducedRecord.componentCount = D.record.componentCount := rfl

/-! ### 1b. Record companions (graft from DESIGN_A's `eraseTwo_crossingCount`; unit U-M6) -/

/-- **Leaf (record level, U-M6).**  The reduced record has two crossings fewer and the writhe minus the
two signs (`Record.crossingCount`, `Record.writhe` of LinkRecord; `y ≠ z` because `a ≠ a + j` for
`1 ≤ j < k`). -/
theorem reducedRecord_counts :
    B.reducedRecord.crossingCount + 2 = D.record.crossingCount ∧
    B.reducedRecord.writhe + ((D.record.sgn (D.overVisit B.y) : ℤ) + (D.record.sgn (D.overVisit B.z) : ℤ)) =
      D.record.writhe := by
  sorry

end BigonData

/-- **Leaf (record level, U-M6; graft from DESIGN_A's `eraseTwo_switch`).**  Restricting to a crossing
set commutes with switching a RETAINED crossing: the consumers of row 110 exhibit the bigon on
`D.switch x` and identify `(D.switch x).record` with `D.record.switch v` (`Diagram.switchRecordIso`,
the identity on occurrences), so the reduced record of the switched diagram is the switched reduced
record.  `(ρ.switch v).Crossing` and `ρ.Crossing` are the same type (`Record.switch` keeps `M` and
`pair`). -/
theorem Record.restrictCrossings_switch (ρ : Record) (S : Set ρ.Crossing) (v : ρ.M)
    (hv : ρ.CrossKeep S v) :
    Nonempty (RecordIso ((ρ.switch v).restrictCrossings S) ((ρ.restrictCrossings S).switch ⟨v, hv⟩)) := by
  sorry

/-! ## 2. The constructor (the ONE geometric leaf of the lane) -/

/-- **Generic polygonal R-II deletion** (the leaf of units U-M0 … U-M7, PLAN_FINAL §5).  Construction
(DESIGN_B §3.3): `U := Metric.cthickening (ρ₀/2) K` with `ρ₀` the gap between `K` and the finite union of
the other edge segments and of `M₀`, `M_{j+1}`, the ends of `s` (convex, compact, `K ⊆ interior U`);
`D'` := `D` with the run `M₁ … M_j` replaced by `M' ∈ (p, y)` on the entering edge and `q` = the exit
point of the exiting edge from `U` (`k − j + 2` vertices on component `i`, other components unchanged,
over data pulled back through the strand map); `RIIData U D' D` with arcs `a = [p → M₁ → … → M_j → q]`,
`b = s ∩ U`, `a' = [p → M' → q]`, `b' = b`; the record bridge by a monotone traversal key on component
`i` (Smoothing §8 template: `firstReturn_no_between`, `cycNext_unique_on`). -/
theorem exists_rii_deletion (D : Diagram) (B : BigonData D) :
    ∃ D' : Diagram, RII D' D ∧ D'.componentCount = D.componentCount ∧
      Nonempty (RecordIso D'.record B.reducedRecord) := by
  sorry

/-- **The vertex–edge specialisation (`j = 1`, `K` = the closed contact triangle)** — the site builder
of rows 110 (corner wall), 174 (`m`-corner), 176 (`j`-corner).  The segment clauses `in_iff / out_iff /
s_iff` are automatic for a triangle whose sides are `[y, M₁]`, `[M₁, z]`, `[y, z]` (barycentric side
lemmas; G11's affine-basis toolkit, GenericTransport.lean 9093–9259); the consumer supplies only the
labels, the two crossings, `same_over`, and the printed emptiness "the isolated contact disc contains
no other strand" (sm-4:618-620) as `clear`. -/
theorem exists_bigonData_of_triangle (D : Diagram) (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k)
    (hk : 4 ≤ (D.Γ.comp i).k) (s : D.Γ.Strand) (y z : D.Γ.Crossing)
    (hy : y.val = {⟨i, a⟩, s}) (hz : z.val = {⟨i, a + 1⟩, s})
    (same_over : (D.overStrand y = s ∧ D.overStrand z = s) ∨ (D.overStrand y ≠ s ∧ D.overStrand z ≠ s))
    (clear : ∀ u : D.Γ.Strand, u ≠ ⟨i, a⟩ → u ≠ ⟨i, a + 1⟩ → u ≠ s →
      Disjoint (D.Γ.seg u)
        (convexHull ℝ {D.Γ.crossingPoint y, (D.Γ.comp i).P (a + 1), D.Γ.crossingPoint z})) :
    ∃ B : BigonData D, B.i = i ∧ B.y = y ∧ B.z = z := by
  sorry

/-- **Companions (PROVED from the constructor and the record leaf):** the reduced diagram has two
crossings fewer and writhe `w − sign y − sign z` (`record_crossingCount`, `record_writhe`,
`RecordIso.crossingCount_eq / writhe_eq`). -/
theorem rii_deletion_counts (D : Diagram) (B : BigonData D) :
    ∃ D' : Diagram, RII D' D ∧ D'.componentCount = D.componentCount ∧
      Nonempty (RecordIso D'.record B.reducedRecord) ∧
      Fintype.card D'.Γ.Crossing + 2 = Fintype.card D.Γ.Crossing ∧
      D'.writhe + ((D.sign B.y : ℤ) + (D.sign B.z : ℤ)) = D.writhe := by
  obtain ⟨D', hR, hc, ⟨ι⟩⟩ := exists_rii_deletion D B
  obtain ⟨hcount, hwrithe⟩ := B.reducedRecord_counts
  refine ⟨D', hR, hc, ⟨ι⟩, ?_, ?_⟩
  · rw [← D'.record_crossingCount, ← D.record_crossingCount, ι.crossingCount_eq]
    exact hcount
  · rw [← D'.record_writhe, ← D.record_writhe, ι.writhe_eq]
    exact hwrithe

/-! ## 3. Glue: what each consumer gets by instantiation (PROVED) -/

/-- **Row 110 (bigon branch), `hR` and `hrec` of `s7g_switch_value_of_rii`.**  From a bigon site on
`D.switch x` and the consumer's record identification of the reduced record with `D_L`'s record
(U110-A's persistent-visit-order transport, composed through `Record.restrictCrossings_switch` and
`restrictCrossings_iso_of_recordIso`), the two hypotheses of the accepted glue lemma. -/
theorem s7_rii_witnesses (D : Diagram) (x : D.Γ.Crossing) (B : BigonData (D.switch x)) (DL : Diagram)
    (hrec : Nonempty (RecordIso B.reducedRecord DL.record)) :
    ∃ Dred : Diagram, RII Dred (D.switch x) ∧ Nonempty (RecordIso Dred.record DL.record) := by
  obtain ⟨D', hR, -, ⟨ι⟩⟩ := exists_rii_deletion _ B
  obtain ⟨κ⟩ := hrec
  exact ⟨D', hR, ⟨ι.trans κ⟩⟩

/-- Row 110: the value identity sm-4:600-606 itself (`P (D^{sw}) = P D_L`), with no geometric input
beyond the bigon site (the body is the accepted `P_reidemeister_II` + `presentations`). -/
theorem s7_switch_value_of_bigon (D : Diagram) (x : D.Γ.Crossing) (B : BigonData (D.switch x))
    (DL : Diagram) (hrec : Nonempty (RecordIso B.reducedRecord DL.record)) :
    SM.P (D.switch x) = SM.P DL := by
  obtain ⟨Dred, hR, hrec'⟩ := s7_rii_witnesses D x B DL hrec
  exact (P_reidemeister_II hR).symm.trans (presentations _ _ hrec')

/-- Row 174: `gsc_fulltwist_triple` (U_R174.lean:926) verbatim. -/
def moves_fulltwist_triple (D_L D_H D₀ : Diagram) (q : D_H.Γ.Crossing) : Prop :=
  D_H.IsPositive q ∧ IsOrientedSmoothing D_H q D₀ ∧
    ∃ D_L' : Diagram, Relation.ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L

/-- **Row 174, the G10 move — the interface field `gsc_moves.fulltwist` VERBATIM.**  A bigon site on
`D_H.switch q` (the switched empty pair `a, c` on the `E`-side lift) plus the consumer's record
identification (the wall transport of the carried marks) gives `gsc_fulltwist_triple` with `D₀` the
library smoothing.  No planar-isotopic start is needed: the reduced diagram agrees with `D_H.switch q`
outside the disc literally. -/
theorem gsc_fulltwist_of_bigon (D_L D_H : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1) (B : BigonData (D_H.switch q))
    (hrec : Nonempty (RecordIso B.reducedRecord D_L.record)) :
    ∃ D₀ : Diagram, moves_fulltwist_triple D_L D_H D₀ q := by
  obtain ⟨D₀, h₀⟩ := exists_smoothing D_H q
  obtain ⟨D', hR, hc, ⟨ι⟩⟩ := exists_rii_deletion _ B
  obtain ⟨κ⟩ := hrec
  refine ⟨D₀, hq, h₀, D', Relation.ReflTransGen.single hR.symm, ?_⟩
  exact CV.gausscode_polynomial D' D_L (hc.trans hH) hL (ι.trans κ)

/-- **Row 176: the port field in the form the constructor can deliver** (U_R176.lean:878
`est_PortData.port` asks for the LITERAL `ReflTransGen RII (Dp.switch y) D₀` with `D₀` on the OTHER
side's polygon — false in general, PLAN_FINAL §3 F-176-1; this is the weakened field, the shape of row
174's `gsc_fulltwist_triple`). -/
def est_port_weak (Dp D₀ : Diagram) (y : Dp.Γ.Crossing) : Prop :=
  ∃ D₀' : Diagram, Relation.ReflTransGen RII (Dp.switch y) D₀' ∧ homfly D₀' = homfly D₀

theorem est_port_weak_of_bigon (Dp D₀ : Diagram) (y : Dp.Γ.Crossing) (hp : Dp.componentCount = 1)
    (h₀ : D₀.componentCount = 1) (B : BigonData (Dp.switch y))
    (hrec : Nonempty (RecordIso B.reducedRecord D₀.record)) : est_port_weak Dp D₀ y := by
  obtain ⟨D', hR, hc, ⟨ι⟩⟩ := exists_rii_deletion _ B
  obtain ⟨κ⟩ := hrec
  exact ⟨D', Relation.ReflTransGen.single hR.symm, CV.gausscode_polynomial D' D₀ (hc.trans hp) h₀ (ι.trans κ)⟩

/-- The ledger of row 176 re-based on the weakened port: lem:fulltwist's FIRST display holds verbatim
(`CV.fulltwist_skein` at `D₀'`, then `homfly D₀' = homfly D₀`). -/
theorem fulltwist_skein_of_port_weak (Dp D₀ DA : Diagram) (y : Dp.Γ.Crossing) (hq : Dp.IsPositive y)
    (T1 : IsOrientedSmoothing Dp y DA) (hw : est_port_weak Dp D₀ y) :
    homfly Dp = R.aInv ^ 2 * homfly D₀ + R.aInv * R.z * homfly DA := by
  obtain ⟨D₀', hR, he⟩ := hw
  rw [← he]
  exact CV.fulltwist_skein D₀' Dp DA y hq T1 hR

/-- **Graft (judge): lem:fulltwist's SECOND display from the weakened port** — `CV.fulltwist_coefficient`
with `T2` replaced by `est_port_weak`; the proof is the accepted one (d6:2039–2044) on the re-based first
display.  With this lemma the 176 ledger `est_omega1_eq_of_port` is re-based by replacing ONE call
(`CV.fulltwist_coefficient … D.port …` ↦ `fulltwist_coefficient_of_port_weak … D.port …`). -/
theorem fulltwist_coefficient_of_port_weak (Dp D₀ DA : Diagram) (y : Dp.Γ.Crossing) (hq : Dp.IsPositive y)
    (T1 : IsOrientedSmoothing Dp y DA) (hw : est_port_weak Dp D₀ y)
    (h₀ : D₀.componentCount = 1) (hp : Dp.componentCount = 1)
    (hd : CV.d Dp hp = CV.d D₀ h₀ - 2) :
    CV.Omega Dp hp - CV.Omega D₀ h₀ = coeffAt (CV.d D₀ h₀ - 1) (-1) (homfly DA) := by
  have h1 := fulltwist_skein_of_port_weak Dp D₀ DA y hq T1 hw
  unfold CV.Omega
  rw [hd, h1, coeffAt_add, CV.R.aInv_sq, CV.R.aInv_mul_z, CV.coeffAt_single_mul, CV.coeffAt_single_mul]
  have e1 : CV.d D₀ h₀ - 2 - -2 = CV.d D₀ h₀ := by ring
  have e2 : CV.d D₀ h₀ - 2 - -1 = CV.d D₀ h₀ - 1 := by ring
  rw [e1, e2]
  norm_num

/-- **Row 177 (6), `esc_rii_after_smoothing`** from two bigon sites (one per side, on the switched
smoothing outputs, `j = 2` with the run = the two ends of the corner-cut arc) and the record
identification of the two reduced two-component records (the wall transport with the six local visits
gone, PLAN_FINAL §4.4).  Two components: `presentations`, not `gausscode_polynomial`. -/
theorem esc_rii_after_smoothing_of_bigons (D_H0 D_L0 : Diagram) (y_H : D_H0.Γ.Crossing)
    (y_L : D_L0.Γ.Crossing) (B_H : BigonData (D_H0.switch y_H)) (B_L : BigonData (D_L0.switch y_L))
    (hrec : Nonempty (RecordIso B_H.reducedRecord B_L.reducedRecord)) :
    homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L) := by
  obtain ⟨H', hRH, -, ⟨ιH⟩⟩ := exists_rii_deletion _ B_H
  obtain ⟨L', hRL, -, ⟨ιL⟩⟩ := exists_rii_deletion _ B_L
  obtain ⟨κ⟩ := hrec
  calc homfly (D_H0.switch y_H) = homfly H' := (homfly_reidemeister_II hRH).symm
    _ = homfly L' := by
        rw [← P_eq_homfly, ← P_eq_homfly]
        exact presentations _ _ ⟨ιH.trans (κ.trans ιL.symm)⟩
    _ = homfly (D_L0.switch y_L) := homfly_reidemeister_II hRL

/-- **Row 177 (6), the interface in the form the toolkit can realise**: ONE pair of smoothings (the
library's `smoothDiagram`, with their record clauses), not every pair — `esc_MoveData.rii_after_smoothing`
(U_R177.lean:1123) quantifies over ALL oriented smoothings, whose arcs are arbitrary polygonal paths
inside an arbitrary clean disc (PLAN_FINAL §3 F-177-1).  The ledger (U_R177.lean:1365-1374) obtains its
smoothings from `exists_smoothing_record_visit` and consumes the skein relation at `x` and the record
clause only, so this form suffices. -/
def esc_rii_after_smoothing_weak (D_H D_L : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing)
    (pyH pyL : Plane) : Prop :=
  ∃ (D_H0 D_L0 : Diagram), IsOrientedSmoothing D_H x_H D_H0 ∧ IsOrientedSmoothing D_L x_L D_L0 ∧
    Nonempty (RecordIso D_H0.record (D_H.record.smooth (D_H.overVisit x_H))) ∧
    Nonempty (RecordIso D_L0.record (D_L.record.smooth (D_L.overVisit x_L))) ∧
    ∀ (y_H : D_H0.Γ.Crossing) (y_L : D_L0.Γ.Crossing),
      D_H0.Γ.crossingPoint y_H = pyH → D_L0.Γ.crossingPoint y_L = pyL →
      homfly (D_H0.switch y_H) = homfly (D_L0.switch y_L)

/-! ## 4. Row 177 (4): the RIII through the wall on a SWITCHED positive diagram (G11 generalised) -/

section RIIISw

open RProof

/-- **A triangle configuration with one switched local crossing** (row 177 (4): the `K3` over-order is
cyclic on the positive lift and becomes transitive after switching `x`).  `G11_Config` minus its
`trans` clause plus the switched pair and the transitivity of the SWITCHED over-order. -/
structure G11_ConfigSw (k : ℕ) [NeZero k] where
  hk : 3 ≤ k
  X : LabelledTuple k
  gen : (Shadow.single ⟨k, hk, X⟩).Generic
  m : ZMod k
  p : ZMod k
  q : ZMod k
  hmp : IsCrossing X {m, p}
  hmq : IsCrossing X {m, q}
  hpq : IsCrossing X {p, q}
  order : crossingParameter (xPair hmp) m (mem_pair_left m p) <
    crossingParameter (xPair hmq) m (mem_pair_left m q)
  clear_frontier : ∀ h : ZMod k, h ≠ m → h ≠ p → h ≠ q →
    ∀ x ∈ edgeSegment X h, x ∉ frontier (G11_triangle X hmp hmq hpq)
  clear_vertex : ∀ i : ZMod k, X i ∉ G11_triangle X hmp hmq hpq
  /-- which local pair is switched: `0 = {m,p}`, `1 = {m,q}`, `2 = {p,q}` -/
  sw : Fin 3
  /-- the switched over-order is transitive -/
  trans_sw : ¬ IsAlternating (if sw = 0 then -crossingSign X m p else crossingSign X m p)
    (if sw = 1 then -crossingSign X m q else crossingSign X m q)
    (if sw = 2 then -crossingSign X p q else crossingSign X p q)

namespace G11_ConfigSw

variable {k : ℕ} [NeZero k] (C : G11_ConfigSw k)

def comp : PolyComp := ⟨k, C.hk, C.X⟩

/-- the switched local crossing, read on the shadow -/
def xs : (Shadow.single C.comp).Crossing :=
  (Shadow.singleCrossingEquiv C.comp).symm
    (if C.sw = 0 then xPair C.hmp else if C.sw = 1 then xPair C.hmq else xPair C.hpq)

/-- `D₀^{sw}`: the positive diagram of `X` switched at the local crossing `xs` -/
def D₀sw : Diagram := ((Shadow.single C.comp).positiveDiagram C.gen).switch C.xs

theorem D₀sw_componentCount : C.D₀sw.componentCount = 1 := rfl

def vmp : Visit C.X := ⟨xPair C.hmp, ⟨C.m, mem_pair_left _ _⟩⟩
def vpm : Visit C.X := ⟨xPair C.hmp, ⟨C.p, mem_pair_right _ _⟩⟩
def vmq : Visit C.X := ⟨xPair C.hmq, ⟨C.m, mem_pair_left _ _⟩⟩
def vqm : Visit C.X := ⟨xPair C.hmq, ⟨C.q, mem_pair_right _ _⟩⟩
def vpq : Visit C.X := ⟨xPair C.hpq, ⟨C.p, mem_pair_left _ _⟩⟩
def vqp : Visit C.X := ⟨xPair C.hpq, ⟨C.q, mem_pair_right _ _⟩⟩

/-- the three adjacent transpositions of the RIII move (as `G11_Config.σ`) -/
def σ : Equiv.Perm (Visit C.X) :=
  Equiv.swap C.vmp C.vmq * (Equiv.swap C.vpm C.vpq * Equiv.swap C.vqm C.vqp)

def σD : Equiv.Perm C.D₀sw.Γ.Visit :=
  (Shadow.singleVisitEquiv C.comp).symm.permCongr C.σ

end G11_ConfigSw

/-- **G11 core on the switched diagram** (the statement of `RProof.G11_core_statement` with `D₀`
replaced by `D₀^{sw}`): a diagram `D₁` with the same HOMFLY and an occurrence bijection twisted by the
three transpositions.  Realisation (PLAN_FINAL §5 Wave 3): G11 Units B–D verbatim (shadow-level: `X₀`,
`X₁`, the disc, the arcs, the move match, the crossings inside `U`), D8 / Unit E / Unit F re-derived for
over data "positive except at `xs`" — after a statement-neutral refactor of D8/E to take the over data
of the six local visits as a parameter (DESIGN_A §2's process graft). -/
def G11_core_sw_statement {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : Prop :=
  ∃ (D₁ : Diagram) (Ψ : C.D₀sw.Γ.Visit ≃ D₁.Γ.Visit),
    D₁.componentCount = 1 ∧
    homfly D₁ = homfly C.D₀sw ∧
    (∀ v, Ψ (C.D₀sw.twin v) = D₁.twin (Ψ v)) ∧
    (∀ v, D₁.overBit (Ψ v) = C.D₀sw.overBit v) ∧
    (∀ v, D₁.sign (Ψ v).1 = C.D₀sw.sign v.1) ∧
    (∀ u v w, D₁.VisitBetween (Ψ u) (Ψ v) (Ψ w) ↔ C.D₀sw.VisitBetween (C.σD u) (C.σD v) (C.σD w))

/-- **Leaf (Wave 3, ≈ 4.5–6.5k lines).** -/
theorem G11_core_sw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : G11_core_sw_statement C := by
  sorry

end RIIISw

/-- Row 177 (4) `esc_switch_riii` from the chain `D_H.switch x_H ≃_Reparam M₀ –RIII→ M₁ ≅_record
D_L.switch x_L` (G11's route): only `homfly M₁ = homfly (D_H.switch x_H)` and the record iso
`M₁ ≅ D_L.switch x_L` (G11 Unit F pattern with the switched bit) are consumed. -/
theorem esc_switch_riii_of_chain (D_H D_L M₁ : Diagram) (x_H : D_H.Γ.Crossing) (x_L : D_L.Γ.Crossing)
    (h1 : homfly M₁ = homfly (D_H.switch x_H)) (hc1 : M₁.componentCount = 1)
    (hcL : D_L.componentCount = 1) (hrec : Nonempty (RecordIso M₁.record (D_L.switch x_L).record)) :
    homfly (D_H.switch x_H) = homfly (D_L.switch x_L) := by
  rw [← h1]
  exact CV.gausscode_polynomial M₁ (D_L.switch x_L) hc1 hcL hrec.some

/-! ## 5. Avoidances (PROVED): the R-I curl of row 110 is a record-level fact -/

/-- **The two-component row needs only record identifications of the two knot restrictions** —
`mp:lowest` at `c = 2` (`SM.lowest.two_component_row`) + `presentations`.  The curl `y` of row 110's
`D_A` (a self crossing of component 1) is NOT deleted: the row is read on `D_A` itself. -/
theorem two_component_row_of_recordIso (DA : Diagram) (h2 : DA.componentCount = 2)
    (i j : Fin DA.Γ.c) (hij : i ≠ j) (K₁ K₂ : Diagram)
    (h₁ : Nonempty (RecordIso (DA.knotRestrict i).record K₁.record))
    (h₂ : Nonempty (RecordIso (DA.knotRestrict j).record K₂.record)) :
    zRow (-1) (SM.P DA) =
      aPow (-(twoLinking DA i j)) * (aPow 1 - aPow (-1)) * (zRow 0 (SM.P K₁) * zRow 0 (SM.P K₂)) := by
  rw [SM.lowest.two_component_row DA i j h2 hij, presentations _ _ h₁, presentations _ _ h₂]

open scoped Classical in
/-- **A curl is a block of value one**: for a one-circle record `ρ` whose interlacement blocks are
supplied by actual diagrams (mp:blocks `BlockSupply`), if the block `H₀` is a single self crossing
(the curl `y`: its two occurrences are adjacent, so it interlaces nothing), then every diagram with
record `ρ` has `P` equal to the product over the OTHER blocks — `mp:blocks.product` + lc:single-crossing.
This is the record-level reading of sm-4:857-866 ("the deletion of the curl `y` from component 1 of
`D_A` is that smoothing with the triangle discarded"): the curl-free value of component 1 is the
product of its other blocks, no `RIData` witness.  The consumer (U110-B/H) supplies the `BlockSupply`
from `CV.GroupedKnot.blockSupply` / `CBProducts.product_of_chain`'s family plus a one-crossing
one-circle diagram for the curl block (PLAN_FINAL §4.1). -/
theorem curl_block_value (ρ : Record) (C : ρ.interlacementGraph.ConnectedComponent → Diagram)
    (hB : BlockSupply ρ C) (D : Diagram) (hD : Nonempty (RecordIso D.record ρ))
    (H₀ : ρ.interlacementGraph.ConnectedComponent) (x₀ : (C H₀).Γ.Crossing)
    (h1 : (C H₀).Γ.c = 1) (hx : ∀ y : (C H₀).Γ.Crossing, y = x₀) :
    SM.P D = ∏ H ∈ Finset.univ.erase H₀, SM.P (C H) := by
  rw [SM.blocks.product ρ C hB D hD, ← Finset.mul_prod_erase Finset.univ _ (Finset.mem_univ H₀),
    single_crossing.one_crossing (C H₀) x₀ h1 hx, one_mul]

end

end SM.Link
