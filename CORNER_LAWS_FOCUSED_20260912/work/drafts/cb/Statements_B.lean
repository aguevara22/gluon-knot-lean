import SM.MarkedProducts
import SM.CornerStateSum
import SM.CarriersLemma
import SM.GaussCyclicGap
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Actual carrier blocks — statements for cb:blocks (row 101) and cb:products (row 102)

Draft B (2026-09-14; design panel work/drafts/cb/, plan work/drafts/cb/PLAN_B.md). Emphasis: literal
fidelity to the printed SM text, stated in SM vocabulary on the accepted SM Carrier lane.

Source (frame SM15): reference/SM/sm-3-statesum.tex — cb:blocks 4623–4637 (eq. cb:undominated 4628),
cb:products 4638–4651 (eq. cb:product 4646; proof 4652–4696, eq. cb:greedy-step 4662). Consumers read
for shape only: cb:singleton 4697–4759, thm:C-S7 (sm-4-knotlaws.tex:267–330).

Main declarations: `SM.cb_blocks_definition : CbBlocksDefinitionData hn hP S hS` (DEFINE row 101) and
`SM.cb_products : CbProductsData hn hP S hS` (PROVE row 102); both `sorry` here (statements only).
Each field of a bundle renders one printed clause and quotes it; fields marked "(proof)" render a
sentence of the printed proof that a later row cites (eq. cb:greedy-step is cited by cb:singleton).

## Binders (as printed)

"Fix a generic polygon `P`, its interlacement graph `G_P`, and an independent support `S`":
`hn : 3 ≤ n`, `hP : SM.Generic P` (the SM generic class, def:polygon/def:chirotope, as in every
Chapter-3 row: def:smoothing, lem:carriers, def:C), `S : Finset (Crossing P)`,
`hS : IsDecomposition hn hP S` (= `S ∈ independentSupports hn hP` = `S ∈ Ind(G_P)`, def:decomposition).
`G_P = interlacementGraph hn hP` (accepted def:interlace).

## Notation map (printed → Lean; everything on the accepted SM Carrier lane)

* `V(G_P) = X(P)`: `Crossing P` (`Finset.univ`); `N_{G_P}(T)`: `supportNeighbors hn hP T`
  (SM/InterlaceSupports.lean:49, "the set of crossings interlacing some element of T");
  `U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`: `supportUnselected hn hP S` (ibid.:60, `supportUnselected_eq`
  is the printed equation by `rfl`).
* "the induced subgraph `G_P[U(S)]`": `residualGraph hn hP S := (interlacementGraph hn hP).induce
  ↑(supportUnselected hn hP S)` (Mathlib `SimpleGraph.induce`); "its blocks", "the connected
  components": `Block hn hP S := (residualGraph hn hP S).ConnectedComponent`; the block of
  `c ∈ U(S)`: `blockOf`; the crossings ("labels") of a block `H`: `blockLabels hn hP S H`; `|H|` is
  `(blockLabels hn hP S H).card`. These are thin SM restatements of the accepted CV objects
  `CV.residualGraph` / `CV.Piece` / `CV.pieceLabels` (CV/Carriers.lean §6, CV:def:pieces) read at
  `generic_crossingGeometry hn hP`: the graphs are equal by `geometricInterlacementGraph_eq_generic`
  (`rfl`) and the vertex sets by `CV.U_eq_generic` (CV/Events.lean:215); the bridge
  `blockEquivPiece` is a plan lemma (PLAN_B §4), not part of the row.
* "carrier `A`": `A : Component hn hP S` (def:smoothing, the accepted carriers of `S`); "a visit lies on
  a carrier": `owner hn hP S (Sum.inr v) = A` (conv:selected-visits at selected visits; here only
  unselected visits matter).
* "An undominated crossing has both visits on one carrier by Lemma lem:carriers; that carrier is its
  owner": `crossingOwner hn hP S c := owner hn hP S (Sum.inr (someVisit c))` — the carrier of a fixed
  visit of `c` (`someVisit`, hypothesis-free); the field `owner_spec` says that for `c ∈ U(S)` it is the
  carrier of EITHER visit (lem:carriers (iii), accepted `carriers_lemma.nonneighbor_visits_together`).
  The owner of a block: `blockOwner hn hP S H := crossingOwner hn hP S (blockRep H)` (a fixed label of
  `H`); "the blocks owned by `A`": `blocksOwnedBy hn hP S A`.
* "`D_A`, the actual positive diagram of a carrier `A`": the accepted `positiveLift hn hP S A hS :
  Diagram` (def:positive-lift, SM/LinkPositiveLift.lean:596 — the one-component diagram on the
  corner polygon `ccpCornerPolygon hn hP S A` with every crossing positive; its crossings are
  `carrierCrossings hn hP S A` through `carrierCrossingEquiv`); "`P_A = P_{D_A}`":
  `carrierPolynomial hn hP S A hS := P (positiveLift hn hP S A hS)` with `P = SM.P` (lp:core's `P_D`).
  "the corresponding `H_A^+`": `cornerHomfly hn hP S A hS = homfly (positiveLift hn hP S A hS)`
  (def:C, SM/CornerStateSum.lean). "`m_A`" (the writhe of `D_A`, def:positive-lift "Its writhe is
  m_Q"; thm:C-S7 "its polynomial P_A = H_A^+ and writhe m_A are those in the state sum"):
  `carrierCrossingCount hn hP S A` (def:smoothing's `m_Q`; `positiveLift_writhe_eq_carrierCrossingCount`).
* "the restricted named cyclic record" of a block `H` (cb:products; mp:blocks' phrase): the record
  of the original traversal of `P` read positively — `positiveRecord hn hP : Record`, one circle,
  occurrences `Visit P`, successor the Gauss successor `nextGaussVisit hn hP` (= `(gaussList hn hP).next`),
  pairing `visitTwin`, over bit `det(d_own, d_twin) > 0` (the positive resolution of def:positive-lift),
  all signs `+1` — restricted to the crossings of `H` by the accepted `Record.restrictCrossings`
  (SM/MarkedProducts.lean:210, "that restricted named cyclic record" of mp:blocks):
  `blockRecord hn hP S H := (positiveRecord hn hP).restrictCrossings (recordCrossings hn hP (blockLabels … H))`.
  Reading R-B1 (PLAN_B §3): "the original record restricted to `H`, with its signs, pairing and
  over/under choices" (proof, 4675–4677) is this record; for the owner `A` of `H` the record of `D_A` is
  (`RecordIso`) `positiveRecord` restricted to `carrierCrossings A` (plan lemma `positiveLift_record_iso`,
  the printed sentence "Successor splitting retains the cyclic order inherited from the original
  traversal. The surviving crossing germs have not changed"), so the restriction to `H` is also
  "`D_A`'s record restricted to `H`" as mp:blocks reads it.
* "an actual positive carrier diagram `D_H`": `positiveLift hn hP T q hT` for some independent support
  `T` and carrier `q` of `T` (the actual positive diagram of a carrier of `P`); "with exactly its
  restricted named cyclic record": `Nonempty (RecordIso (positiveLift hn hP T q hT).record (blockRecord … H))`
  (def:gauss-record's named record isomorphism, SM/LinkRecord.lean:539).
* "Its polynomial `P_H`": `blockPolynomial hn hP S H := recordPolynomial (blockRecord hn hP S H)`, where
  `recordPolynomial ρ` is `P D` for any actual `D` with record `ρ` (`recordPolynomial_eq`, proved below
  from lc:presentations / rp:record-polynomial) — "independent of the further smoothings used to
  produce it" is the field `P_H_independent`.
* eq. cb:product: `product` and `crossing_count`; "With no owned blocks the actual diagram has value 1
  and `m_A = 0`": `no_owned_blocks`.

Checked with `cd work/lean && lake env lean ../drafts/cb/Statements_B.lean`. -/

namespace SM

open SM.Link SM.Carrier Classical

noncomputable section

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-! ## 1. `U(S)`, the residual graph `G_P[U(S)]`, its blocks (cb:blocks, sm-3:4625–4630) -/

section Blocks

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

/-- cb:blocks: "the induced subgraph `G_P[U(S)]`" on `U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`
(`supportUnselected hn hP S`, the accepted def:interlace object). -/
abbrev residualGraph : SimpleGraph (↑(supportUnselected hn hP S) : Set (Crossing P)) :=
  (interlacementGraph hn hP).induce (↑(supportUnselected hn hP S) : Set (Crossing P))

/-- cb:blocks: "The connected components of `G_P[U(S)]` are called its *blocks*." -/
abbrev Block := (residualGraph hn hP S).ConnectedComponent

instance : Fintype (Block hn hP S) := Fintype.ofFinite _

/-- The block of an undominated crossing `c ∈ U(S)`. -/
def blockOf (c : Crossing P) (hc : c ∈ supportUnselected hn hP S) : Block hn hP S :=
  (residualGraph hn hP S).connectedComponentMk ⟨c, hc⟩

/-- The labels (crossings) of a block `H`: the `c ∈ U(S)` whose block is `H`; `|H|` is its card. -/
def blockLabels (H : Block hn hP S) : Finset (Crossing P) :=
  Finset.univ.filter fun c : Crossing P => ∃ hc : c ∈ supportUnselected hn hP S, blockOf hn hP S c hc = H

theorem mem_blockLabels (H : Block hn hP S) (c : Crossing P) :
    c ∈ blockLabels hn hP S H ↔ ∃ hc : c ∈ supportUnselected hn hP S, blockOf hn hP S c hc = H := by
  simp only [blockLabels, Finset.mem_filter, Finset.mem_univ, true_and]

/-- A fixed label of the block `H` (every block is nonempty: it is the class of a vertex). -/
def blockRep (H : Block hn hP S) : Crossing P := (Classical.choose (Quot.exists_rep H)).1

theorem blockRep_mem (H : Block hn hP S) : blockRep hn hP S H ∈ blockLabels hn hP S H := by
  rw [mem_blockLabels]
  exact ⟨(Classical.choose (Quot.exists_rep H)).2, Classical.choose_spec (Quot.exists_rep H)⟩

end Blocks

/-! ## 2. Owners (cb:blocks, sm-3:4631–4633) -/

section Owners

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

omit [NeZero n] in
/-- A fixed visit of a crossing (hypothesis-free; the two visits of `c ∈ U(S)` have the same owner,
`cb_blocks_definition.owner_spec`). -/
def someVisit (c : Crossing P) : Visit P :=
  ⟨c, Classical.choose (crossing_visits_exist c)⟩

/-- cb:blocks: "An undominated crossing has both visits on one carrier by Lemma lem:carriers; that
carrier is its *owner*." The owner of `c` is the carrier of (either) visit of `c`. -/
def crossingOwner (c : Crossing P) : Component hn hP S :=
  owner hn hP S (Sum.inr (someVisit c))

/-- The owner of a block: the owner of any of its labels (cb:products: "Every block `H` has one
owner"); fixed at the label `blockRep H`. -/
def blockOwner (H : Block hn hP S) : Component hn hP S :=
  crossingOwner hn hP S (blockRep hn hP S H)

/-- "the blocks owned by `A`" (eq. cb:product, `∏_{H owned by A}`, `∑_{H owned by A}`). -/
def blocksOwnedBy (A : Component hn hP S) : Finset (Block hn hP S) :=
  Finset.univ.filter fun H : Block hn hP S => blockOwner hn hP S H = A

theorem mem_blocksOwnedBy (A : Component hn hP S) (H : Block hn hP S) :
    H ∈ blocksOwnedBy hn hP S A ↔ blockOwner hn hP S H = A := by
  simp only [blocksOwnedBy, Finset.mem_filter, Finset.mem_univ, true_and]

end Owners

/-! ## 3. `D_A`, `P_A` (cb:blocks, sm-3:4633–4637) -/

section CarrierPolynomial

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

/-- cb:blocks: "Write `D_A` for the actual positive diagram of a carrier `A`, and `P_A = P_{D_A}`":
`D_A = positiveLift hn hP S A hS` (def:positive-lift), `P` = lp:core's evaluation `P_D`. -/
def carrierPolynomial (A : Component hn hP S) (hS : IsDecomposition hn hP S) : R :=
  SM.P (positiveLift hn hP S A hS)

end CarrierPolynomial

/-! ## 4. The named cyclic record of `P` read positively, and the restricted record of a block
(cb:products "its restricted named cyclic record", sm-3:4640–4641; proof 4675–4677 "the complete record
of `D_H` is exactly the original record restricted to `H`, with its signs, pairing and over/under
choices") -/

section PositiveRecord

variable (hn : 3 ≤ n) (hP : Generic P)

/-- The over bit of the positive resolution at the visit `v` (def:positive-lift: the over strand is the
one making the crossing positive, `det(u_o, u_u) > 0`): `v` is over iff `det(d_{v}, d_{twin v}) > 0`. -/
def positiveOverBit (v : Visit P) : Bool :=
  decide (0 < det (edge P v.2.val) (edge P (visitTwin v).2.val))

omit [NeZero n] in
theorem positiveOverBit_twin (hn : 3 ≤ n) (hP : Generic P) (v : Visit P) :
    positiveOverBit (P := P) (visitTwin v) = !positiveOverBit (P := P) v := by
  have hne : det (edge P v.2.val) (edge P (visitTwin v).2.val) ≠ 0 := by
    have hcr : IsCrossing P {v.2.val, (visitTwin v).2.val} := by
      have h := v.1.property
      rwa [visit_crossing_val_eq_pair v] at h
    exact crossing_det_ne_zero_of_geometry (generic_crossingGeometry hn hP) hcr
  unfold positiveOverBit
  rw [visitTwin_involutive, det_swap]
  by_cases h : 0 < det (edge P v.2.val) (edge P (visitTwin v).2.val)
  · simp [h, not_lt.mpr h.le]
  · have hlt : det (edge P v.2.val) (edge P (visitTwin v).2.val) < 0 :=
      lt_of_le_of_ne (not_lt.mp h) hne
    simp [h, hlt]

/-- The Gauss successor of `P` as a permutation of the visits: the cyclic successor in the Gauss list
(`nextGaussVisit hn hP`, `nextGaussVisit_eq_list_next`; Mathlib `List.formPerm`). -/
def gaussSucc : Equiv.Perm (Visit P) := (gaussList hn hP).formPerm

theorem gaussSucc_apply (v : Visit P) : gaussSucc hn hP v = nextGaussVisit hn hP v := by
  rw [nextGaussVisit_eq_list_next]
  exact List.formPerm_apply_mem_eq_next (gaussList_nodup hn hP) v (mem_gaussList hn hP v)

omit [NeZero n] in
/-- The Gauss list is one cycle: any two visits are in the same `gaussSucc`-cycle. -/
theorem gaussSucc_sameCycle (v w : Visit P) : (gaussSucc hn hP).SameCycle v w := by
  by_cases h2 : 2 ≤ (gaussList hn hP).length
  · have hc := List.isCycle_formPerm (gaussList_nodup hn hP) h2
    exact hc.sameCycle
      ((List.formPerm_apply_mem_ne_self_iff _ (gaussList_nodup hn hP) v (mem_gaussList hn hP v)).mpr h2)
      ((List.formPerm_apply_mem_ne_self_iff _ (gaussList_nodup hn hP) w (mem_gaussList hn hP w)).mpr h2)
  · -- at most one visit: `v = w`
    have hvw : v = w := by
      have hv := List.mem_iff_get.mp (mem_gaussList hn hP v)
      have hw := List.mem_iff_get.mp (mem_gaussList hn hP w)
      obtain ⟨i, hi⟩ := hv
      obtain ⟨j, hj⟩ := hw
      have hij : i = j := Fin.ext (by omega)
      rw [← hi, ← hj, hij]
    rw [hvw]

/-- **The named cyclic record of the generic polygon `P`, read positively** (def:gauss-record on the
traversal of `P`; def:positive-lift's positive resolution): one parametrizing circle, occurrence set
`M = Visit P` (the `2m` visits of the traversal circle), forward successor `s` = the Gauss successor,
pairing `τ = visitTwin`, over bit `positiveOverBit`, all crossing signs `+1`. -/
def positiveRecord : Record where
  comps := Unit
  M := Visit P
  comp _ := ()
  succ := gaussSucc hn hP
  pair := visitTwinPerm
  isOver := positiveOverBit
  sgn _ := 1
  succ_comp _ := rfl
  succ_cycle v w _ := gaussSucc_sameCycle hn hP v w
  pair_ne v := visitTwin_ne v
  pair_invol v := visitTwin_involutive v
  bit_pair v := positiveOverBit_twin hn hP v
  sgn_pair _ := rfl
  sgn_ne _ := by decide

@[simp] theorem positiveRecord_M : (positiveRecord hn hP).M = Visit P := rfl
@[simp] theorem positiveRecord_comps : (positiveRecord hn hP).comps = Unit := rfl
theorem positiveRecord_succ (v : Visit P) : (positiveRecord hn hP).succ v = nextGaussVisit hn hP v :=
  gaussSucc_apply hn hP v
theorem positiveRecord_pair (v : Visit P) : (positiveRecord hn hP).pair v = visitTwin v := rfl
theorem positiveRecord_sgn (v : Visit P) : (positiveRecord hn hP).sgn v = 1 := rfl

/-- "one-circle": the record of `P` has one parametrizing circle. -/
theorem positiveRecord_componentCount : (positiveRecord hn hP).componentCount = 1 :=
  Fintype.card_unit

/-- The record crossings ("chords") of a set `T` of crossings of `P`: the chords `{v, τv}` of the
visits of the crossings in `T`. -/
def recordCrossings (T : Finset (Crossing P)) : Set (positiveRecord hn hP).Crossing :=
  {y | ∃ v : Visit P, v.1 ∈ T ∧ y = (positiveRecord hn hP).crossingOf v}

/-- A visit is retained by `recordCrossings T` iff its crossing lies in `T`. -/
theorem crossKeep_recordCrossings_iff (T : Finset (Crossing P)) (v : Visit P) :
    (positiveRecord hn hP).CrossKeep (recordCrossings hn hP T) v ↔ v.1 ∈ T := by
  constructor
  · rintro ⟨w, hw, hvw⟩
    have hv : v ∈ ((positiveRecord hn hP).crossingOf w).1 :=
      ((positiveRecord hn hP).crossingOf_eq_iff v _).mp hvw
    change v ∈ ({w, visitTwin w} : Finset (Visit P)) at hv
    rcases Finset.mem_insert.mp hv with rfl | hv
    · exact hw
    · rw [Finset.mem_singleton.mp hv, visitTwin_crossing]
      exact hw
  · intro hv
    exact ⟨v, hv, rfl⟩

/-- "its restricted named cyclic record" (cb:products; mp:blocks): the record of `P` restricted, by the
accepted `Record.restrictCrossings`, to the crossings of the block `H` — occurrences the visits of the
crossings of `H`, first-return successor (their inherited cyclic order), pairing, bits and signs
unchanged. -/
def blockRecord (S : Finset (Crossing P)) (H : Block hn hP S) : Record :=
  (positiveRecord hn hP).restrictCrossings (recordCrossings hn hP (blockLabels hn hP S H))

theorem blockRecord_componentCount (S : Finset (Crossing P)) (H : Block hn hP S) :
    (blockRecord hn hP S H).componentCount = 1 := by
  rw [blockRecord, Record.componentCount_restrictCrossings, positiveRecord_componentCount]

end PositiveRecord

/-! ## 5. The polynomial of a realizable record; `P_H` (cb:products, sm-3:4641–4643) -/

section RecordPolynomial

/-- The polynomial of a record: `P D` for an actual diagram `D` with that named record (any such `D`
gives the same value, `recordPolynomial_eq`, by lc:presentations / rp:record-polynomial); `0` for a
record no actual diagram has. -/
def recordPolynomial (ρ : Record) : R :=
  if h : IsRealizable ρ then
    SM.P (Classical.choose (show ∃ D : Diagram, Nonempty (RecordIso D.record ρ) from h))
  else 0

theorem recordPolynomial_eq (ρ : Record) (D : Diagram) (h : Nonempty (RecordIso D.record ρ)) :
    recordPolynomial ρ = SM.P D := by
  unfold recordPolynomial
  split_ifs with hr
  · obtain ⟨ι⟩ := Classical.choose_spec (show ∃ D : Diagram, Nonempty (RecordIso D.record ρ) from hr)
    obtain ⟨κ⟩ := h
    exact presentations _ D ⟨ι.trans κ.symm⟩
  · exact absurd ⟨D, h⟩ hr

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

/-- cb:products: "Its polynomial `P_H`" — the polynomial of (any) actual diagram with the restricted
named cyclic record of `H`. -/
def blockPolynomial (H : Block hn hP S) : R := recordPolynomial (blockRecord hn hP S H)

end RecordPolynomial

/-! ## 6. Row 101 — cb:blocks (sm-3:4623–4637), the bundle -/

section BlocksRow

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

/-- cb:blocks as printed, one field per printed clause, on the printed binder (`P` generic, `S` an
independent support). Notation: `U = supportUnselected hn hP S`, `N = supportNeighbors hn hP S`,
`G_P = interlacementGraph hn hP`, `D_A = positiveLift hn hP S A hS`. -/
structure CbBlocksDefinitionData (_hS : IsDecomposition hn hP S) : Prop where
  /-- "For a vertex set `T` write `N_G(T)` for the union of its graph neighbourhoods": a crossing lies
  in `N_{G_P}(S)` iff it is adjacent in `G_P` to some element of `S` -/
  neighbors : ∀ y : Crossing P,
    y ∈ supportNeighbors hn hP S ↔ ∃ x ∈ S, (interlacementGraph hn hP).Adj y x
  /-- eq. cb:undominated: "`U(S) = V(G_P) ∖ (S ∪ N_{G_P}(S))`" (`V(G_P) = X(P) = Finset.univ`) -/
  undominated_eq : supportUnselected hn hP S = Finset.univ \ (S ∪ supportNeighbors hn hP S)
  /-- the same, membership-wise: undominated = neither selected nor adjacent to a selected crossing -/
  undominated_iff : ∀ y : Crossing P,
    y ∈ supportUnselected hn hP S ↔ y ∉ S ∧ ∀ x ∈ S, ¬ (interlacementGraph hn hP).Adj y x
  /-- "the induced subgraph `G_P[U(S)]`": vertex set `U(S)`, adjacency that of `G_P` -/
  induced_adj : ∀ x y : (↑(supportUnselected hn hP S) : Set (Crossing P)),
    (residualGraph hn hP S).Adj x y ↔ (interlacementGraph hn hP).Adj x y
  /-- "The connected components of `G_P[U(S)]` are called its blocks": two undominated crossings lie in
  the same block iff they are joined by a path in `G_P[U(S)]` -/
  same_block_iff : ∀ (x y : Crossing P) (hx : x ∈ supportUnselected hn hP S)
    (hy : y ∈ supportUnselected hn hP S),
    blockOf hn hP S x hx = blockOf hn hP S y hy ↔ (residualGraph hn hP S).Reachable ⟨x, hx⟩ ⟨y, hy⟩
  /-- the labels of a block `H` are the undominated crossings whose block is `H` -/
  block_labels : ∀ (H : Block hn hP S) (c : Crossing P),
    c ∈ blockLabels hn hP S H ↔ ∃ hc : c ∈ supportUnselected hn hP S, blockOf hn hP S c hc = H
  /-- the blocks are nonempty subsets of `U(S)`, pairwise disjoint, covering `U(S)` (the connected
  components partition the vertex set) -/
  blocks_partition :
    (∀ H : Block hn hP S, blockLabels hn hP S H ⊆ supportUnselected hn hP S ∧
      (blockLabels hn hP S H).Nonempty) ∧
    (∀ H H' : Block hn hP S, H ≠ H' → Disjoint (blockLabels hn hP S H) (blockLabels hn hP S H')) ∧
    (Finset.univ : Finset (Block hn hP S)).biUnion (blockLabels hn hP S) = supportUnselected hn hP S
  /-- "An undominated crossing has both visits on one carrier by Lemma lem:carriers" (lem:carriers
  (iii), second half) -/
  both_visits_one_carrier : ∀ c ∈ supportUnselected hn hP S, ∀ v w : Visit P, v.1 = c → w.1 = c →
    owner hn hP S (Sum.inr v) = owner hn hP S (Sum.inr w)
  /-- "that carrier is its owner": the owner of `c ∈ U(S)` is the carrier of each of its visits … -/
  owner_spec : ∀ c ∈ supportUnselected hn hP S, ∀ v : Visit P, v.1 = c →
    owner hn hP S (Sum.inr v) = crossingOwner hn hP S c
  /-- … and it is the only carrier on which both visits lie -/
  owner_unique : ∀ c ∈ supportUnselected hn hP S, ∀ q : Component hn hP S,
    (∀ v : Visit P, v.1 = c → owner hn hP S (Sum.inr v) = q) → q = crossingOwner hn hP S c
  /-- the owner's self-crossings (def:smoothing, "the crossings of `Q`") are exactly the undominated
  crossings it owns (lem:carriers (iii), first sentence: "A carrier's self-intersections are exactly the
  unselected crossings both of whose visits are assigned to it") -/
  owned_iff_carrierCrossing : ∀ (A : Component hn hP S) (c : Crossing P),
    c ∈ carrierCrossings hn hP S A ↔ c ∈ supportUnselected hn hP S ∧ crossingOwner hn hP S c = A
  /-- "Write `D_A` for the actual positive diagram of a carrier `A`": `D_A = positiveLift hn hP S A hS`
  is the one-component diagram whose curve is the carrier (its corner polygon), every crossing of which
  is positive, with writhe `m_A = carrierCrossingCount` (def:positive-lift) -/
  actual_positive_diagram : ∀ A : Component hn hP S,
    (positiveLift hn hP S A _hS).componentCount = 1 ∧
    (∀ i : Fin 1, ((positiveLift hn hP S A _hS).Γ.comp i).P = ccpCornerPolygon hn hP S A) ∧
    (∀ x, (positiveLift hn hP S A _hS).IsPositive x) ∧
    (positiveLift hn hP S A _hS).writhe = carrierCrossingCount hn hP S A
  /-- "and `P_A = P_{D_A}`" -/
  P_A_def : ∀ A : Component hn hP S, carrierPolynomial hn hP S A _hS = SM.P (positiveLift hn hP S A _hS)
  /-- "These polynomials equal the corresponding `H_A^+` by Theorem lp:core": `P_A = H_A^+`, the
  HOMFLY–PT polynomial of the positive lift (def:C's `cornerHomfly`) -/
  P_A_eq_cornerHomfly : ∀ A : Component hn hP S,
    carrierPolynomial hn hP S A _hS = cornerHomfly hn hP S A _hS ∧
    cornerHomfly hn hP S A _hS = homfly (positiveLift hn hP S A _hS)

/-- **Row 101, cb:blocks** (sm-3:4623–4637). -/
theorem cb_blocks_definition (hS : IsDecomposition hn hP S) : CbBlocksDefinitionData hn hP S hS := by
  sorry

end BlocksRow

/-! ## 7. Row 102 — cb:products (sm-3:4638–4651), the bundle -/

section ProductsRow

variable (hn : 3 ≤ n) (hP : Generic P) (S : Finset (Crossing P))

/-- cb:products as printed, one field per printed clause, on the binder of cb:blocks (`P` generic,
`S ∈ Ind(G_P)`); fields marked "(proof)" render sentences of the printed proof that later rows cite
(eq. cb:greedy-step is used by cb:singleton). Notation: `U = supportUnselected hn hP`,
`D_A = positiveLift hn hP S A hS`, `P_A = carrierPolynomial`, `m_A = carrierCrossingCount hn hP S A`,
`|H| = (blockLabels hn hP S H).card`, `P_H = blockPolynomial hn hP S H`, the restricted named cyclic
record of `H` = `blockRecord hn hP S H`. -/
structure CbProductsData (_hS : IsDecomposition hn hP S) : Prop where
  /-- "Every block `H` has one owner": every label of `H` has the owner `blockOwner H` -/
  one_owner : ∀ (H : Block hn hP S), ∀ c ∈ blockLabels hn hP S H,
    crossingOwner hn hP S c = blockOwner hn hP S H
  /-- "and admits an actual positive carrier diagram `D_H` with exactly its restricted named cyclic
  record": the actual positive diagram of some carrier `q` of some independent support `T` of `P` whose
  named record is the record of `P` restricted to `H` -/
  block_diagram : ∀ H : Block hn hP S,
    ∃ (T : Finset (Crossing P)) (hT : IsDecomposition hn hP T) (q : Component hn hP T),
      Nonempty (RecordIso (positiveLift hn hP T q hT).record (blockRecord hn hP S H))
  /-- (proof, 4657–4674) the `D_H` produced by the printed further smoothings: "an independent support
  `S_H ⊇ S` with `U(S_H) = H`"; its carrier owning `H` has self-crossings exactly `H` ("No other
  self-crossing label survives, so its actual positive diagram is a required `D_H`") -/
  block_diagram_support : ∀ H : Block hn hP S,
    ∃ (T : Finset (Crossing P)) (hT : IsDecomposition hn hP T) (q : Component hn hP T),
      S ⊆ T ∧ supportUnselected hn hP T = blockLabels hn hP S H ∧
      carrierCrossings hn hP T q = blockLabels hn hP S H ∧
      Nonempty (RecordIso (positiveLift hn hP T q hT).record (blockRecord hn hP S H))
  /-- (proof, 4658–4660) "choose any label `c ∈ U(S) ∖ H` and adjoin it to the support. It is adjacent
  to no selected label, so the enlarged support is independent" -/
  greedy_independent : ∀ T : Finset (Crossing P), IsDecomposition hn hP T →
    ∀ c ∈ supportUnselected hn hP T, IsDecomposition hn hP (insert c T)
  /-- eq. cb:greedy-step (proof, 4661–4663): "with current support `T`, the new residual set is exactly
  `U(T ∪ {c}) = U(T) ∖ ({c} ∪ N_{G_P}(c))`" (`N_{G_P}(c) = supportNeighbors hn hP {c}`) -/
  greedy_step : ∀ (T : Finset (Crossing P)) (c : Crossing P),
    supportUnselected hn hP (insert c T) =
      supportUnselected hn hP T \ insert c (supportNeighbors hn hP {c})
  /-- "Its polynomial `P_H` is independent of the further smoothings used to produce it": any two
  actual diagrams with the restricted named cyclic record of `H` have the same polynomial
  (rp:record-polynomial) … -/
  P_H_independent : ∀ (H : Block hn hP S) (D D' : Diagram),
    Nonempty (RecordIso D.record (blockRecord hn hP S H)) →
    Nonempty (RecordIso D'.record (blockRecord hn hP S H)) → SM.P D = SM.P D'
  /-- … and `P_H` is that common value -/
  P_H_spec : ∀ (H : Block hn hP S) (D : Diagram),
    Nonempty (RecordIso D.record (blockRecord hn hP S H)) → SM.P D = blockPolynomial hn hP S H
  /-- (proof, 4653–4654) "The self-crossings of a carrier are exactly its owned undominated labels" -/
  self_crossings_eq_owned : ∀ A : Component hn hP S,
    carrierCrossings hn hP S A = (blocksOwnedBy hn hP S A).biUnion (blockLabels hn hP S)
  /-- eq. cb:product, first identity: "For every original carrier `A`, `P_A = ∏_{H owned by A} P_H`" -/
  product : ∀ A : Component hn hP S,
    carrierPolynomial hn hP S A _hS = ∏ H ∈ blocksOwnedBy hn hP S A, blockPolynomial hn hP S H
  /-- eq. cb:product, second identity: "`m_A = ∑_{H owned by A} |H|`" -/
  crossing_count : ∀ A : Component hn hP S,
    carrierCrossingCount hn hP S A = ∑ H ∈ blocksOwnedBy hn hP S A, (blockLabels hn hP S H).card
  /-- "With no owned blocks the actual diagram has value `1` and `m_A = 0`" (the actual diagram `D_A` is
  then a crossing-free one-circle diagram) -/
  no_owned_blocks : ∀ A : Component hn hP S, blocksOwnedBy hn hP S A = ∅ →
    carrierPolynomial hn hP S A _hS = 1 ∧ carrierCrossingCount hn hP S A = 0 ∧
    (positiveLift hn hP S A _hS).IsCrossingFreeCircle

/-- **Row 102, cb:products** (sm-3:4638–4651). -/
theorem cb_products (hS : IsDecomposition hn hP S) : CbProductsData hn hP S hS := by
  sorry

end ProductsRow

end

end SM
