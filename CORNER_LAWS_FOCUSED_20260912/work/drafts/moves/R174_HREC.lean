import SM.Smoothing
import SM.MarkedProducts
import SM.SingleCrossing
import CV.FullTwist
import RProof.GenericTransport
import RProof.RALedgers

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


/-! ## 1c. The construction API of Wave 1 (unit U-M0) and the sub-leaves of units U-M1 … U-M7

Everything in this section is NEW relative to `Statements_FINAL.lean`; nothing above it changed.
Conventions of the construction (PLAN_FINAL §5, DESIGN_B §3.3):
* `M_m := P (a + m)` for `0 ≤ m ≤ j + 1`; `e_in = ⟨i, a⟩ = [M₀, M₁]`, `e_out = ⟨i, a + j⟩ = [M_j, M_{j+1}]`;
  a strand is *foreign* when it is neither `s` nor one of `⟨i, a + m⟩`, `0 ≤ m ≤ j`.
* U-M1 produces a `Cut`: the disc `U ⊇ K`, the entry parameter `t_p` of `e_in`, the parameter `t_M` of the
  new vertex `M' = edgePt e_in t_M ∈ (p, y)`, the exit parameter `t_q` of `e_out` (`q = edgePt e_out t_q`),
  the two parameters `t_in < t_out` of `s ∩ U`, and the membership laws of the three local edges.
* The reduced component has `k' = k − j + 2` vertices, labelled with the rotation `M₀ = 0`:
  `Q 0 = M₀`, `Q 1 = M'`, `Q 2 = q`, `Q n = M_{j + n − 2}` for `3 ≤ n < k'` (so `Q 3 = M_{j+1}` and
  `Q (k' − 1) = P (a − 1)`).  Its strands have the four kinds `cutIn = [M₀, M']` (label `0`, a prefix of
  `e_in`), `mid = [M', q]` (label `1`), `cutOut = [q, M_{j+1}]` (label `2`, a suffix of `e_out`) and
  `old e` (labels `≥ 3`; on the other components every strand is `old`).  `orig` sends a kind to the
  strand of `D` it is a piece of (`mid ↦ e_in` by convention; never used for `mid`).
* Statement conventions: `RIIData U D' D` has the REDUCED diagram `D'` as its crossing-free side (its arcs
  `a, b`) and the original `D` as the side with the two crossings `y, z` (its arcs `a', b'`).
* Sub-leaves are named `m<unit>_…`; each is exactly what U-M7's assembly `m7_riiData` /
  `exists_rii_deletion` consumes.  `exists_rii_deletion` is PROVED below from `m1_exists_cut`,
  `m7_riiData` and `m6_recordIso`. -/

namespace BigonData

variable {D : Diagram} (B : BigonData D)

/-! ### 1c.0 Site vocabulary and the facts about the site that need no construction -/

/-- the vertex count `k` of the run component -/
abbrev k : ℕ := (D.Γ.comp B.i).k

/-- the vertex count of the reduced component, `k' = k − j + 2` -/
abbrev k' : ℕ := B.k - B.j + 2

/-- `M_m = P (a + m)`: `M₀` the tail of the entering edge, `M₁ … M_j` the run, `M_{j+1}` the head of the
exiting edge -/
def M (m : ℕ) : Plane := (D.Γ.comp B.i).P (B.a + (m : ZMod B.k))

/-- the strand `⟨i, a + m⟩`: `m = 0` the entering edge, `1 ≤ m < j` the run edges, `m = j` the exiting edge -/
def strand (m : ℕ) : D.Γ.Strand := ⟨B.i, B.a + (m : ZMod B.k)⟩

/-- the entering edge `e_in = ⟨i, a⟩` -/
abbrev eIn : D.Γ.Strand := ⟨B.i, B.a⟩

/-- the exiting edge `e_out = ⟨i, a + j⟩` -/
abbrev eOut : D.Γ.Strand := ⟨B.i, B.a + (B.j : ZMod B.k)⟩

/-- a strand is *foreign* when it is neither the remote strand nor one of the `j + 1` local strands
`⟨i, a + m⟩`, `0 ≤ m ≤ j` -/
def Foreign (u : D.Γ.Strand) : Prop := u ≠ B.s ∧ ∀ m : ℕ, m ≤ B.j → u ≠ B.strand m

theorem three_le_k : 3 ≤ B.k := (D.Γ.comp B.i).hk

theorem j_add_three_le_k : B.j + 3 ≤ B.k := B.hk

/-- `hk` read on `B.k` (for `omega`) -/
theorem hk' : B.j + 3 ≤ B.k := B.hk

theorem five_le_k' : 5 ≤ B.k' := by
  have := B.hk'; unfold k'; omega

theorem three_le_k' : 3 ≤ B.k' := by have := B.five_le_k'; omega

theorem k'_add_j : B.k' + B.j = B.k + 2 := by have := B.hk'; unfold k'; omega

theorem strand_zero : B.strand 0 = B.eIn := by simp [strand]

theorem strand_j : B.strand B.j = B.eOut := rfl

theorem M_zero : B.M 0 = D.Γ.tail B.eIn := by simp [M, Shadow.tail]

theorem M_succ_j : B.M (B.j + 1) = D.Γ.head B.eOut := by
  unfold Shadow.head M; rw [Nat.cast_succ, add_assoc]

theorem tail_strand (m : ℕ) : D.Γ.tail (B.strand m) = B.M m := rfl

theorem head_strand (m : ℕ) : D.Γ.head (B.strand m) = B.M (m + 1) := by
  unfold Shadow.head strand M; rw [Nat.cast_succ, add_assoc]

/-- the strands `⟨i, a + m⟩`, `⟨i, a + m'⟩` with `m, m' < k` are distinct for distinct `m, m'` -/
theorem strand_inj {m m' : ℕ} (hm : m < B.k) (hm' : m' < B.k) (h : B.strand m = B.strand m') : m = m' := by
  unfold strand at h
  rw [Sigma.mk.inj_iff] at h
  have h2 := eq_of_heq h.2
  have h3 : (m : ZMod B.k) = m' := add_left_cancel h2
  exact Smoothing.nat_eq_of_zcast_eq hm hm' h3

/-- `Foreign` is exactly the hypothesis list of `clear` -/
theorem foreign_iff (u : D.Γ.Strand) : B.Foreign u ↔
    u ≠ B.eIn ∧ u ≠ B.eOut ∧ u ≠ B.s ∧ ∀ m : ℕ, 1 ≤ m → m < B.j → u ≠ B.strand m := by
  constructor
  · rintro ⟨hs, hm⟩
    refine ⟨?_, hm B.j le_rfl, hs, fun m _ hm' => hm m hm'.le⟩
    rw [← B.strand_zero]; exact hm 0 (Nat.zero_le _)
  · rintro ⟨h0, hj, hs, hm⟩
    refine ⟨hs, fun m hmj => ?_⟩
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rwa [strand_zero]
    · rcases hmj.lt_or_eq with hlt | rfl
      · exact hm m hpos hlt
      · exact hj

/-- `clear` in the `Foreign` vocabulary -/
theorem clear_of_foreign {u : D.Γ.Strand} (hu : B.Foreign u) : Disjoint (D.Γ.seg u) B.K := by
  obtain ⟨h0, hj, hs, hm⟩ := (B.foreign_iff u).mp hu
  exact B.clear u h0 hj hs hm

/-- the entering and exiting edges are distinct (`a ≠ a + j` for `1 ≤ j < k`) -/
theorem eIn_ne_eOut : B.eIn ≠ B.eOut := by
  intro h
  have := B.strand_inj (by have := B.hk'; omega) (by have := B.hk'; omega) (B.strand_zero.trans (h.trans B.strand_j.symm))
  have := B.hj; omega

theorem s_ne_eIn : B.s ≠ B.eIn := by
  intro h
  obtain ⟨u, v, huv, hna, -⟩ := B.y.2
  have : ({B.eIn, B.s} : Finset D.Γ.Strand) = {u, v} := B.hy.symm.trans huv
  rw [h, Finset.pair_eq_singleton] at this
  have hcard := congrArg Finset.card this
  rw [Finset.card_singleton, Finset.card_pair (D.Γ.ne_of_not_adjacent hna)] at hcard
  omega

theorem s_ne_eOut : B.s ≠ B.eOut := by
  intro h
  obtain ⟨u, v, huv, hna, -⟩ := B.z.2
  have : ({B.eOut, B.s} : Finset D.Γ.Strand) = {u, v} := B.hz.symm.trans huv
  rw [h, Finset.pair_eq_singleton] at this
  have hcard := congrArg Finset.card this
  rw [Finset.card_singleton, Finset.card_pair (D.Γ.ne_of_not_adjacent hna)] at hcard
  omega

/-- the two crossings of the bigon are distinct -/
theorem y_ne_z : B.y ≠ B.z := by
  intro h
  have h1 : ({B.eIn, B.s} : Finset D.Γ.Strand) = {B.eOut, B.s} := B.hy.symm.trans (h ▸ B.hz)
  have h2 : B.eIn ∈ ({B.eOut, B.s} : Finset D.Γ.Strand) := h1 ▸ Finset.mem_insert_self _ _
  rcases Finset.mem_insert.mp h2 with h3 | h3
  · exact B.eIn_ne_eOut h3
  · exact B.s_ne_eIn (Finset.mem_singleton.mp h3).symm

theorem eIn_mem_y : B.eIn ∈ B.y.val := by rw [B.hy]; exact Finset.mem_insert_self _ _
theorem s_mem_y : B.s ∈ B.y.val := by rw [B.hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
theorem eOut_mem_z : B.eOut ∈ B.z.val := by rw [B.hz]; exact Finset.mem_insert_self _ _
theorem s_mem_z : B.s ∈ B.z.val := by rw [B.hz]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

/-- a parameter placing an edge point at a crossing point of one of its two strands is strictly inside `(0,1)` -/
theorem param_of_edgePt_eq {x : D.Γ.Crossing} {e : D.Γ.Strand} (he : e ∈ x.val) {t : ℝ}
    (ht : D.Γ.edgePt e t = D.Γ.crossingPoint x) : 0 < t ∧ t < 1 := by
  obtain ⟨t', h0, h1, ht'⟩ := D.Γ.crossingPoint_mem x he
  have : t = t' := D.generic.edgePt_injective e (ht.trans ht')
  subst this
  exact D.generic.crossingPoint_param x he ht' h0 h1

theorem ty_pos : 0 < B.ty := (param_of_edgePt_eq B.eIn_mem_y B.hty).1
theorem ty_lt_one : B.ty < 1 := (param_of_edgePt_eq B.eIn_mem_y B.hty).2
theorem tz_pos : 0 < B.tz := (param_of_edgePt_eq B.eOut_mem_z B.htz).1
theorem tz_lt_one : B.tz < 1 := (param_of_edgePt_eq B.eOut_mem_z B.htz).2
theorem tsy_pos : 0 < B.tsy := (param_of_edgePt_eq B.s_mem_y B.htsy).1
theorem tsy_lt_one : B.tsy < 1 := (param_of_edgePt_eq B.s_mem_y B.htsy).2
theorem tsz_pos : 0 < B.tsz := (param_of_edgePt_eq B.s_mem_z B.htsz).1
theorem tsz_lt_one : B.tsz < 1 := (param_of_edgePt_eq B.s_mem_z B.htsz).2

/-- `M₀ ∉ K` (`in_iff` at `t = 0`) -/
theorem M_zero_not_mem_K : B.M 0 ∉ B.K := by
  rw [B.M_zero, ← D.Γ.edgePt_zero]
  intro h
  exact absurd ((B.in_iff 0 le_rfl zero_le_one).mp h) (not_le.mpr B.ty_pos)

/-- `M_{j+1} ∉ K` (`out_iff` at `t = 1`) -/
theorem M_succ_j_not_mem_K : B.M (B.j + 1) ∉ B.K := by
  rw [B.M_succ_j, ← D.Γ.edgePt_one]
  intro h
  exact absurd ((B.out_iff 1 zero_le_one le_rfl).mp h) (not_le.mpr B.tz_lt_one)

/-- the vertex–edge case: the entering and exiting edges are consecutive, so no crossing contains both
(the `no_io` field of a `j = 1` site, for U-M7's `exists_bigonData_of_triangle`) -/
theorem no_io_of_succ (i : Fin D.Γ.c) (a : ZMod (D.Γ.comp i).k) (x : D.Γ.Crossing) :
    ¬ ((⟨i, a⟩ : D.Γ.Strand) ∈ x.val ∧ (⟨i, a + 1⟩ : D.Γ.Strand) ∈ x.val) := by
  rintro ⟨h1, h2⟩
  have hne : (⟨i, a + 1⟩ : D.Γ.Strand) ≠ ⟨i, a⟩ := D.Γ.mk_add_one_ne ⟨i, a⟩
  have hother := D.Γ.eq_other_of_mem_of_ne x h1 h2 hne
  have hna := D.Γ.not_adjacent_other x h1
  rw [← hother] at hna
  exact hna (D.Γ.adjacent_mk_add_one ⟨i, a⟩)

/-! ### 1c.1 The cut (the output of unit U-M1) -/

/-- **The cut data of a bigon site** (U-M1's deliverable).  A disc `U` around `K`, the entry parameter
`t_p` of the entering edge, the parameter `t_M` of the new vertex `M' = edgePt e_in t_M ∈ (p, y)`, the exit
parameter `t_q` of the exiting edge (`q = edgePt e_out t_q`), the two parameters of `s ∩ U`, the exact
membership laws of the three local edges in `U` and in `interior U`, the clearance of every foreign edge from
`U`, and the two transversality facts of the new vertices (`q ∉ line(e_in)`, `M' ∉ line(e_out)`) together with
the side law of the new middle edge `[M', q]` (it misses `line(s)`).  Construction (DESIGN_B §3.3):
`ρ₀ := infDist`-gap between `K` and the compact set `⋃ foreign seg ∪ {M₀, M_{j+1}, tail s, head s}`,
`U := Metric.cthickening (ρ₀/2) K`. -/
structure Cut where
  U : Set Plane
  disc : IsDisc U
  K_sub : B.K ⊆ interior U
  tp : ℝ
  tM : ℝ
  tq : ℝ
  tin : ℝ
  tout : ℝ
  tp_pos : 0 < tp
  tp_lt_tM : tp < tM
  tM_lt_ty : tM < B.ty
  tz_lt_tq : B.tz < tq
  tq_lt_one : tq < 1
  tin_pos : 0 < tin
  tin_lt : tin < min B.tsy B.tsz
  lt_tout : max B.tsy B.tsz < tout
  tout_lt_one : tout < 1
  /-- `e_in ∩ U = [p, M₁]` -/
  in_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.eIn t ∈ U ↔ tp ≤ t)
  /-- `e_in ∩ interior U = (p, M₁]` -/
  in_int_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.eIn t ∈ interior U ↔ tp < t)
  /-- `e_out ∩ U = [M_j, q]` -/
  out_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.eOut t ∈ U ↔ t ≤ tq)
  /-- `e_out ∩ interior U = [M_j, q)` -/
  out_int_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.eOut t ∈ interior U ↔ t < tq)
  /-- `s ∩ U = [b_in, b_out]` -/
  s_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.s t ∈ U ↔ tin ≤ t ∧ t ≤ tout)
  /-- `s ∩ interior U = (b_in, b_out)` -/
  s_int_iff : ∀ t : ℝ, 0 ≤ t → t ≤ 1 → (D.Γ.edgePt B.s t ∈ interior U ↔ tin < t ∧ t < tout)
  /-- every foreign edge is clear of the closed disc -/
  clear : ∀ u : D.Γ.Strand, B.Foreign u → Disjoint (D.Γ.seg u) U
  /-- `q ∉ line(e_in)` -/
  q_off_in : det (D.Γ.dir B.eIn) (D.Γ.edgePt B.eOut tq - D.Γ.edgePt B.eIn tM) ≠ 0
  /-- `M' ∉ line(e_out)` -/
  mid_off_out : det (D.Γ.edgePt B.eOut tq - D.Γ.edgePt B.eIn tM) (D.Γ.dir B.eOut) ≠ 0
  /-- the middle edge `[M', q]` misses the line of `s` (both ends strictly on the `M₀`-side) -/
  mid_side : ∀ θ : ℝ, 0 ≤ θ → θ ≤ 1 →
    det (D.Γ.dir B.s) (D.Γ.edgePt B.eIn tM + θ • (D.Γ.edgePt B.eOut tq - D.Γ.edgePt B.eIn tM) - D.Γ.tail B.s) ≠ 0

namespace Cut

variable {B} (C : B.Cut)

/-- the entry point `p` of the entering edge into `U` -/
def p : Plane := D.Γ.edgePt B.eIn C.tp
/-- the new vertex `M' ∈ (p, y)` -/
def M' : Plane := D.Γ.edgePt B.eIn C.tM
/-- the exit point `q` of the exiting edge from `U` -/
def q : Plane := D.Γ.edgePt B.eOut C.tq
/-- the entry point of `s` into `U` -/
def sIn : Plane := D.Γ.edgePt B.s C.tin
/-- the exit point of `s` from `U` -/
def sOut : Plane := D.Γ.edgePt B.s C.tout

theorem tM_pos : 0 < C.tM := C.tp_pos.trans C.tp_lt_tM
theorem tM_lt_one : C.tM < 1 := C.tM_lt_ty.trans B.ty_lt_one
theorem tp_lt_one : C.tp < 1 := C.tp_lt_tM.trans C.tM_lt_one
theorem tq_pos : 0 < C.tq := B.tz_pos.trans C.tz_lt_tq
theorem tin_lt_tout : C.tin < C.tout :=
  C.tin_lt.trans ((min_le_max).trans_lt C.lt_tout)
theorem tin_lt_tsy : C.tin < B.tsy := C.tin_lt.trans_le (min_le_left _ _)
theorem tin_lt_tsz : C.tin < B.tsz := C.tin_lt.trans_le (min_le_right _ _)
theorem tsy_lt_tout : B.tsy < C.tout := (le_max_left _ _).trans_lt C.lt_tout
theorem tsz_lt_tout : B.tsz < C.tout := (le_max_right _ _).trans_lt C.lt_tout

theorem isClosed_U : IsClosed C.U := C.disc.isCompact.isClosed

theorem mem_frontier_iff (x : Plane) : x ∈ frontier C.U ↔ x ∈ C.U ∧ x ∉ interior C.U := by
  rw [C.isClosed_U.frontier_eq]; rfl

theorem p_mem : C.p ∈ C.U := (C.in_iff _ C.tp_pos.le C.tp_lt_one.le).mpr le_rfl
theorem p_not_mem_interior : C.p ∉ interior C.U := fun h =>
  lt_irrefl _ ((C.in_int_iff _ C.tp_pos.le C.tp_lt_one.le).mp h)
theorem p_frontier : C.p ∈ frontier C.U := (C.mem_frontier_iff _).mpr ⟨C.p_mem, C.p_not_mem_interior⟩

theorem q_mem : C.q ∈ C.U := (C.out_iff _ C.tq_pos.le C.tq_lt_one.le).mpr le_rfl
theorem q_not_mem_interior : C.q ∉ interior C.U := fun h =>
  lt_irrefl _ ((C.out_int_iff _ C.tq_pos.le C.tq_lt_one.le).mp h)
theorem q_frontier : C.q ∈ frontier C.U := (C.mem_frontier_iff _).mpr ⟨C.q_mem, C.q_not_mem_interior⟩

theorem sIn_mem : C.sIn ∈ C.U :=
  (C.s_iff _ C.tin_pos.le (C.tin_lt_tout.trans C.tout_lt_one).le).mpr ⟨le_rfl, C.tin_lt_tout.le⟩
theorem sIn_not_mem_interior : C.sIn ∉ interior C.U := fun h =>
  lt_irrefl _ ((C.s_int_iff _ C.tin_pos.le (C.tin_lt_tout.trans C.tout_lt_one).le).mp h).1
theorem sIn_frontier : C.sIn ∈ frontier C.U :=
  (C.mem_frontier_iff _).mpr ⟨C.sIn_mem, C.sIn_not_mem_interior⟩

theorem sOut_mem : C.sOut ∈ C.U :=
  (C.s_iff _ (C.tin_pos.trans C.tin_lt_tout).le C.tout_lt_one.le).mpr ⟨C.tin_lt_tout.le, le_rfl⟩
theorem sOut_not_mem_interior : C.sOut ∉ interior C.U := fun h =>
  lt_irrefl _ ((C.s_int_iff _ (C.tin_pos.trans C.tin_lt_tout).le C.tout_lt_one.le).mp h).2
theorem sOut_frontier : C.sOut ∈ frontier C.U :=
  (C.mem_frontier_iff _).mpr ⟨C.sOut_mem, C.sOut_not_mem_interior⟩

/-- `M' ∈ interior U` -/
theorem M'_mem_interior : C.M' ∈ interior C.U :=
  (C.in_int_iff _ C.tM_pos.le C.tM_lt_one.le).mpr C.tp_lt_tM

theorem M_zero_not_mem : B.M 0 ∉ C.U := by
  rw [B.M_zero, ← D.Γ.edgePt_zero]
  intro h
  exact absurd ((C.in_iff 0 le_rfl zero_le_one).mp h) (not_le.mpr C.tp_pos)

theorem M_succ_j_not_mem : B.M (B.j + 1) ∉ C.U := by
  rw [B.M_succ_j, ← D.Γ.edgePt_one]
  intro h
  exact absurd ((C.out_iff 1 zero_le_one le_rfl).mp h) (not_le.mpr C.tq_lt_one)

theorem tail_s_not_mem : D.Γ.tail B.s ∉ C.U := by
  rw [← D.Γ.edgePt_zero]
  intro h
  exact absurd ((C.s_iff 0 le_rfl zero_le_one).mp h).1 (not_le.mpr C.tin_pos)

theorem head_s_not_mem : D.Γ.head B.s ∉ C.U := by
  rw [← D.Γ.edgePt_one]
  intro h
  exact absurd ((C.s_iff 1 zero_le_one le_rfl).mp h).2 (not_le.mpr C.tout_lt_one)

/-- the run vertices lie in `interior U` -/
theorem run_mem_interior (m : ℕ) (h1 : 1 ≤ m) (hj : m ≤ B.j) : B.M m ∈ interior C.U :=
  C.K_sub (B.run_mem m h1 hj)

end Cut

/-- **Sub-leaf (U-M1).**  The gap construction: `ρ₀ := infDist`, `U := Metric.cthickening (ρ₀/2) K`
(`Convex.cthickening`, `IsCompact.cthickening`), `K ⊆ interior U`, entry/exit parameters as `sInf`/`sSup` of the
closed parameter sets, the interior laws by `Convex.openSegment_closure_interior_subset_interior`, the choice of
`t_M ∈ (t_p, t_y)` off `line(e_out)` (a line meets `(p, y)` in at most one point unless it contains `e_in`, which
would force `y = z`), `q ∉ line(e_in)` and the side law of `[M', q]` from the side lemma (the run lies strictly on
one side of `line(s)`, `M₀`, `M_{j+1}`, `p`, `M'`, `q` strictly on the other). -/
theorem m1_exists_cut : Nonempty B.Cut := by
  sorry

/-! ### 1c.2 Strand kinds -/

/-- The four kinds of strands of the reduced shadow. -/
inductive Kind (_B : BigonData D)
  | old (e : D.Γ.Strand)
  | cutIn
  | mid
  | cutOut
  deriving DecidableEq

namespace Kind

variable {B}

/-- the strand of `D` a kind is a piece of (`mid ↦ e_in` by convention) -/
def orig : B.Kind → D.Γ.Strand
  | old e => e
  | cutIn => B.eIn
  | mid => B.eIn
  | cutOut => B.eOut

/-- tail vertex of a kind, for the new vertices `M' = edgePt e_in t_M`, `q = edgePt e_out t_q` -/
def tail (tM tq : ℝ) : B.Kind → Plane
  | old e => D.Γ.tail e
  | cutIn => D.Γ.tail B.eIn
  | mid => D.Γ.edgePt B.eIn tM
  | cutOut => D.Γ.edgePt B.eOut tq

/-- direction of a kind -/
def dir (tM tq : ℝ) : B.Kind → Plane
  | old e => D.Γ.dir e
  | cutIn => tM • D.Γ.dir B.eIn
  | mid => D.Γ.edgePt B.eOut tq - D.Γ.edgePt B.eIn tM
  | cutOut => (1 - tq) • D.Γ.dir B.eOut

/-- head vertex of a kind -/
def head (tM tq : ℝ) (κ : B.Kind) : Plane := κ.tail tM tq + κ.dir tM tq

/-- closed segment of a kind -/
def seg (tM tq : ℝ) (κ : B.Kind) : Set Plane :=
  {q | ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ q = κ.tail tM tq + θ • κ.dir tM tq}

/-- open segment of a kind -/
def interior (tM tq : ℝ) (κ : B.Kind) : Set Plane :=
  {q | ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q = κ.tail tM tq + θ • κ.dir tM tq}

/-- the kind of the strand preceding a strand of the given kind on its component -/
def pred : B.Kind → B.Kind
  | old e => if e = B.strand (B.j + 1) then cutOut else old ⟨e.1, e.2 - 1⟩
  | cutIn => old ⟨B.i, B.a - 1⟩
  | mid => cutIn
  | cutOut => mid

/-- the kind of the strand following a strand of the given kind on its component -/
def succ : B.Kind → B.Kind
  | old e => if e = ⟨B.i, B.a - 1⟩ then cutIn else old ⟨e.1, e.2 + 1⟩
  | cutIn => mid
  | mid => cutOut
  | cutOut => old (B.strand (B.j + 1))

/-- the kinds that occur in the reduced shadow: everything but the `j + 1` deleted local strands -/
def Occurs (κ : B.Kind) : Prop := ∀ m : ℕ, m ≤ B.j → κ ≠ old (B.strand m)

/-- the parameter on the original strand of the point at parameter `θ` of a kind (identity on old
strands, affine rescaling on the two cut pieces; junk on `mid`) -/
def origParam (tM tq : ℝ) : B.Kind → ℝ → ℝ
  | old _ => fun θ => θ
  | cutIn => fun θ => θ * tM
  | mid => fun θ => θ
  | cutOut => fun θ => tq + θ * (1 - tq)

/-- the inverse rescaling: the parameter on the cut piece of the point at parameter `θ` of the original
strand -/
def liftParam (tM tq : ℝ) : B.Kind → ℝ → ℝ
  | old _ => fun θ => θ
  | cutIn => fun θ => θ / tM
  | mid => fun θ => θ
  | cutOut => fun θ => (θ - tq) / (1 - tq)

theorem occurs_cutIn : (cutIn : B.Kind).Occurs := fun _ _ h => nomatch h
theorem occurs_mid : (mid : B.Kind).Occurs := fun _ _ h => nomatch h
theorem occurs_cutOut : (cutOut : B.Kind).Occurs := fun _ _ h => nomatch h
theorem occurs_old {e : D.Γ.Strand} (h : ∀ m : ℕ, m ≤ B.j → e ≠ B.strand m) : (old e : B.Kind).Occurs :=
  fun m hm heq => h m hm (Kind.old.inj heq)
theorem occurs_old_of_fst_ne {e : D.Γ.Strand} (h : e.1 ≠ B.i) : (old e : B.Kind).Occurs :=
  occurs_old fun _ _ heq => h (congrArg Sigma.fst heq)

theorem not_occurs_old_eIn : ¬ (old B.eIn : B.Kind).Occurs := fun h =>
  h 0 (Nat.zero_le _) (by rw [B.strand_zero])
theorem not_occurs_old_eOut : ¬ (old B.eOut : B.Kind).Occurs := fun h => h B.j le_rfl rfl

theorem liftParam_origParam (tM tq : ℝ) (hM : tM ≠ 0) (hq : tq ≠ 1) (κ : B.Kind) (θ : ℝ) :
    κ.liftParam tM tq (κ.origParam tM tq θ) = θ := by
  have hq' : 1 - tq ≠ 0 := sub_ne_zero.mpr hq.symm
  cases κ <;> simp [liftParam, origParam] <;> field_simp

theorem origParam_liftParam (tM tq : ℝ) (hM : tM ≠ 0) (hq : tq ≠ 1) (κ : B.Kind) (θ : ℝ) :
    κ.origParam tM tq (κ.liftParam tM tq θ) = θ := by
  have hq' : 1 - tq ≠ 0 := sub_ne_zero.mpr hq.symm
  cases κ <;> simp [liftParam, origParam] <;> field_simp <;> ring

/-- a non-middle kind is a positively rescaled piece of its original strand -/
theorem dir_eq_smul_orig (tM tq : ℝ) (hM : 0 < tM) (hq : tq < 1) (κ : B.Kind) (hκ : κ ≠ mid) :
    ∃ l : ℝ, 0 < l ∧ κ.dir tM tq = l • D.Γ.dir κ.orig := by
  cases κ with
  | old e => exact ⟨1, one_pos, (one_smul _ _).symm⟩
  | cutIn => exact ⟨tM, hM, rfl⟩
  | mid => exact absurd rfl hκ
  | cutOut => exact ⟨1 - tq, sub_pos.mpr hq, rfl⟩

/-- the points of a non-middle kind are the points of its original strand at the rescaled parameter -/
theorem tail_add_smul_dir (tM tq : ℝ) (κ : B.Kind) (hκ : κ ≠ mid) (θ : ℝ) :
    κ.tail tM tq + θ • κ.dir tM tq = D.Γ.edgePt κ.orig (κ.origParam tM tq θ) := by
  cases κ with
  | old e => simp [tail, dir, orig, origParam, Shadow.edgePt_eq]
  | cutIn => simp [tail, dir, orig, origParam, Shadow.edgePt_eq, smul_smul]
  | mid => exact absurd rfl hκ
  | cutOut =>
    simp only [tail, dir, orig, origParam, Shadow.edgePt_eq, smul_smul, add_assoc, ← add_smul]

theorem seg_old (tM tq : ℝ) (e : D.Γ.Strand) : (old e : B.Kind).seg tM tq = D.Γ.seg e := by
  ext q; simp [seg, tail, dir, Shadow.seg, edgeSegment, edgePoint, Shadow.tail, Shadow.dir]

theorem interior_old (tM tq : ℝ) (e : D.Γ.Strand) : (old e : B.Kind).interior tM tq = D.Γ.interior e := by
  ext q; simp [interior, tail, dir, Shadow.interior, edgeInterior, edgePoint, Shadow.tail, Shadow.dir]

/-- the head of a kind is the tail of its successor (occurring kinds) -/
theorem head_eq_tail_succ (tM tq : ℝ) (κ : B.Kind) (hκ : κ.Occurs) : κ.head tM tq = κ.succ.tail tM tq := by
  cases κ with
  | old e =>
    simp only [head, tail, dir, succ]
    rw [← D.Γ.head_eq_tail_add_dir e]
    split_ifs with h
    · subst h
      simp [Shadow.head, Shadow.tail]
    · exact D.Γ.head_eq_tail_mk_add_one e
  | cutIn => simp [head, tail, dir, succ, Shadow.edgePt_eq]
  | mid => simp [head, tail, dir, succ]
  | cutOut =>
    simp only [head, tail, dir, succ, Shadow.edgePt_eq, tail_strand, M_succ_j, Shadow.head_eq_tail_add_dir]
    module

theorem succ_pred (κ : B.Kind) (hκ : κ.Occurs) : κ.pred.succ = κ := by
  cases κ with
  | old e =>
    simp only [pred]
    split_ifs with h
    · rw [h]; rfl
    · simp only [succ]
      split_ifs with h'
      · exfalso
        apply not_occurs_old_eIn (B := B)
        have : e = B.eIn := by
          have h2 := congrArg (fun u : D.Γ.Strand => (⟨u.1, u.2 + 1⟩ : D.Γ.Strand)) h'
          simpa using h2
        rw [← this]; exact hκ
      · simp
  | cutIn => simp [pred, succ]
  | mid => rfl
  | cutOut => rfl

theorem pred_succ (κ : B.Kind) (hκ : κ.Occurs) : κ.succ.pred = κ := by
  cases κ with
  | old e =>
    obtain ⟨i', b⟩ := e
    simp only [succ]
    split_ifs with h
    · rw [h]; rfl
    · simp only [pred]
      split_ifs with h'
      · exfalso
        apply not_occurs_old_eOut (B := B)
        have : (⟨i', b⟩ : D.Γ.Strand) = B.eOut := by
          unfold strand at h'
          rw [Sigma.mk.inj_iff] at h'
          obtain ⟨rfl, hb⟩ := h'
          have hb' := eq_of_heq hb
          rw [Sigma.mk.inj_iff]
          exact ⟨rfl, heq_of_eq (by rw [eq_sub_of_add_eq hb']; push_cast; ring)⟩
        rw [← this]; exact hκ
      · simp
  | cutIn => rfl
  | mid => rfl
  | cutOut => simp [pred, succ]

end Kind

/-! ### 1c.3 The reduced tuple, component and shadow -/

/-- **The reduced vertex tuple** (`k' = k − j + 2` vertices, rotation `M₀ = 0`): `Q 0 = M₀`, `Q 1 = M'`,
`Q 2 = q`, `Q n = M_{j+n−2}` for `3 ≤ n < k'`. -/
def reducedTuple (tM tq : ℝ) : LabelledTuple B.k' := fun n =>
  if n.val = 0 then B.M 0
  else if n.val = 1 then D.Γ.edgePt B.eIn tM
  else if n.val = 2 then D.Γ.edgePt B.eOut tq
  else B.M (B.j + n.val - 2)

/-- the reduced component -/
def reducedComp (tM tq : ℝ) : PolyComp := ⟨B.k', B.three_le_k', B.reducedTuple tM tq⟩

/-- **The reduced shadow**: `D.Γ` with component `i` replaced by the reduced component; same component
count, other components untouched. -/
def reducedShadow (tM tq : ℝ) : Shadow :=
  ⟨D.Γ.c, D.Γ.hc, Function.update D.Γ.comp B.i (B.reducedComp tM tq)⟩

section Reduced

variable (tM tq : ℝ)

@[simp] theorem reducedShadow_c : (B.reducedShadow tM tq).c = D.Γ.c := rfl

theorem reducedShadow_comp_self : (B.reducedShadow tM tq).comp B.i = B.reducedComp tM tq :=
  Function.update_self _ _ _

theorem reducedShadow_comp_of_ne {i' : Fin D.Γ.c} (h : i' ≠ B.i) :
    (B.reducedShadow tM tq).comp i' = D.Γ.comp i' :=
  Function.update_of_ne h _ _

theorem reducedShadow_k_self : ((B.reducedShadow tM tq).comp B.i).k = B.k' := by
  rw [reducedShadow_comp_self]; rfl

theorem reducedShadow_k_of_ne {i' : Fin D.Γ.c} (h : i' ≠ B.i) :
    ((B.reducedShadow tM tq).comp i').k = (D.Γ.comp i').k := by
  rw [reducedShadow_comp_of_ne _ _ _ h]

/-- vertices addressed by natural-number labels transport along an equality of components -/
theorem _root_.SM.Link.PolyComp.P_natCast_eq_of_eq {C C' : PolyComp} (h : C = C') (m : ℕ) :
    C.P (m : ZMod C.k) = C'.P (m : ZMod C'.k) := by
  subst h; rfl

/-- `k' = 0` in `ZMod` of the reduced component's own vertex count (stated on the shadow's modulus) -/
theorem natCast_k'_eq_zero : ((B.k' : ℕ) : ZMod ((B.reducedShadow tM tq).comp B.i).k) = 0 := by
  rw [ZMod.natCast_eq_zero_iff, reducedShadow_k_self]

/-- case analysis on the strands of the reduced shadow: on component `i` (labels `m < k'`), or on another
component (labels `m < k_{i'}`), every strand is a natural-number label -/
@[elab_as_elim] theorem strand_cases {P : (B.reducedShadow tM tq).Strand → Prop}
    (hi : ∀ m : ℕ, m < B.k' → P ⟨B.i, (m : ZMod _)⟩)
    (ho : ∀ (i' : Fin D.Γ.c), i' ≠ B.i → ∀ m : ℕ, m < (D.Γ.comp i').k → P ⟨i', (m : ZMod _)⟩)
    (u : (B.reducedShadow tM tq).Strand) : P u := by
  obtain ⟨i', n⟩ := u
  by_cases h : i' = B.i
  · subst h
    have hn : n.val < B.k' := lt_of_lt_of_eq (ZMod.val_lt n) (B.reducedShadow_k_self tM tq)
    have := hi n.val hn
    rwa [ZMod.natCast_zmod_val] at this
  · have hn : n.val < (D.Γ.comp i').k := lt_of_lt_of_eq (ZMod.val_lt n) (B.reducedShadow_k_of_ne tM tq h)
    have := ho i' h n.val hn
    rwa [ZMod.natCast_zmod_val] at this

theorem reducedTuple_val (m : ℕ) (hm : m < B.k') :
    B.reducedTuple tM tq (m : ZMod B.k') =
      if m = 0 then B.M 0 else if m = 1 then D.Γ.edgePt B.eIn tM
      else if m = 2 then D.Γ.edgePt B.eOut tq else B.M (B.j + m - 2) := by
  unfold reducedTuple
  rw [ZMod.val_natCast, Nat.mod_eq_of_lt hm]

theorem reducedTuple_zero : B.reducedTuple tM tq ((0 : ℕ) : ZMod B.k') = B.M 0 := by
  rw [reducedTuple_val _ _ _ 0 (by have := B.five_le_k'; omega)]; simp

theorem reducedTuple_one : B.reducedTuple tM tq ((1 : ℕ) : ZMod B.k') = D.Γ.edgePt B.eIn tM := by
  rw [reducedTuple_val _ _ _ 1 (by have := B.five_le_k'; omega)]; simp

theorem reducedTuple_two : B.reducedTuple tM tq ((2 : ℕ) : ZMod B.k') = D.Γ.edgePt B.eOut tq := by
  rw [reducedTuple_val _ _ _ 2 (by have := B.five_le_k'; omega)]; simp

theorem reducedTuple_of_ge {m : ℕ} (h3 : 3 ≤ m) (hm : m < B.k') :
    B.reducedTuple tM tq (m : ZMod B.k') = B.M (B.j + m - 2) := by
  rw [reducedTuple_val _ _ _ m hm]
  rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem reducedTuple_k' : B.reducedTuple tM tq ((B.k' : ℕ) : ZMod B.k') = B.M 0 := by
  rw [ZMod.natCast_self]; exact B.reducedTuple_zero tM tq

/-- the tail of the strand `⟨i, m⟩` of the reduced shadow -/
theorem tail_mk_i (m : ℕ) :
    (B.reducedShadow tM tq).tail ⟨B.i, (m : ZMod _)⟩ = B.reducedTuple tM tq (m : ZMod B.k') :=
  PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_self tM tq) m

/-- the direction of the strand `⟨i, m⟩` of the reduced shadow -/
theorem dir_mk_i (m : ℕ) :
    (B.reducedShadow tM tq).dir ⟨B.i, (m : ZMod _)⟩ =
      B.reducedTuple tM tq ((m + 1 : ℕ) : ZMod B.k') - B.reducedTuple tM tq (m : ZMod B.k') := by
  show ((B.reducedShadow tM tq).comp B.i).P ((m : ZMod _) + 1) - ((B.reducedShadow tM tq).comp B.i).P (m : ZMod _) = _
  rw [← Nat.cast_succ, PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_self tM tq),
    PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_self tM tq)]
  rfl

theorem tail_mk_of_ne {i' : Fin D.Γ.c} (h : i' ≠ B.i) (m : ℕ) :
    (B.reducedShadow tM tq).tail ⟨i', (m : ZMod _)⟩ = D.Γ.tail ⟨i', (m : ZMod _)⟩ :=
  PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_of_ne tM tq h) m

theorem dir_mk_of_ne {i' : Fin D.Γ.c} (h : i' ≠ B.i) (m : ℕ) :
    (B.reducedShadow tM tq).dir ⟨i', (m : ZMod _)⟩ = D.Γ.dir ⟨i', (m : ZMod _)⟩ := by
  show ((B.reducedShadow tM tq).comp i').P ((m : ZMod _) + 1) - ((B.reducedShadow tM tq).comp i').P (m : ZMod _) =
    (D.Γ.comp i').P ((m : ZMod _) + 1) - (D.Γ.comp i').P (m : ZMod _)
  rw [← Nat.cast_succ, ← Nat.cast_succ, PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_of_ne tM tq h),
    PolyComp.P_natCast_eq_of_eq (B.reducedShadow_comp_of_ne tM tq h)]

/-! ### 1c.4 The kind map and the index laws -/

/-- the kind of the edge with label `n` (as a natural number) of the reduced component -/
def kindIdx (n : ℕ) : B.Kind :=
  if n = 0 then Kind.cutIn else if n = 1 then Kind.mid else if n = 2 then Kind.cutOut
  else Kind.old (B.strand (B.j + n - 2))

open scoped Classical in
/-- **the kind map** of the reduced shadow -/
def kind (u : (B.reducedShadow tM tq).Strand) : B.Kind :=
  if (u.1 : Fin D.Γ.c) = B.i then B.kindIdx u.2.val else Kind.old ⟨u.1, (u.2.val : ZMod (D.Γ.comp u.1).k)⟩

/-- the reduced label of the old strand `⟨i, b⟩` (given by its value `b`): `(b − a − j).val + 2` -/
def oldIdx (b : ℕ) : ℕ := ((b : ZMod B.k) - B.a - (B.j : ZMod B.k)).val + 2

/-- the strand of the reduced shadow of a given kind -/
def strandOf : B.Kind → (B.reducedShadow tM tq).Strand
  | Kind.cutIn => ⟨B.i, ((0 : ℕ) : ZMod _)⟩
  | Kind.mid => ⟨B.i, ((1 : ℕ) : ZMod _)⟩
  | Kind.cutOut => ⟨B.i, ((2 : ℕ) : ZMod _)⟩
  | Kind.old e => if e.1 = B.i then ⟨B.i, (B.oldIdx e.2.val : ZMod _)⟩ else ⟨e.1, (e.2.val : ZMod _)⟩

/-- the original strand of a strand of the reduced shadow -/
def orig (u : (B.reducedShadow tM tq).Strand) : D.Γ.Strand := (B.kind tM tq u).orig

theorem kindIdx_zero : B.kindIdx 0 = Kind.cutIn := rfl
theorem kindIdx_one : B.kindIdx 1 = Kind.mid := rfl
theorem kindIdx_two : B.kindIdx 2 = Kind.cutOut := rfl
theorem kindIdx_of_ge {n : ℕ} (h : 3 ≤ n) : B.kindIdx n = Kind.old (B.strand (B.j + n - 2)) := by
  unfold kindIdx; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem kind_mk_i (m : ℕ) (hm : m < B.k') : B.kind tM tq ⟨B.i, (m : ZMod _)⟩ = B.kindIdx m := by
  unfold kind
  dsimp only
  split_ifs with h
  · congr 1
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    rwa [reducedShadow_k_self]
  · exact absurd rfl h

theorem kind_mk_of_ne {i' : Fin D.Γ.c} (h : i' ≠ B.i) (m : ℕ) (hm : m < (D.Γ.comp i').k) :
    B.kind tM tq ⟨i', (m : ZMod _)⟩ = Kind.old ⟨i', (m : ZMod _)⟩ := by
  unfold kind
  dsimp only
  split_ifs with h'
  · exact absurd h' h
  · congr 2
    rw [ZMod.val_natCast, Nat.mod_eq_of_lt]
    rwa [reducedShadow_k_of_ne _ _ _ h]

/-- **Index law: tails.** -/
theorem tail_eq (u : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).tail u = (B.kind tM tq u).tail tM tq := by
  refine B.strand_cases tM tq ?_ ?_ u
  · intro m hm
    rw [tail_mk_i, kind_mk_i _ _ _ m hm]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · rw [reducedTuple_zero, kindIdx_zero, Kind.tail, M_zero]
      · rw [reducedTuple_one, kindIdx_one, Kind.tail]
      · rw [reducedTuple_two, kindIdx_two, Kind.tail]
    · rw [reducedTuple_of_ge _ _ _ h3 hm, kindIdx_of_ge _ h3, Kind.tail, tail_strand]
  · intro i' h m hm
    rw [tail_mk_of_ne _ _ _ h, kind_mk_of_ne _ _ _ h m hm, Kind.tail]

/-- **Index law: directions.** -/
theorem dir_eq (u : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).dir u = (B.kind tM tq u).dir tM tq := by
  refine B.strand_cases tM tq ?_ ?_ u
  · intro m hm
    rw [dir_mk_i, kind_mk_i _ _ _ m hm]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · rw [reducedTuple_zero, reducedTuple_one, kindIdx_zero, Kind.dir, M_zero, Shadow.edgePt_eq]
        simp
      · rw [reducedTuple_one, reducedTuple_two, kindIdx_one, Kind.dir]
      · rw [reducedTuple_two, reducedTuple_of_ge _ _ _ (le_refl 3) (by have := B.five_le_k'; omega),
          kindIdx_two, Kind.dir]
        rw [show B.j + 3 - 2 = B.j + 1 by omega, M_succ_j, Shadow.head_eq_tail_add_dir, Shadow.edgePt_eq]
        module
    · rw [kindIdx_of_ge _ h3, Kind.dir, reducedTuple_of_ge _ _ _ h3 hm]
      rcases Nat.lt_or_ge (m + 1) B.k' with hlt | hge
      · rw [reducedTuple_of_ge _ _ _ (by omega) hlt, Shadow.dir, strand, edge, M, M,
          show B.j + (m + 1) - 2 = B.j + m - 2 + 1 by omega, Nat.cast_succ, add_assoc]
      · have hm1 : m + 1 = B.k' := by omega
        rw [hm1, reducedTuple_k', M_zero, Shadow.dir, strand, edge, M, Shadow.tail]
        have : B.a + ((B.j + m - 2 : ℕ) : ZMod B.k) + 1 = B.a := by
          rw [add_assoc, ← Nat.cast_succ, show (B.j + m - 2).succ = B.k by have := B.k'_add_j; omega,
            ZMod.natCast_self, add_zero]
        rw [this]
  · intro i' h m hm
    rw [dir_mk_of_ne _ _ _ h, kind_mk_of_ne _ _ _ h m hm, Kind.dir]

theorem seg_eq (u : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).seg u = (B.kind tM tq u).seg tM tq := by
  unfold Kind.seg
  rw [← tail_eq, ← dir_eq]; rfl

theorem interior_eq (u : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).interior u = (B.kind tM tq u).interior tM tq := by
  unfold Kind.interior
  rw [← tail_eq, ← dir_eq]; rfl

theorem head_eq (u : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).head u = (B.kind tM tq u).head tM tq := by
  rw [Shadow.head_eq_tail_add_dir, tail_eq, dir_eq]; rfl

/-- the evaluation of a traversal point of the reduced shadow through the kind of its strand -/
theorem eval_eq (q : (B.reducedShadow tM tq).Pt) :
    (B.reducedShadow tM tq).eval q =
      (B.kind tM tq ⟨q.1, q.2.1⟩).tail tM tq + q.2.2.val • (B.kind tM tq ⟨q.1, q.2.1⟩).dir tM tq := by
  rw [← tail_eq, ← dir_eq]; rfl

/-- every strand of the reduced shadow has an occurring kind -/
theorem kind_occurs (u : (B.reducedShadow tM tq).Strand) : (B.kind tM tq u).Occurs := by
  refine B.strand_cases tM tq ?_ ?_ u
  · intro m hm
    rw [kind_mk_i _ _ _ m hm]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · exact Kind.occurs_cutIn
      · exact Kind.occurs_mid
      · exact Kind.occurs_cutOut
    · rw [kindIdx_of_ge _ h3]
      refine Kind.occurs_old fun m' hm' heq => ?_
      have := B.strand_inj (by have := B.k'_add_j; omega) (by have := B.hk'; omega) heq
      omega
  · intro i' h m hm
    rw [kind_mk_of_ne _ _ _ h m hm]
    exact Kind.occurs_old_of_fst_ne h

theorem kindIdx_inj {m m' : ℕ} (hm : m < B.k') (hm' : m' < B.k') (h : B.kindIdx m = B.kindIdx m') : m = m' := by
  rcases Nat.lt_or_ge m 3 with h3 | h3 <;> rcases Nat.lt_or_ge m' 3 with h3' | h3'
  · interval_cases m <;> interval_cases m' <;> first | rfl | (exfalso; cases h)
  · rw [kindIdx_of_ge _ h3'] at h
    interval_cases m <;> cases h
  · rw [kindIdx_of_ge _ h3] at h
    interval_cases m' <;> cases h
  · rw [kindIdx_of_ge _ h3, kindIdx_of_ge _ h3'] at h
    have := B.strand_inj (by have := B.k'_add_j; omega) (by have := B.k'_add_j; omega) (Kind.old.inj h)
    omega

theorem kindIdx_old_fst {n : ℕ} {e : D.Γ.Strand} (h : B.kindIdx n = Kind.old e) : e.1 = B.i := by
  rcases Nat.lt_or_ge n 3 with h3 | h3
  · interval_cases n <;> cases h
  · rw [kindIdx_of_ge _ h3] at h
    exact (congrArg Sigma.fst (Kind.old.inj h)).symm

/-- **Index law: the kind map is injective.** -/
theorem kind_injective : Function.Injective (B.kind tM tq) := by
  intro u u'
  refine B.strand_cases tM tq ?_ ?_ u <;> refine B.strand_cases tM tq ?_ ?_ u'
  · intro m' hm' m hm heq
    rw [kind_mk_i _ _ _ m hm, kind_mk_i _ _ _ m' hm'] at heq
    rw [B.kindIdx_inj hm hm' heq]
  · intro i' h m' hm' m hm heq
    exfalso
    rw [kind_mk_i _ _ _ m hm, kind_mk_of_ne _ _ _ h m' hm'] at heq
    exact h (B.kindIdx_old_fst heq)
  · intro m' hm' i' h m hm heq
    exfalso
    rw [kind_mk_i _ _ _ m' hm', kind_mk_of_ne _ _ _ h m hm] at heq
    exact h (B.kindIdx_old_fst heq.symm)
  · intro i₂ h₂ m₂ hm₂ i₁ h₁ m₁ hm₁ heq
    rw [kind_mk_of_ne _ _ _ h₁ m₁ hm₁, kind_mk_of_ne _ _ _ h₂ m₂ hm₂] at heq
    have h1 := Kind.old.inj heq
    rw [Sigma.mk.inj_iff] at h1
    obtain ⟨rfl, h2⟩ := h1
    have h3 := eq_of_heq h2
    rw [Smoothing.nat_eq_of_zcast_eq hm₁ hm₂ h3]

/-- the reduced label of an occurring old strand of component `i`: `3 ≤ oldIdx b < k'`, and it lands on
`old ⟨i, b⟩` -/
theorem oldIdx_spec {b : ZMod B.k} (hb : ∀ m : ℕ, m ≤ B.j → (⟨B.i, b⟩ : D.Γ.Strand) ≠ B.strand m) :
    3 ≤ B.oldIdx b.val ∧ B.oldIdx b.val < B.k' ∧ B.kindIdx (B.oldIdx b.val) = Kind.old ⟨B.i, b⟩ := by
  have hd : B.j < (b - B.a).val := by
    by_contra hle
    rw [not_lt] at hle
    apply hb (b - B.a).val hle
    simp [strand]
  have hlt := ZMod.val_lt (b - B.a)
  have hsub : (b - B.a - (B.j : ZMod B.k)).val = (b - B.a).val - B.j := by
    have e : b - B.a - (B.j : ZMod B.k) = (((b - B.a).val - B.j : ℕ) : ZMod B.k) := by
      rw [Nat.cast_sub hd.le, ZMod.natCast_zmod_val]
    rw [e, ZMod.val_natCast, Nat.mod_eq_of_lt (by omega)]
  unfold oldIdx
  rw [ZMod.natCast_zmod_val, hsub]
  refine ⟨by omega, by unfold k'; omega, ?_⟩
  rw [kindIdx_of_ge _ (by omega)]
  congr 2
  unfold strand
  rw [show B.j + ((b - B.a).val - B.j + 2) - 2 = (b - B.a).val by omega, ZMod.natCast_zmod_val]
  simp

/-- **Index law: every occurring kind is realised.** -/
theorem kind_strandOf (κ : B.Kind) (hκ : κ.Occurs) : B.kind tM tq (B.strandOf tM tq κ) = κ := by
  cases κ with
  | cutIn => rw [strandOf, kind_mk_i _ _ _ 0 (by have := B.five_le_k'; omega)]; rfl
  | mid => rw [strandOf, kind_mk_i _ _ _ 1 (by have := B.five_le_k'; omega)]; rfl
  | cutOut => rw [strandOf, kind_mk_i _ _ _ 2 (by have := B.five_le_k'; omega)]; rfl
  | old e =>
    obtain ⟨i', b⟩ := e
    by_cases h : i' = B.i
    · subst h
      obtain ⟨-, h2, h3⟩ := B.oldIdx_spec (fun m hm heq => hκ m hm (by rw [heq]))
      rw [strandOf, ite_eq_left rfl, kind_mk_i _ _ _ _ h2, h3]
    · rw [strandOf, ite_eq_right h, kind_mk_of_ne _ _ _ h b.val (ZMod.val_lt b), ZMod.natCast_zmod_val]

theorem kind_surj (κ : B.Kind) (hκ : κ.Occurs) : ∃ u, B.kind tM tq u = κ :=
  ⟨B.strandOf tM tq κ, B.kind_strandOf tM tq κ hκ⟩

theorem strandOf_kind (u : (B.reducedShadow tM tq).Strand) : B.strandOf tM tq (B.kind tM tq u) = u :=
  B.kind_injective tM tq (B.kind_strandOf tM tq _ (B.kind_occurs tM tq u))

/-- the cyclic predecessor label `⟨i', m⟩ − 1`, as a natural-number label (the modulus `N` of the strand
type and its value `N'` are kept apart so that no rewriting inside `ZMod N` is needed) -/
theorem natCast_sub_one_eq {N N' : ℕ} [NeZero N] (hN : N = N') {m : ℕ} (hm : m < N') :
    ((m : ZMod N) - 1) = (((if m = 0 then N' - 1 else m - 1 : ℕ)) : ZMod N) := by
  subst hN
  split_ifs with h
  · subst h
    rw [Nat.cast_pred (Nat.pos_of_ne_zero (NeZero.ne N)), ZMod.natCast_self]; simp
  · rw [Nat.cast_pred (Nat.pos_of_ne_zero h)]

/-- **Index law: the predecessor.**  The kind of the preceding strand is the `pred` of the kind (this
encodes the whole adjacency structure of the reduced shadow). -/
theorem kind_pred (u : (B.reducedShadow tM tq).Strand) :
    B.kind tM tq ⟨u.1, u.2 - 1⟩ = (B.kind tM tq u).pred := by
  refine B.strand_cases tM tq ?_ ?_ u
  · intro m hm
    have hN : ((B.reducedShadow tM tq).comp B.i).k = B.k' := B.reducedShadow_k_self tM tq
    show B.kind tM tq ⟨B.i, (m : ZMod _) - 1⟩ = _
    rw [natCast_sub_one_eq hN hm, kind_mk_i _ _ _ m hm]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · rw [ite_eq_left rfl, kind_mk_i _ _ _ _ (by have := B.five_le_k'; omega), kindIdx_of_ge _ (by have := B.five_le_k'; omega),
          kindIdx_zero, Kind.pred]
        congr 2
        unfold strand
        rw [show B.j + (B.k' - 1) - 2 = B.k - 1 by have := B.k'_add_j; omega,
          Nat.cast_pred (by have := B.three_le_k; omega), ZMod.natCast_self, zero_sub, ← sub_eq_add_neg]
      · rw [ite_eq_right one_ne_zero, kind_mk_i _ _ _ 0 (by have := B.five_le_k'; omega)]; rfl
      · rw [ite_eq_right two_ne_zero, kind_mk_i _ _ _ 1 (by have := B.five_le_k'; omega)]; rfl
    · rw [ite_eq_right (by omega), kind_mk_i _ _ _ (m - 1) (by omega), kindIdx_of_ge _ h3, Kind.pred]
      rcases Nat.lt_or_ge m 4 with h4 | h4
      · have hm3 : m = 3 := by omega
        subst hm3
        rw [show (3 : ℕ) - 1 = 2 from rfl, show B.j + 3 - 2 = B.j + 1 by omega, ite_eq_left rfl, kindIdx_two]
      · rw [kindIdx_of_ge _ (by omega), ite_eq_right]
        · congr 2
          unfold strand
          rw [show B.j + m - 2 = (B.j + (m - 1) - 2) + 1 by omega, Nat.cast_succ, ← add_assoc,
            add_sub_cancel_right]
        · intro heq
          have := B.strand_inj (by have := B.k'_add_j; omega) (by have := B.hk'; omega) heq
          omega
  · intro i' h m hm
    have hN : ((B.reducedShadow tM tq).comp i').k = (D.Γ.comp i').k := B.reducedShadow_k_of_ne tM tq h
    have hne : (⟨i', (m : ZMod (D.Γ.comp i').k)⟩ : D.Γ.Strand) ≠ B.strand (B.j + 1) :=
      fun heq => h (congrArg Sigma.fst heq)
    have hk3 := (D.Γ.comp i').hk
    have hm' : (if m = 0 then (D.Γ.comp i').k - 1 else m - 1) < (D.Γ.comp i').k := by split_ifs <;> omega
    show B.kind tM tq ⟨i', (m : ZMod _) - 1⟩ = _
    rw [kind_mk_of_ne _ _ _ h m hm, Kind.pred, ite_eq_right hne, natCast_sub_one_eq hN hm,
      kind_mk_of_ne _ _ _ h _ hm', natCast_sub_one_eq rfl hm]

/-- **Index law: the successor.** -/
theorem kind_succ (u : (B.reducedShadow tM tq).Strand) :
    B.kind tM tq ⟨u.1, u.2 + 1⟩ = (B.kind tM tq u).succ := by
  have h := B.kind_pred tM tq ⟨u.1, u.2 + 1⟩
  simp only [add_sub_cancel_right] at h
  have hu : (⟨u.1, u.2⟩ : (B.reducedShadow tM tq).Strand) = u := rfl
  rw [hu] at h
  rw [h, Kind.succ_pred _ (B.kind_occurs tM tq _)]

/-- **Index law: adjacency**, read on kinds (`kind_succ`, `kind_pred`, `kind_injective`). -/
theorem adjacent_iff_kind (u u' : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).Adjacent u u' ↔
      B.kind tM tq u' = B.kind tM tq u ∨ B.kind tM tq u' = (B.kind tM tq u).succ ∨
        B.kind tM tq u' = (B.kind tM tq u).pred := by
  constructor
  · rintro ⟨i', a₁, a₂, rfl, rfl, h | h | h⟩
    · have : a₂ = a₁ - 1 := by linear_combination h
      right; right; rw [this]; exact B.kind_pred tM tq ⟨i', a₁⟩
    · left; rw [sub_eq_zero.mp h]
    · have : a₂ = a₁ + 1 := by linear_combination h
      right; left; rw [this]; exact B.kind_succ tM tq ⟨i', a₁⟩
  · rintro (h | h | h)
    · rw [B.kind_injective tM tq h]; exact Shadow.Adjacent.refl _ u
    · rw [← B.kind_succ] at h; rw [B.kind_injective tM tq h]; exact Shadow.adjacent_mk_add_one _ u
    · rw [← B.kind_pred] at h; rw [B.kind_injective tM tq h]; exact Shadow.adjacent_mk_sub_one _ u

/-- **Index law: vertex–edge incidence**, read on kinds. -/
theorem incidentTail_iff_kind (u u' : (B.reducedShadow tM tq).Strand) :
    (B.reducedShadow tM tq).IncidentTail u u' ↔
      B.kind tM tq u' = B.kind tM tq u ∨ B.kind tM tq u' = (B.kind tM tq u).pred := by
  constructor
  · rintro ⟨i', a₁, a₂, rfl, rfl, h | h⟩
    · right; rw [h]; exact B.kind_pred tM tq ⟨i', a₁⟩
    · left; rw [h]
  · rintro (h | h)
    · rw [B.kind_injective tM tq h]; exact ⟨u.1, u.2, u.2, rfl, rfl, Or.inr rfl⟩
    · rw [← B.kind_pred] at h; rw [B.kind_injective tM tq h]
      exact ⟨u.1, u.2, u.2 - 1, rfl, rfl, Or.inl rfl⟩

/-- the strand of an old kind keeps its component -/
theorem strandOf_old_fst (e : D.Γ.Strand) : (B.strandOf tM tq (Kind.old e)).1 = e.1 := by
  obtain ⟨i', b⟩ := e
  simp only [strandOf]
  split_ifs with h
  · exact h.symm
  · rfl

end Reduced

/-! ### 1c.5 Genericity of the reduced shadow (unit U-M2), the crossing correspondence (unit U-M3) and the
reduced diagram -/

section Construction

variable {B} (C : B.Cut)

/-- the reduced shadow of a cut -/
abbrev Cut.shadow : Shadow := B.reducedShadow C.tM C.tq

/-- **Sub-leaf (U-M2).**  Regularity: at `M₀` and `M_{j+1}` the new edges are positive rescalings
(`regularPair_smul_pos`); at `M'` by `q ∉ line(e_in)` (`Cut.q_off_in`, `regularPair_of_det_ne_zero`); at `q`
by `M' ∉ line(e_out)` (`Cut.mid_off_out`); elsewhere `D.generic.regular`. -/
theorem m2_regular (i' : Fin D.Γ.c) : Regular (C.shadow.comp i').P := by
  sorry

/-- **Sub-leaf (U-M2).**  No vertex on a non-incident edge: new vertices `M', q ∈ U` versus foreign edges
(`Cut.clear`), versus `s` (`e_in ∩ s = {y}`, `t_M ≠ t_y`; `e_out ∩ s = {z}`), versus the other cut piece (the two
`det` fields); old vertices versus the middle edge (`M₀, M_{j+1}, tail s` and every foreign tail are outside
`U`, `[M', q] ⊆ U` by convexity); everything else is `D.generic.tail_off` read through `kind`. -/
theorem m2_tail_off (u u' : C.shadow.Strand) (h : ¬ C.shadow.IncidentTail u u') :
    C.shadow.tail u ∉ C.shadow.seg u' := by
  sorry

/-- **Sub-leaf (U-M2).**  Transversality: two non-adjacent strands that meet have independent directions —
the middle edge meets nothing non-adjacent (`[M', q] ⊆ U` misses the foreign edges, `Cut.mid_side` keeps it off
`s`, `q ∉ line(e_in)` / `M' ∉ line(e_out)` keep its interior off the cut pieces); a cut piece meets a foreign
edge only at a crossing of `D` (`Kind.dir_eq_smul_orig`, `det_smul_smul`). -/
theorem m2_transverse (u u' : C.shadow.Strand) (h : ¬ C.shadow.Adjacent u u')
    (hmeet : (C.shadow.seg u ∩ C.shadow.seg u').Nonempty) :
    det (C.shadow.dir u) (C.shadow.dir u') ≠ 0 := by
  sorry

/-- **Sub-leaf (U-M2).**  No triple point: the middle edge has no interior point on another strand, and `orig`
is injective on the other three kinds, so a triple point of the reduced shadow is a triple point of `D`. -/
theorem m2_no_triple : ¬ ∃ u u' u'' : C.shadow.Strand, u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧
    (C.shadow.interior u ∩ C.shadow.interior u' ∩ C.shadow.interior u'').Nonempty := by
  sorry

/-- **Leaf of U-M2 (assembled from the four sub-leaves).**  The reduced shadow is generic. -/
theorem m2_generic : C.shadow.Generic where
  regular := m2_regular C
  tail_off := m2_tail_off C
  transverse := m2_transverse C
  no_triple := m2_no_triple C

/-- **Sub-leaf (U-M3).**  The original strands of the two strands of a crossing of the reduced shadow form
a crossing of `D` (both strands are non-middle, `Kind.orig` of distinct non-middle kinds are distinct, the
common point is a common point of the originals, non-adjacency transports through `kind_pred`). -/
theorem m3_isCrossing_orig (y' : C.shadow.Crossing) :
    D.Γ.IsCrossing {B.orig C.tM C.tq y'.fst, B.orig C.tM C.tq y'.snd} := by
  sorry

/-- the crossing of `D` under a crossing of the reduced shadow -/
def origCrossing (y' : C.shadow.Crossing) : D.Γ.Crossing :=
  ⟨{B.orig C.tM C.tq y'.fst, B.orig C.tM C.tq y'.snd}, m3_isCrossing_orig C y'⟩

theorem orig_mem_origCrossing {y' : C.shadow.Crossing} {u : C.shadow.Strand} (hu : u ∈ y'.val) :
    B.orig C.tM C.tq u ∈ (origCrossing C y').val := by
  show B.orig C.tM C.tq u ∈ ({B.orig C.tM C.tq y'.fst, B.orig C.tM C.tq y'.snd} : Finset D.Γ.Strand)
  rw [y'.val_eq] at hu
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu
  rcases hu with rfl | rfl <;> simp

/-- **Sub-leaf (U-M3).**  No crossing of the reduced shadow uses the middle edge. -/
theorem m3_kind_ne_mid (y' : C.shadow.Crossing) {u : C.shadow.Strand} (hu : u ∈ y'.val) :
    B.kind C.tM C.tq u ≠ Kind.mid := by
  sorry

/-- **Sub-leaf (U-M3).**  `orig` is injective on the two strands of a crossing (a crossing never uses both
`cutIn` and `mid`, the only two kinds with the same original). -/
theorem m3_orig_injOn_crossing (y' : C.shadow.Crossing) {u u' : C.shadow.Strand} (hu : u ∈ y'.val)
    (hu' : u' ∈ y'.val) (h : B.orig C.tM C.tq u = B.orig C.tM C.tq u') : u = u' := by
  sorry

/-- **Sub-leaf (U-M3).**  The deleted crossings are not hit: `y` would need the cut piece of `e_in` to reach
`t_y > t_M`, `z` the cut piece of `e_out` to reach `t_z < t_q`. -/
theorem m3_origCrossing_ne_y (y' : C.shadow.Crossing) : origCrossing C y' ≠ B.y := by
  sorry

theorem m3_origCrossing_ne_z (y' : C.shadow.Crossing) : origCrossing C y' ≠ B.z := by
  sorry

/-- **Sub-leaf (U-M3).**  Equal double points (`Kind.tail_add_smul_dir`, `Generic.common_point_unique`). -/
theorem m3_crossingPoint_origCrossing (y' : C.shadow.Crossing) :
    C.shadow.crossingPoint y' = D.Γ.crossingPoint (origCrossing C y') := by
  sorry

/-- **Sub-leaf (U-M3).**  The crossing correspondence is injective (equal double points, `no_triple`). -/
theorem m3_origCrossing_injective : Function.Injective (origCrossing C) := by
  sorry

/-- **Sub-leaf (U-M3).**  Every crossing of `D` other than `y, z` lifts: its strands are foreign, or `s`, or
`e_in` at a parameter `< t_p` (foreign edges miss `U`), or `e_out` at a parameter `> t_q`; the lifted strands
still meet and are non-adjacent. -/
theorem m3_exists_lift (x : D.Γ.Crossing) (hy : x ≠ B.y) (hz : x ≠ B.z) :
    ∃ y' : C.shadow.Crossing, origCrossing C y' = x := by
  sorry

/-- **The crossing bijection** `D' ≃ D ∖ {y, z}` (assembled from the U-M3 sub-leaves). -/
noncomputable def crossingEquiv : C.shadow.Crossing ≃ {x : D.Γ.Crossing // x ≠ B.y ∧ x ≠ B.z} :=
  Equiv.ofBijective (fun y' => ⟨origCrossing C y', m3_origCrossing_ne_y C y', m3_origCrossing_ne_z C y'⟩)
    ⟨fun y' y'' h => m3_origCrossing_injective C (congrArg Subtype.val h),
     fun x => by
      obtain ⟨y', hy'⟩ := m3_exists_lift C x.1 x.2.1 x.2.2
      exact ⟨y', Subtype.ext hy'⟩⟩

/-- the over strand of the reduced diagram at `y'`: the strand of `y'` lying over the over strand of `D` at
the original crossing (over data pulled back through `orig`) -/
noncomputable def overStrand' (y' : C.shadow.Crossing) : C.shadow.Strand :=
  if B.orig C.tM C.tq y'.fst = D.overStrand (origCrossing C y') then y'.fst else y'.snd

theorem overStrand'_mem (y' : C.shadow.Crossing) : overStrand' C y' ∈ y'.val := by
  unfold overStrand'
  split_ifs
  · exact y'.fst_mem
  · exact y'.snd_mem

theorem orig_overStrand' (y' : C.shadow.Crossing) :
    B.orig C.tM C.tq (overStrand' C y') = D.overStrand (origCrossing C y') := by
  unfold overStrand'
  split_ifs with h
  · exact h
  · have h1 : B.orig C.tM C.tq y'.fst = D.underStrand (origCrossing C y') :=
      D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing C y'.fst_mem) h
    apply D.eq_over_of_mem_of_ne _ (orig_mem_origCrossing C y'.snd_mem)
    intro h2
    exact C.shadow.other_ne y' y'.fst_mem
      (m3_orig_injOn_crossing C y' y'.snd_mem y'.fst_mem (h2.trans h1.symm))

/-- **The reduced diagram** `D'`: the reduced shadow with the over data of `D` pulled back through `orig`. -/
noncomputable def reducedDiagram : Diagram where
  Γ := C.shadow
  generic := m2_generic C
  overStrand := overStrand' C
  over_mem := overStrand'_mem C

@[simp] theorem reducedDiagram_Γ : (B.reducedDiagram C).Γ = C.shadow := rfl

theorem reducedDiagram_componentCount : (B.reducedDiagram C).componentCount = D.componentCount := rfl

theorem reducedDiagram_underStrand_orig (y' : C.shadow.Crossing) :
    B.orig C.tM C.tq ((B.reducedDiagram C).underStrand y') = D.underStrand (origCrossing C y') := by
  have hmem : (B.reducedDiagram C).underStrand y' ∈ y'.val := (B.reducedDiagram C).under_mem y'
  have hne : (B.reducedDiagram C).underStrand y' ≠ overStrand' C y' := (B.reducedDiagram C).under_ne_over y'
  apply D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing C hmem)
  intro h
  exact hne (m3_orig_injOn_crossing C y' hmem (overStrand'_mem C y') (h.trans (orig_overStrand' C y').symm))

/-- **Signs are inherited** (the directions of the cut pieces are positive multiples of the originals; a
consequence of `m3_kind_ne_mid`). -/
theorem m3_sign (y' : C.shadow.Crossing) : (B.reducedDiagram C).sign y' = D.sign (origCrossing C y') := by
  have key : ∀ u u' : C.shadow.Strand, u ∈ y'.val → u' ∈ y'.val →
      B.orig C.tM C.tq u = D.overStrand (origCrossing C y') →
      B.orig C.tM C.tq u' = D.underStrand (origCrossing C y') →
      SignType.sign (det (C.shadow.dir u) (C.shadow.dir u')) = D.sign (origCrossing C y') := by
    intro u u' hu hu' ho ho'
    obtain ⟨l, hl, hdl⟩ := Kind.dir_eq_smul_orig C.tM C.tq C.tM_pos C.tq_lt_one (B.kind C.tM C.tq u)
      (m3_kind_ne_mid C y' hu)
    obtain ⟨m, hm, hdm⟩ := Kind.dir_eq_smul_orig C.tM C.tq C.tM_pos C.tq_lt_one (B.kind C.tM C.tq u')
      (m3_kind_ne_mid C y' hu')
    unfold Diagram.sign
    rw [B.dir_eq, B.dir_eq, hdl, hdm, det_smul_smul, sign_mul, sign_pos (mul_pos hl hm), one_mul]
    show SignType.sign (det (D.Γ.dir (B.orig C.tM C.tq u)) (D.Γ.dir (B.orig C.tM C.tq u'))) = _
    rw [ho, ho']
  exact key _ _ (overStrand'_mem C y') ((B.reducedDiagram C).under_mem y') (orig_overStrand' C y')
    (reducedDiagram_underStrand_orig C y')

/-- **Sub-leaf (U-M3).**  The crossing parameter of a strand through `y'` is the lifted parameter of `D`
(`Kind.tail_add_smul_dir`, `m3_crossingPoint_origCrossing`, `Generic.edgePt_injective`). -/
theorem m3_crossingParam (y' : C.shadow.Crossing) {u : C.shadow.Strand} (hu : u ∈ y'.val) :
    (B.reducedDiagram C).crossingParam y' hu =
      (B.kind C.tM C.tq u).liftParam C.tM C.tq
        (D.crossingParam (origCrossing C y') (orig_mem_origCrossing C hu)) := by
  sorry

/-! ### 1c.6 The arcs and the cleanness of the two diagrams inside `U` (unit U-M4) -/

/-- the arc `[p → M₁ → … → M_j → q]` of `D` inside `U` (on component `i`: enters on `e_in` at `t_p`, exits on
`e_out` at `t_q`) -/
def arcIn : D.Γ.Arc := ⟨B.i, (B.a, clampIco C.tp), (B.a + (B.j : ZMod B.k), clampIco C.tq)⟩

/-- the arc `s ∩ U = [b_in, b_out]` of `D` -/
def arcS : D.Γ.Arc := ⟨B.s.1, (B.s.2, clampIco C.tin), (B.s.2, clampIco C.tout)⟩

/-- the arc `[p → M' → q]` of the reduced diagram (enters on `cutIn` at `t_p / t_M`, exits at the vertex `q`,
the tail of `cutOut`) -/
def arcIn' : C.shadow.Arc :=
  ⟨B.i, (((0 : ℕ) : ZMod _), clampIco (C.tp / C.tM)), (((2 : ℕ) : ZMod _), ⟨0, le_rfl, zero_lt_one⟩)⟩

/-- the strand of the reduced shadow carrying `s` -/
def sStrand : C.shadow.Strand := B.strandOf C.tM C.tq (Kind.old B.s)

/-- the arc `s ∩ U` of the reduced diagram (the same points, read on the reduced label of `s`) -/
def arcS' : C.shadow.Arc :=
  ⟨(sStrand C).1, ((sStrand C).2, clampIco C.tin), ((sStrand C).2, clampIco C.tout)⟩

theorem kind_sStrand : B.kind C.tM C.tq (sStrand C) = Kind.old B.s :=
  B.kind_strandOf C.tM C.tq _ (Kind.occurs_old fun m hm => by
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [strand_zero]; exact B.s_ne_eIn
    · rcases hm.lt_or_eq with hlt | rfl
      · intro heq
        exact B.run_free m hpos hlt B.y (heq ▸ B.s_mem_y : B.strand m ∈ B.y.val)
      · exact B.s_ne_eOut)

/-- the four arc ends: `p`, `q`, `b_in`, `b_out` -/
theorem eval_arcIn_start : D.Γ.eval (arcIn C).startPt = C.p := by
  show D.Γ.edgePt B.eIn (clampIco C.tp).val = _
  rw [clampIco_val_of_mem ⟨C.tp_pos.le, C.tp_lt_one⟩]; rfl

theorem eval_arcIn_stop : D.Γ.eval (arcIn C).stopPt = C.q := by
  show D.Γ.edgePt B.eOut (clampIco C.tq).val = _
  rw [clampIco_val_of_mem ⟨C.tq_pos.le, C.tq_lt_one⟩]; rfl

theorem eval_arcS_start : D.Γ.eval (arcS C).startPt = C.sIn := by
  show D.Γ.edgePt B.s (clampIco C.tin).val = _
  rw [clampIco_val_of_mem ⟨C.tin_pos.le, C.tin_lt_tout.trans C.tout_lt_one⟩]; rfl

theorem eval_arcS_stop : D.Γ.eval (arcS C).stopPt = C.sOut := by
  show D.Γ.edgePt B.s (clampIco C.tout).val = _
  rw [clampIco_val_of_mem ⟨(C.tin_pos.trans C.tin_lt_tout).le, C.tout_lt_one⟩]; rfl

theorem eval_arcIn'_start : C.shadow.eval (arcIn' C).startPt = C.p := by
  have h0 : (0 : ℕ) < B.k' := by have := B.five_le_k'; omega
  have hval : (clampIco (C.tp / C.tM)).val = C.tp / C.tM :=
    clampIco_val_of_mem ⟨(div_pos C.tp_pos C.tM_pos).le, (div_lt_one C.tM_pos).mpr C.tp_lt_tM⟩
  show C.shadow.eval ⟨B.i, (((0 : ℕ) : ZMod _), clampIco (C.tp / C.tM))⟩ = _
  rw [B.eval_eq, B.kind_mk_i _ _ _ h0, kindIdx_zero, Kind.tail, Kind.dir, hval, smul_smul,
    div_mul_cancel₀ _ C.tM_pos.ne']
  rfl

theorem eval_arcIn'_stop : C.shadow.eval (arcIn' C).stopPt = C.q := by
  have h2 : (2 : ℕ) < B.k' := by have := B.five_le_k'; omega
  show C.shadow.eval ⟨B.i, (((2 : ℕ) : ZMod _), ⟨0, le_rfl, zero_lt_one⟩)⟩ = _
  rw [B.eval_eq, B.kind_mk_i _ _ _ h2, kindIdx_two, Kind.tail]
  simp [Cut.q]

theorem eval_arcS'_start : C.shadow.eval (arcS' C).startPt = C.sIn := by
  show C.shadow.eval ⟨(sStrand C).1, ((sStrand C).2, clampIco C.tin)⟩ = _
  rw [B.eval_eq]
  have : (⟨(sStrand C).1, (sStrand C).2⟩ : C.shadow.Strand) = sStrand C := rfl
  rw [this, kind_sStrand, Kind.tail, Kind.dir,
    clampIco_val_of_mem ⟨C.tin_pos.le, C.tin_lt_tout.trans C.tout_lt_one⟩]
  rfl

theorem eval_arcS'_stop : C.shadow.eval (arcS' C).stopPt = C.sOut := by
  show C.shadow.eval ⟨(sStrand C).1, ((sStrand C).2, clampIco C.tout)⟩ = _
  rw [B.eval_eq]
  have : (⟨(sStrand C).1, (sStrand C).2⟩ : C.shadow.Strand) = sStrand C := rfl
  rw [this, kind_sStrand, Kind.tail, Kind.dir,
    clampIco_val_of_mem ⟨(C.tin_pos.trans C.tin_lt_tout).le, C.tout_lt_one⟩]
  rfl

/-- **Sub-leaf (U-M4).**  The two arcs of `D` are distinct (different strands at the entering end:
`e_in ≠ s`). -/
theorem m4_arcIn_ne_arcS : arcIn C ≠ arcS C := by
  sorry

/-- **Sub-leaf (U-M4).**  The two arcs of the reduced diagram are distinct. -/
theorem m4_arcIn'_ne_arcS' : arcIn' C ≠ arcS' C := by
  sorry

/-- **Sub-leaf (U-M4, the `mem_iff` classification).**  `D ∩ U` is exactly the two arcs: a traversal point of
`D` evaluates into `U` iff it lies on `[p → M₁ → … → M_j → q]` or on `[b_in, b_out]` (`Cut.in_iff`,
`Cut.out_iff`, `Cut.s_iff`, `Cut.clear`, `Cut.run_mem_interior` + convexity for the run edges;
`traversalBetween` arithmetic on the labels `a, a+1, …, a+j`), the arcs are arcs of `U` (`IsArc`: ends on the
frontier by `Cut.p_frontier` etc., inner points in `interior U` by the interior laws) and disjoint. -/
theorem m4_arcCover : D.Γ.ArcCover C.U {arcIn C, arcS C} := by
  sorry

/-- **Sub-leaf (U-M4).**  `D' ∩ U` is exactly the two arcs `[p → M' → q]` (kinds `cutIn` from `t_p / t_M`,
`mid`, the vertex `q`) and `s ∩ U`. -/
theorem m4_arcCover' : C.shadow.ArcCover C.U {arcIn' C, arcS' C} := by
  sorry

/-- **Sub-leaf (U-M4).**  `D` meets `U` cleanly: the frontier points of the trace are the four ends, each
traversed once (none is a vertex or a double point); every component has a point outside `U` (`M₀`, or the
tail of a foreign strand, or `tail s`). -/
theorem m4_clean : Clean C.U D := by
  sorry

/-- **Sub-leaf (U-M4).**  The reduced diagram meets `U` cleanly. -/
theorem m4_clean' : Clean C.U (B.reducedDiagram C) := by
  sorry

/-- **Sub-leaf (U-M4).**  The crossings of `D` inside `U` are exactly `y` and `z` (every other crossing has a
foreign strand, `Cut.clear`; `y, z ∈ K ⊆ interior U`). -/
theorem m4_inner_iff' (x : D.Γ.Crossing) : D.Γ.crossingPoint x ∈ interior C.U ↔ x = B.y ∨ x = B.z := by
  sorry

/-- **Sub-leaf (U-M4).**  The reduced diagram has no crossing inside `U` (`m3_crossingPoint_origCrossing` +
`m4_inner_iff'` + `m3_origCrossing_ne_y/z`). -/
theorem m4_no_inner (x' : C.shadow.Crossing) : C.shadow.crossingPoint x' ∉ interior C.U := by
  sorry

/-- **Sub-leaf (U-M4).**  `y` is a crossing between the two arcs (its `e_in`-occurrence at `t_y ∈ (t_p, 1)`
is an inner point of `arcIn`, its `s`-occurrence at `t_sy ∈ (t_in, t_out)` an inner point of `arcS`). -/
theorem m4_sep_y : D.Separates (arcIn C) (arcS C) B.y := by
  sorry

theorem m4_sep_z : D.Separates (arcIn C) (arcS C) B.z := by
  sorry

/-- **Sub-leaf (U-M4).**  The common over strand: `B.same_over` read on the arcs. -/
theorem m4_same_over :
    (D.OverOn (arcIn C) B.y ∧ D.OverOn (arcIn C) B.z) ∨ (D.OverOn (arcS C) B.y ∧ D.OverOn (arcS C) B.z) := by
  sorry

/-! ### 1c.7 The outside match (unit U-M5) -/

/-- the traversal point of `D` under a traversal point of the reduced shadow: the original strand at the
rescaled parameter (`origParam`; junk on the middle edge, which is never outside `U`) -/
noncomputable def origPt (q : C.shadow.Pt) : D.Γ.Pt :=
  ⟨(B.orig C.tM C.tq ⟨q.1, q.2.1⟩).1, ((B.orig C.tM C.tq ⟨q.1, q.2.1⟩).2,
    clampIco ((B.kind C.tM C.tq ⟨q.1, q.2.1⟩).origParam C.tM C.tq q.2.2.val))⟩

/-- `orig` keeps the component -/
theorem orig_fst (u : C.shadow.Strand) : (B.orig C.tM C.tq u).1 = u.1 := by
  refine B.strand_cases C.tM C.tq ?_ ?_ u
  · intro m hm
    unfold orig
    rw [B.kind_mk_i _ _ _ hm]
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m <;> rfl
    · rw [kindIdx_of_ge _ h3]; rfl
  · intro i' h m hm
    unfold orig
    rw [B.kind_mk_of_ne _ _ h m hm]; rfl

/-- **Sub-leaf (U-M5).**  The move match: `φ := origPt` on the outside points (bijective onto `D`'s outside
points: old strands identically, `cutIn ↦ e_in` on `[0, t_p]`, `cutOut ↦ e_out` on `[t_q, 1]`, `s` identically;
`eval_eq`, `dir_pos` / `dir_pos_before` by the positive rescaling `Kind.dir_eq_smul_orig`), `ψ :=` the crossing
bijection `crossingEquiv` (every crossing of `D'` is outer, the outer crossings of `D` are those `≠ y, z`),
`e := Equiv.refl` (`orig_fst`); `over_eq` / `under_eq` from `orig_overStrand'` and `m3_crossingParam`. -/
theorem m5_moveMatch : Nonempty (MoveMatch C.U (B.reducedDiagram C) D) := by
  sorry

/-! ### 1c.8 The record bridge (unit U-M6) -/

/-- the occurrence of `D` under an occurrence of the reduced diagram -/
noncomputable def origVisit (v : C.shadow.Visit) : D.Γ.Visit :=
  ⟨origCrossing C v.1, ⟨B.orig C.tM C.tq v.2.val, orig_mem_origCrossing C v.2.2⟩⟩

theorem origVisit_fst (v : C.shadow.Visit) : (origVisit C v).1 = origCrossing C v.1 := rfl

theorem origVisit_injective : Function.Injective (origVisit C) := by
  intro v w h
  obtain ⟨y, u, hu⟩ := v
  obtain ⟨y', u', hu'⟩ := w
  have h1 : origCrossing C y = origCrossing C y' := congrArg Sigma.fst h
  have hyy := m3_origCrossing_injective C h1
  subst hyy
  have h2 : B.orig C.tM C.tq u = B.orig C.tM C.tq u' := congrArg (fun z : D.Γ.Visit => z.2.val) h
  have huu := m3_orig_injOn_crossing C y hu hu' h2
  subst huu
  rfl

variable (B) in
/-- the retained occurrences of `reducedRecord` are those at crossings other than `y, z` -/
theorem crossKeep_keep_iff (v : D.Γ.Visit) : D.record.CrossKeep B.keep v ↔ v.1 ≠ B.y ∧ v.1 ≠ B.z := by
  have key : ∀ x : D.Γ.Crossing,
      D.record.crossingOf v = D.record.crossingOf (D.overVisit x) ↔ v.1 = x := by
    intro x
    rw [Record.crossingOf_eq_iff]
    show v ∈ ({D.overVisit x, D.record.pair (D.overVisit x)} : Finset D.Γ.Visit) ↔ _
    rw [D.record_pair_apply, D.mem_pair_twin_iff]
    rfl
  show (¬ D.record.crossingOf v = D.record.crossingOf (D.overVisit B.y) ∧
    ¬ D.record.crossingOf v = D.record.crossingOf (D.overVisit B.z)) ↔ (¬ v.1 = B.y ∧ ¬ v.1 = B.z)
  rw [key, key]

theorem origVisit_keep (v : C.shadow.Visit) : D.record.CrossKeep B.keep (origVisit C v) :=
  (B.crossKeep_keep_iff _).mpr ⟨m3_origCrossing_ne_y C v.1, m3_origCrossing_ne_z C v.1⟩

/-- **Sub-leaf (U-M6).**  Every retained occurrence of `D` is the image of an occurrence of the reduced
diagram (`m3_exists_lift` + the strand lift `strandOf (old e)` / `cutIn` / `cutOut`). -/
theorem m6_exists_origVisit (w : D.Γ.Visit) (hw : D.record.CrossKeep B.keep w) :
    ∃ v : C.shadow.Visit, origVisit C v = w := by
  sorry

/-- **The occurrence bijection** `Ψ : D'.Visit ≃ {v // v.1 ≠ y ∧ v.1 ≠ z}` (= the occurrences of
`reducedRecord`), assembled from the sub-leaves. -/
noncomputable def visitEquiv : C.shadow.Visit ≃ {w : D.Γ.Visit // D.record.CrossKeep B.keep w} :=
  Equiv.ofBijective (fun v => ⟨origVisit C v, origVisit_keep C v⟩)
    ⟨fun v w h => origVisit_injective C (congrArg Subtype.val h),
     fun w => by
      obtain ⟨v, hv⟩ := m6_exists_origVisit C w.1 w.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem compOf_origVisit (v : C.shadow.Visit) : D.compOf (origVisit C v) = (B.reducedDiagram C).compOf v :=
  orig_fst C v.2.val

/-- twins correspond -/
theorem twin_origVisit (v : C.shadow.Visit) :
    D.twin (origVisit C v) = origVisit C ((B.reducedDiagram C).twin v) := by
  have hmem : B.orig C.tM C.tq (C.shadow.other v.1 v.2.2) ∈ (origCrossing C v.1).val :=
    orig_mem_origCrossing C (C.shadow.other_mem v.1 v.2.2)
  have hne : B.orig C.tM C.tq (C.shadow.other v.1 v.2.2) ≠ B.orig C.tM C.tq v.2.val := fun h =>
    C.shadow.other_ne v.1 v.2.2 (m3_orig_injOn_crossing C v.1 (C.shadow.other_mem v.1 v.2.2) v.2.2 h)
  have h := D.Γ.eq_other_of_mem_of_ne (origCrossing C v.1) (orig_mem_origCrossing C v.2.2) hmem hne
  exact congrArg (fun t : {s // s ∈ (origCrossing C v.1).val} => (⟨origCrossing C v.1, t⟩ : D.Γ.Visit))
    (Subtype.ext h.symm)

/-- over bits correspond -/
theorem overBit_origVisit (v : C.shadow.Visit) :
    (B.reducedDiagram C).overBit v = D.overBit (origVisit C v) := by
  have hov := orig_overStrand' C v.1
  by_cases h : v.2.val = overStrand' C v.1
  · have e1 : (B.reducedDiagram C).overBit v = true := decide_eq_true h
    have e2 : D.overBit (origVisit C v) = true := by
      apply decide_eq_true
      show B.orig C.tM C.tq v.2.val = D.overStrand (origCrossing C v.1)
      rw [h]; exact hov
    rw [e1, e2]
  · have e1 : (B.reducedDiagram C).overBit v = false := decide_eq_false h
    have e2 : D.overBit (origVisit C v) = false := by
      apply decide_eq_false
      intro heq
      exact h (m3_orig_injOn_crossing C v.1 v.2.2 (overStrand'_mem C v.1) (heq.trans hov.symm))
    rw [e1, e2]

/-- signs correspond -/
theorem sign_origVisit (v : C.shadow.Visit) :
    (B.reducedDiagram C).sign v.1 = D.sign (origVisit C v).1 :=
  m3_sign C v.1

/-- **The traversal key of U-M6**: on component `i` the traversal coordinate of `D` rotated so that `M₀` (the
tail of `e_in`, label `a`) sits at `0` (`rexB_rot k a.val`); elsewhere the plain coordinate.  On the retained
occurrences of component `i` it is a strictly increasing function of the reduced coordinate: the blocks
`[0, t_p)` (on `e_in`, mapped to `cutIn` by `· / t_M`), `[j + t_q, j + 1)` (on `e_out`, mapped to `cutOut`) and
`[j + 1, k)` (old edges, shifted by `−(j − 2)`) come in this order (`lt_iff_of_blocks`). -/
noncomputable def key (v : D.Γ.Visit) : ℝ :=
  if D.compOf v = B.i then rexB_rot (B.k : ℝ) (B.a.val : ℝ) (D.visitCoord v) else D.visitCoord v

/-- **Sub-leaf (U-M6).**  The reduced coordinate compares like the key on the same component. -/
theorem m6_key_lt_iff (v w : C.shadow.Visit) (h : (B.reducedDiagram C).compOf v = (B.reducedDiagram C).compOf w) :
    (B.reducedDiagram C).visitCoord v < (B.reducedDiagram C).visitCoord w ↔
      B.key (origVisit C v) < B.key (origVisit C w) := by
  sorry

/-- **Sub-leaf (U-M6).**  The successor of the reduced diagram is the first return of `D`'s successor to the
retained occurrences (`cycNext_unique_on` on the key; `nextVisit_no_between`, `firstReturn_no_between`;
the rotation `rexB_rot` preserves `cycBetween`). -/
theorem m6_succ (v : C.shadow.Visit) :
    origVisit C ((B.reducedDiagram C).nextVisit v) =
      (firstReturn D.visitSucc (D.record.CrossKeep B.keep) ⟨origVisit C v, origVisit_keep C v⟩).1 := by
  sorry

/-- **The record isomorphism of the deletion** (assembled from the U-M6 sub-leaves): `e = id` on the
`c` circles, `Φ = visitEquiv`. -/
noncomputable def recordIso : RecordIso (B.reducedDiagram C).record B.reducedRecord where
  e := Equiv.refl _
  Φ := visitEquiv C
  comp_eq v := compOf_origVisit C v
  succ_eq v := Subtype.ext (m6_succ C v)
  pair_eq v := Subtype.ext (twin_origVisit C v).symm
  bit_eq v := (overBit_origVisit C v).symm
  sgn_eq v := (sign_origVisit C v).symm

/-- **Leaf of U-M6 (assembled).** -/
theorem m6_recordIso : Nonempty (RecordIso (B.reducedDiagram C).record B.reducedRecord) := ⟨recordIso C⟩

/-! ### 1c.9 The assembly (unit U-M7) -/

/-- **The R-II site** `RIIData U D' D`: the reduced diagram is the crossing-free side, `D` the side with the
two crossings `y, z`.  Every field is a sub-leaf of U-M4/U-M5 or proved above. -/
noncomputable def m7_riiData : RIIData C.U (B.reducedDiagram C) D where
  frame := ⟨C.disc, m4_clean' C, m4_clean C⟩
  out := (m5_moveMatch C).some
  a := arcIn' C
  b := arcS' C
  a' := arcIn C
  b' := arcS C
  ab := m4_arcIn'_ne_arcS' C
  ab' := m4_arcIn_ne_arcS C
  cover := m4_arcCover' C
  cover' := m4_arcCover C
  a_start := (eval_arcIn_start C).trans (eval_arcIn'_start C).symm
  a_stop := (eval_arcIn_stop C).trans (eval_arcIn'_stop C).symm
  b_start := (eval_arcS_start C).trans (eval_arcS'_start C).symm
  b_stop := (eval_arcS_stop C).trans (eval_arcS'_stop C).symm
  no_inner := m4_no_inner C
  x₁ := B.y
  x₂ := B.z
  ne := B.y_ne_z
  inner_iff' := m4_inner_iff' C
  sep₁ := m4_sep_y C
  sep₂ := m4_sep_z C
  same_over := m4_same_over C

/-- the move itself -/
theorem m7_rii : RII (B.reducedDiagram C) D := ⟨C.U, Or.inl ⟨m7_riiData C⟩⟩

end Construction

end BigonData
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
  obtain ⟨C⟩ := B.m1_exists_cut
  exact ⟨B.reducedDiagram C, BigonData.m7_rii C, BigonData.reducedDiagram_componentCount C,
    BigonData.m6_recordIso C⟩

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


/-! ## Site 174 (Wave 2, I-174): the `m`-corner bigon on the `E`-side carrier diagram

Prover of unit I-174, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the
prefix `s174_`.  The plan is PLAN_FINAL.md §4.2: on `D_H := carrierDiagram hn hG' hSm' (τ qAB)` (the
positive lift of the corner polygon of the `E-b` carrier) the selected crossing `m'` is a corner of the
corner polygon, its two incident edges are the pieces of `ℓ₃`/`ℓ₁` (or `ℓ₁`/`ℓ₃`) through the adjacent
visits `w'(ℓ₃)`, `x'(ℓ₁)`, and the remote strand is the `ℓ₂`-piece through `w'(ℓ₂), x'(ℓ₂)`; `K` is the
closed contact triangle `conv{x', m', w'}`.  The site is built in two layers: a generic core
(`s174_core`, on any `CarrierGeometry` polygon, independent support, carrier and selected corner) and
the `GT_Endpoint` wrapper (`s174_site`), which derives the traversal order at the corner from the
canonical sign condition. -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

variable {n : ℕ} [NeZero n]

theorem s174_pos_over_iff {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (Γ.positiveDiagram hΓ).overStrand x = s ↔ 0 < det (Γ.dir s) (Γ.dir t) := by
  have hpos : 0 < det (Γ.dir ((Γ.positiveDiagram hΓ).overStrand x))
      (Γ.dir ((Γ.positiveDiagram hΓ).underStrand x)) := Γ.positiveDiagram_det_pos hΓ x
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  have hmem : (Γ.positiveDiagram hΓ).overStrand x ∈ ({s, t} : Finset Γ.Strand) := by
    rw [← hx]; exact (Γ.positiveDiagram hΓ).over_mem x
  constructor
  · intro h
    have hu : (Γ.positiveDiagram hΓ).underStrand x = t :=
      ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x ht
        (fun heq => hst.symm (heq.trans h))).symm
    rw [h, hu] at hpos
    exact hpos
  · intro hdet
    rcases Finset.mem_insert.mp hmem with h | h
    · exact h
    · exfalso
      have h' : (Γ.positiveDiagram hΓ).overStrand x = t := Finset.mem_singleton.mp h
      have hu : (Γ.positiveDiagram hΓ).underStrand x = s :=
        ((Γ.positiveDiagram hΓ).eq_under_of_mem_of_ne x hs (fun heq => hst (heq.trans h'))).symm
      rw [h', hu, det_swap] at hpos
      linarith

theorem s174_switch_over_self_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) :
    (D.switch x).overStrand x = s ↔ D.overStrand x = t := by
  have hs : s ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
  have ht : t ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [D.switch_overStrand_self]
  constructor
  · intro h
    exact (D.eq_over_of_mem_of_ne x ht (by rw [h]; exact hst.symm)).symm
  · intro h
    exact (D.eq_under_of_mem_of_ne x hs (by rw [h]; exact hst)).symm

omit [NeZero n] in
theorem s174_exact_symm {P P' : LabelledTuple n} {e f g : ZMod n}
    (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
    (hX : ExactTriangleVisitOrders P P' e f g hs) :
    ExactTriangleVisitOrders P' P e f g (fun s => (hs s).symm) := by
  intro v w he
  have h1 := hX ((visitTransport hs).symm w) ((visitTransport hs).symm v) he.symm
  have h2 := hX ((visitTransport hs).symm v) ((visitTransport hs).symm w) he
  rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h1 h2
  refine ⟨fun hu => ?_, fun hu => ?_⟩
  · have hu' : ((visitTransport hs).symm w).1.val ∪ ((visitTransport hs).symm v).1.val =
        {e, f, g} := by
      rw [Finset.union_comm]; exact hu
    exact (h1.1 hu').symm
  · exact (h2.2 hu).symm

section S174Core

variable {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CarrierGeometry P)
  (hs' : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {h_in h_s h_out : ZMod n}
  (hcef : IsCrossing P {h_in, h_s}) (hceg : IsCrossing P {h_in, h_out})
  (hcfg : IsCrossing P {h_s, h_out})
  {S : Finset (Crossing P)} (hS : GeoIndependent hG.cg S) (q : GeoComponent hG.cg S)

omit [NeZero n] in
theorem s174_ne_of_isCrossing {i j : ZMod n} (h : IsCrossing P {i, j}) : i ≠ j :=
  P1.ne_of_isCrossing_pair h

omit [NeZero n] in
theorem s174_triple_perm_gef' : ({h_out, h_in, h_s} : Finset (ZMod n)) = {h_in, h_s, h_out} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

omit [NeZero n] in
theorem s174_triple_perm_feg' : ({h_s, h_in, h_out} : Finset (ZMod n)) = {h_in, h_s, h_out} := by
  ext x; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto

include hcfg in
/-- adjacency of `y_in`, `c_in` on `h_in` in parameter form -/
theorem s174_adj_in (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vef hcef).2.val) :
    ¬ (visitParameter (G11_vef hcef) < visitParameter y ∧
        visitParameter y < visitParameter (G11_veg hceg)) ∧
    ¬ (visitParameter (G11_veg hceg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vef hcef)) :=
  G11_no_visit_between hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hX y hy

include hcef in
/-- adjacency of `c_out`, `z_out` on `h_out` -/
theorem s174_adj_out (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vge hceg).2.val) :
    ¬ (visitParameter (G11_vge hceg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vgf hcfg)) ∧
    ¬ (visitParameter (G11_vgf hcfg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vge hceg)) := by
  have hX' : ExactTriangleVisitOrders P P' h_out h_in h_s hs' :=
    gu2_exact_of_eq hs' s174_triple_perm_gef'.symm hX
  have h := G11_no_visit_between hs' (s174_ne_of_isCrossing hceg).symm
    (s174_ne_of_isCrossing hcfg).symm (s174_ne_of_isCrossing hcef)
    (gu2_isCrossing_comm hceg) (gu2_isCrossing_comm hcfg) hX' y hy
  have e1 : (⟨xPair (gu2_isCrossing_comm hceg), ⟨h_out, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vge hceg := gu2_visit_congr (gu2_xPair_comm hceg) _ _
  have e2 : (⟨xPair (gu2_isCrossing_comm hcfg), ⟨h_out, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vgf hcfg := gu2_visit_congr (gu2_xPair_comm hcfg) _ _
  rw [e1, e2] at h
  exact h

include hceg in
/-- adjacency of `y_s`, `z_s` on `h_s` -/
theorem s174_adj_s (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs') (y : Visit P)
    (hy : y.2.val = (G11_vfe hcef).2.val) :
    ¬ (visitParameter (G11_vfe hcef) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vfg hcfg)) ∧
    ¬ (visitParameter (G11_vfg hcfg) < visitParameter y ∧
        visitParameter y < visitParameter (G11_vfe hcef)) := by
  have hX' : ExactTriangleVisitOrders P P' h_s h_in h_out hs' :=
    gu2_exact_of_eq hs' s174_triple_perm_feg'.symm hX
  have h := G11_no_visit_between hs' (s174_ne_of_isCrossing hcef).symm
    (s174_ne_of_isCrossing hcfg) (s174_ne_of_isCrossing hceg)
    (gu2_isCrossing_comm hcef) hcfg hX' y hy
  have e1 : (⟨xPair (gu2_isCrossing_comm hcef), ⟨h_s, mem_pair_left _ _⟩⟩ : Visit P) =
      G11_vfe hcef := gu2_visit_congr (gu2_xPair_comm hcef) _ _
  rw [e1] at h
  exact h

include hn hcfg in
/-- the marked-circle successor of `y_in` is `c_in` -/
theorem s174_markSucc_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg)) :
    geoMarkSuccessor hG.cg (Sum.inr (G11_vef hcef)) = Sum.inr (G11_veg hceg) :=
  gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hord
    (fun y hy => (s174_adj_in hs' hcef hceg hcfg hX y hy).1)

include hn hcef in
theorem s174_markSucc_cout (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg)) :
    geoMarkSuccessor hG.cg (Sum.inr (G11_vge hceg)) = Sum.inr (G11_vgf hcfg) :=
  gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hord
    (fun y hy => (s174_adj_out hs' hcef hceg hcfg hX y hy).1)

include hn hcfg in
/-- `ρ_S y_in = c_in` -/
theorem s174_succ_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q) :
    geoSmoothingSuccessor hG.cg S (Sum.inr (G11_vef hcef)) = Sum.inr (G11_veg hceg) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hG.cg S _
    ((mem_geoCarrierCrossings hG.cg S q _).mp hy).1]
  exact s174_markSucc_yin hn hG hs' hcef hceg hcfg hX hord

include hn hcef in
/-- `ρ_S c_in = z_out` (the selected corner: leave along the twin's edge) -/
theorem s174_succ_cin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) :
    geoSmoothingSuccessor hG.cg S (Sum.inr (G11_veg hceg)) = Sum.inr (G11_vgf hcfg) := by
  rw [geoSmoothingSuccessor_visit_of_mem hG.cg S _ hcS, gu2_visitTwin_veg]
  exact s174_markSucc_cout hn hG hs' hcef hceg hcfg hX hord

include hn hcef in
/-- the incoming visit of the corner is owned by `q` -/
theorem s174_owner_cin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q) :
    geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q := by
  rw [← geoOwner_successor, s174_succ_cin hn hG hs' hcef hceg hcfg hX hord hcS]
  exact ((mem_geoCarrierCrossings hG.cg S q _).mp hz).2 _ rfl

/-- the corner index of the selected visit `c_in` on the carrier `q` -/
noncomputable def s174_k₀ (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    ZMod (geoCornerCount hG.cg S q) :=
  Classical.choose (geoCornerMark_exists_of_owner hG.cg S q _ hown hcS)

theorem s174_k₀_spec (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    geoCornerMark hG.cg S q (s174_k₀ hG hceg q hown hcS) = Sum.inr (G11_veg hceg) :=
  Classical.choose_spec (geoCornerMark_exists_of_owner hG.cg S q _ hown hcS)

/-- the corner point is the double point of `c` -/
theorem s174_cornerPolygon_k₀ (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) (hcS : xPair hceg ∈ S) :
    geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) = crossingPoint (xPair hceg) := by
  rw [geoCornerPolygon_apply, s174_k₀_spec, geoMarkPosition_evaluation_visit]
  rfl

include hn hcef in
/-- the carrier edge through `z_out` is the outgoing edge `k₀` of the corner -/
theorem s174_carrierEdge_zout (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hcS : xPair hceg ∈ S) (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) :
    G11_carrierEdge hn hG hS q (G11_vgf hcfg) hz = s174_k₀ hG hceg q hown hcS := by
  obtain ⟨r, hr, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vgf hcfg) hz
  have hsucc := s174_succ_cin hn hG hs' hcef hceg hcfg hX hord hcS
  have h1 : (geoSmoothingSuccessor hG.cg S ^ 1) (geoCornerMark hG.cg S q (s174_k₀ hG hceg q hown hcS)) =
      Sum.inr (G11_vgf hcfg) := by
    rw [pow_one, s174_k₀_spec]; exact hsucc
  have hb1 : GeoBlockInterior hG.cg S q (s174_k₀ hG hceg q hown hcS) 1 := by
    intro i hi1 hi
    have hi' : i = 1 := by omega
    subst hi'
    refine ⟨G11_vgf hcfg, h1, ((mem_geoCarrierCrossings hG.cg S q _).mp hz).1, ?_⟩
    rw [s174_k₀_spec, geoOutSlot_selected hG.cg S _ hcS, gu2_visitTwin_veg]
    rfl
  exact (geo_block_mark_eq hG.cg S q hb hb1 (hρ.trans h1.symm)).1

include hn hcfg in
/-- the carrier edge through `y_in` is the incoming edge `k₀ - 1` of the corner -/
theorem s174_carrierEdge_yin (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hord : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q) :
    G11_carrierEdge hn hG hS q (G11_vef hcef) hy + 1 = s174_k₀ hG hceg q hown hcS := by
  obtain ⟨r, hr, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hS q (G11_vef hcef) hy
  have hsucc := s174_succ_yin hn hG hs' hcef hceg hcfg q hX hord hy
  set j := G11_carrierEdge hn hG hS q (G11_vef hcef) hy with hj
  obtain ⟨m, hm, hchain, hmid, -, -, -, -, -⟩ := geoCornerPolygon_block hn hG.cg hS q j
  have hρ1 : (geoSmoothingSuccessor hG.cg S ^ (r + 1)) (geoCornerMark hG.cg S q j) =
      Sum.inr (G11_veg hceg) := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρ]; exact hsucc
  have hm_eq : m = r + 1 := by
    rcases lt_trichotomy m (r + 1) with hlt | heq | hgt
    · exfalso
      have hnc := hb.not_trueCorner hG.cg S q m hm (by omega)
      rw [hchain] at hnc
      exact hnc (isTrueCorner_geoCornerMark hG.cg S q (j + 1))
    · exact heq
    · exfalso
      obtain ⟨v, hv, hvS, -⟩ := hmid (r + 1) (by omega) hgt
      rw [hρ1] at hv
      have hv' : G11_veg hceg = v := Sum.inr.inj hv
      apply hvS
      rw [← hv']
      exact hcS
  rw [hm_eq, hρ1] at hchain
  exact geoCornerMark_injective hG.cg S q (hchain.symm.trans (s174_k₀_spec hG hceg q hown hcS).symm)


/-! ### The shadow crossings of the carrier lift at the two retained crossings -/

/-- the crossing of the carrier shadow sitting at a retained crossing `c` of the carrier -/
noncomputable def s174_lift (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).Crossing :=
  (geoCarrierCrossingEquiv hn hG hS q).symm ⟨c, hc⟩

theorem s174_lift_congr {c c' : Crossing P} (h : c = c') (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) :
    s174_lift hn hG hS q c hc = s174_lift hn hG hS q c' hc' := by
  subst h; rfl

theorem s174_lift_crossingPoint (c : Crossing P) (hc : c ∈ geoCarrierCrossings hG.cg S q) :
    (geoCarrierShadow hn hG hS q).crossingPoint (s174_lift hn hG hS q c hc) = crossingPoint c := by
  have h := crossingPoint_geoCarrierCrossingEquiv hn hG hS q (s174_lift hn hG hS q c hc)
  rw [s174_lift, Equiv.apply_symm_apply] at h
  exact h.symm

theorem s174_lift_injective_pt {c c' : Crossing P} (hc : c ∈ geoCarrierCrossings hG.cg S q)
    (hc' : c' ∈ geoCarrierCrossings hG.cg S q) (hne : c ≠ c') :
    s174_lift hn hG hS q c hc ≠ s174_lift hn hG hS q c' hc' := by
  intro h
  apply hne
  have := congrArg (geoCarrierShadow hn hG hS q).crossingPoint h
  rw [s174_lift_crossingPoint, s174_lift_crossingPoint] at this
  exact crossingPoint_injective_of_geometry hG.cg this

/-- the strands of the lifted crossing are the two carrier edges of the visits of `v.1` -/
theorem s174_lift_val (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (s174_lift hn hG hS q v.1 hv).val =
      {(⟨0, G11_carrierEdge hn hG hS q v hv⟩ : (geoCarrierShadow hn hG hS q).Strand),
       ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩} := by
  set Γ := geoCarrierShadow hn hG hS q with hΓ
  have hna : ¬ Γ.Adjacent ⟨0, G11_carrierEdge hn hG hS q v hv⟩
      ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    rw [Shadow.single_adjacent_iff]
    exact gu1_carrierEdge_remote hn hG hS q v hv hv'
  have hmem1 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (G11_carrierEdge_spec hn hG hS q v hv).1
  have hmem2 : crossingPoint v.1 ∈ Γ.seg ⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ := by
    have := (G11_carrierEdge_spec hn hG hS q (visitTwin v) hv').1
    rw [visitTwin_crossing] at this
    exact this
  let y₀ : Γ.Crossing := ⟨_, Γ.isCrossing_pair hna ⟨crossingPoint v.1, hmem1, hmem2⟩⟩
  have hpt : Γ.crossingPoint y₀ = crossingPoint v.1 := by
    symm
    apply (geoCarrierShadow_generic hn hG hS q).common_point_unique
    intro s hs
    rcases Finset.mem_insert.mp hs with rfl | hs
    · exact hmem1
    · rw [Finset.mem_singleton.mp hs]; exact hmem2
  have heq : s174_lift hn hG hS q v.1 hv = y₀ := by
    apply (geoCarrierShadow_generic hn hG hS q).crossingPoint_injective
    rw [s174_lift_crossingPoint, hpt]
  rw [heq]

/-! ### `k ≥ 4` -/

theorem s174_adjacent_zmod3 (i j : ZMod 3) : adjacent i j := by
  unfold adjacent
  have hv : ((j - i).val : ZMod 3) = j - i := ZMod.natCast_zmod_val (j - i)
  have hlt : (j - i).val < 3 := ZMod.val_lt (j - i)
  rw [← hv]
  generalize (j - i).val = d at hlt
  interval_cases d
  · right; left; rfl
  · right; right; rfl
  · left; decide

theorem s174_four_le {k : ℕ} (hk : 3 ≤ k) (h : ∃ i j : ZMod k, ¬ adjacent i j) : 4 ≤ k := by
  by_contra hlt
  have h3 : k = 3 := by omega
  subst h3
  obtain ⟨i, j, hij⟩ := h
  exact hij (s174_adjacent_zmod3 i j)

include hn hS in
theorem s174_four_le_cornerCount (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    4 ≤ geoCornerCount hG.cg S q :=
  s174_four_le (three_le_geoCornerCount hn hG hS q)
    ⟨_, _, gu1_carrierEdge_remote hn hG hS q v hv hv'⟩

/-! ### sign helpers -/

omit [NeZero n] in
theorem s174_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < a ↔ 0 < b := by
  rw [← sign_eq_one_iff, ← sign_eq_one_iff, h]

omit [NeZero n] in
theorem s174_det_ne_zero_of_isCrossing (hP : CrossingGeometry P) {i j : ZMod n}
    (h : IsCrossing P {i, j}) : det (edge P i) (edge P j) ≠ 0 :=
  (hP.2.1 i j (gu2_remote_of_isCrossing h) _ (crossingPoint_mem (xPair h) i (mem_pair_left i j))
    (crossingPoint_mem (xPair h) j (mem_pair_right i j))).2.2

omit [NeZero n] in
theorem s174_det_smul_pos_iff {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (u v : Plane) :
    0 < det (c • u) (d • v) ↔ 0 < det u v := by
  rw [gu2_det_smul_smul]
  exact ⟨fun h => pos_of_mul_pos_right h (mul_pos hc hd).le,
    fun h => mul_pos (mul_pos hc hd) h⟩


/-! ### the over strands of the positive lift at the two bigon crossings -/

include hn hS in
/-- at a lifted crossing `⟨0, j⟩, ⟨0, j'⟩` of the positive lift, the strand `⟨0, j'⟩` is over iff
`det (edge P e') (edge P e) > 0` for the original edges `e, e'` of the two visits -/
theorem s174_pos_over_lift_iff (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg S q)
    (hv' : (visitTwin v).1 ∈ geoCarrierCrossings hG.cg S q) :
    (geoPositiveLift hn hG hS q).overStrand (s174_lift hn hG hS q v.1 hv) =
        (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P (visitTwin v).2.val) (edge P v.2.val) := by
  have hval := s174_lift_val hn hG hS q v hv hv'
  rw [Finset.pair_comm] at hval
  have hne : (⟨0, G11_carrierEdge hn hG hS q (visitTwin v) hv'⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠
      ⟨0, G11_carrierEdge hn hG hS q v hv⟩ :=
    (geoCarrierShadow hn hG hS q).ne_of_not_adjacent
      (fun h => gu1_carrierEdge_remote hn hG hS q v hv hv'
        ((Shadow.single_adjacent_iff _ _ _).mp (Shadow.Adjacent.symm _ h)))
  refine (s174_pos_over_iff (geoCarrierShadow_generic hn hG hS q) _ hval hne).trans ?_
  obtain ⟨-, c, hc, he⟩ := G11_carrierEdge_spec hn hG hS q v hv
  obtain ⟨-, c', hc', he'⟩ := G11_carrierEdge_spec hn hG hS q (visitTwin v) hv'
  show 0 < det (edge (geoCornerPolygon hG.cg S q) _) (edge (geoCornerPolygon hG.cg S q) _) ↔ _
  rw [he, he']
  exact s174_det_smul_pos_iff hc' hc _ _


omit [NeZero n] in
theorem s174_not_pos_iff {a : ℝ} (ha : a ≠ 0) : ¬ 0 < a ↔ 0 < -a := by
  rw [not_lt, neg_pos]
  exact ⟨fun h => lt_of_le_of_ne h ha, le_of_lt⟩

omit [NeZero n] in
theorem s174_neg_pos_iff_of_sign_eq {a b : ℝ} (h : SignType.sign a = SignType.sign b) :
    0 < -a ↔ 0 < -b := by
  rw [neg_pos, neg_pos, ← sign_eq_neg_one_iff, ← sign_eq_neg_one_iff, h]

omit [NeZero n] in
/-- the over strand is the second strand iff it is not the first -/
theorem s174_over_other_iff (D : Diagram) (x : D.Γ.Crossing) {s t : D.Γ.Strand}
    (hx : x.val = {s, t}) (hst : s ≠ t) : D.overStrand x = t ↔ D.overStrand x ≠ s := by
  have hmem : D.overStrand x ∈ ({s, t} : Finset D.Γ.Strand) := by rw [← hx]; exact D.over_mem x
  constructor
  · intro h heq; exact hst (heq.symm.trans h)
  · intro h
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact absurd h' h
    · exact Finset.mem_singleton.mp h'

/-! ### the closed contact triangle and its clearance -/

/-- the closed contact triangle `conv{y, c, z}` -/
abbrev s174_K : Set Plane :=
  convexHull ℝ {crossingPoint (xPair hcef), crossingPoint (xPair hceg), crossingPoint (xPair hcfg)}

include hs' in
/-- a corner of the carrier polygon inside the closed triangle is the corner `c` itself -/
theorem s174_corner_mem_K (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (i : ZMod (geoCornerCount hG.cg S q))
    (hi : geoCornerPolygon hG.cg S q i ∈ s174_K hcef hceg hcfg) :
    geoCornerPolygon hG.cg S q i = crossingPoint (xPair hceg) := by
  have hcl := gu2_clear hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX
  have hcorner := isTrueCorner_geoCornerMark hG.cg S q i
  rw [geoCornerPolygon_apply] at hi ⊢
  rcases hmark : geoCornerMark hG.cg S q i with j | v
  · rw [hmark, geoMarkPosition_evaluation_vertex] at hi
    exact absurd hi (hcl.2 j)
  · rw [hmark] at hi hcorner
    rw [geoMarkPosition_evaluation_visit] at hi ⊢
    have hvS : v.1 ∈ S := hcorner
    by_cases hvc : v.1 = xPair hceg
    · rw [hvc]
    · exfalso
      obtain ⟨h, hh, h1, h2, h3⟩ := hK_sel v.1 hvS hvc
      exact gu2_clear_closed hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
        (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX h h1 h2 h3 _ (crossingPoint_mem v.1 h hh) hi

include hn hs' in
/-- **clearance**: every edge of the carrier polygon other than the three local ones misses the
closed contact triangle -/
theorem s174_clear (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hown : geoOwner hG.cg S (Sum.inr (G11_veg hceg)) = q)
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (hjy : G11_carrierEdge hn hG hS q (G11_vef hcef) hy + 1 = s174_k₀ hG hceg q hown hcS)
    (hjz : G11_carrierEdge hn hG hS q (G11_vgf hcfg) hz = s174_k₀ hG hceg q hown hcS)
    (hjs : G11_carrierEdge hn hG hS q (G11_vfg hcfg) hz = G11_carrierEdge hn hG hS q (G11_vfe hcef) hy)
    (h : ZMod (geoCornerCount hG.cg S q))
    (h1 : h ≠ G11_carrierEdge hn hG hS q (G11_vef hcef) hy)
    (h2 : h ≠ s174_k₀ hG hceg q hown hcS)
    (h3 : h ≠ G11_carrierEdge hn hG hS q (G11_vfe hcef) hy) :
    Disjoint (edgeSegment (geoCornerPolygon hG.cg S q) h) (s174_K hcef hceg hcfg) := by
  rw [Set.disjoint_left]
  intro x hx hxK
  have hx₀ := gu2_edgeSegment_sub hn hG hS q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hS q h
  have hcpt : geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) = crossingPoint (xPair hceg) :=
    s174_cornerPolygon_k₀ hG hceg q hown hcS
  have hjy' : G11_carrierEdge hn hG hS q (G11_vef hcef) hy = s174_k₀ hG hceg q hown hcS - 1 :=
    eq_sub_of_add_eq hjy
  -- a corner point of the triangle on the edge `h` is impossible
  have hcorner_case : ∀ i, x = geoCornerPolygon hG.cg S q i → False := by
    intro i hi
    have hi' := s174_corner_mem_K hG hs' hcef hceg hcfg q hX hK_sel i (hi ▸ hxK)
    have hmem : geoCornerPolygon hG.cg S q (s174_k₀ hG hceg q hown hcS) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) h := by
      rw [hcpt, ← hi', ← hi]; exact hx
    refine geoCornerPolygon_tail_off hn hG hS q _ h ?_ hmem
    rintro (hh | hh)
    · exact h1 (hh.trans hjy'.symm)
    · exact h2 hh
  by_cases hhe : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_in
  · rw [hhe] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_e_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hA, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vef hcef) hy
    have hB : crossingPoint (xPair hceg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (G11_carrierEdge hn hG hS q (G11_vef hcef) hy) := by
      rw [← hcpt, ← hjy]
      exact ⟨1, zero_le_one, le_rfl, (edgePoint_one _ _).symm⟩
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h1 hedge₀ hedge hx
      (gu2_edgeSegment_convex hA hB hseg)
    exact hcorner_case i hi
  by_cases hhf : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_s
  · rw [hhf] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_f_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hA, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vfe hcef) hy
    have hC : crossingPoint (xPair hcfg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (G11_carrierEdge hn hG hS q (G11_vfe hcef) hy) := by
      rw [← hjs]
      exact (G11_carrierEdge_spec hn hG hS q (G11_vfg hcfg) hz).1
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h3 hedge₀ hedge hx
      (gu2_edgeSegment_convex hA hC hseg)
    exact hcorner_case i hi
  by_cases hhg : (geoOutSlot hG.cg S (geoCornerMark hG.cg S q h)).1 = h_out
  · rw [hhg] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_g_mem_segment hG hcef hceg hcfg hxK hxt
    obtain ⟨hC, c, hc, hedge⟩ := G11_carrierEdge_spec hn hG hS q (G11_vgf hcfg) hz
    rw [hjz] at hC hedge
    have hB : crossingPoint (xPair hceg) ∈
        edgeSegment (geoCornerPolygon hG.cg S q) (s174_k₀ hG hceg q hown hcS) := by
      rw [← hcpt]
      exact ⟨0, le_rfl, zero_le_one, (edgePoint_zero _ _).symm⟩
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hS q h2 hedge₀ hedge hx
      (gu2_edgeSegment_convex hB hC hseg)
    exact hcorner_case i hi
  exact gu2_clear_closed hG hs' (s174_ne_of_isCrossing hcef) (s174_ne_of_isCrossing hceg)
    (s174_ne_of_isCrossing hcfg) hcef hceg hcfg hX _ hhe hhf hhg x hx₀ hxK



omit [NeZero n] in
/-- two strands of a one-component shadow with non-adjacent labels are distinct -/
theorem s174_strand_ne_of_not_adjacent {C : PolyComp} {j j' : ZMod C.k} (h : ¬ adjacent j j') :
    (⟨0, j⟩ : (Shadow.single C).Strand) ≠ ⟨0, j'⟩ := by
  intro heq
  apply h
  have hjj : j = j' := eq_of_heq (Sigma.mk.inj heq).2
  rw [hjj]
  exact Or.inr (Or.inl (sub_self _))

include hn hs' in
/-- **The core site theorem (row 174 / 176 shape).**  On the positive lift `D₀ = geoPositiveLift` of a
carrier `q` of an independent support `S` whose corner polygon passes through the selected crossing
`c = x_{in,out}` (entering along `h_in`, leaving along `h_out`) with the retained crossings
`y = x_{in,s}` just before the corner on `h_in` and `z = x_{s,out}` just after it on `h_out`, and the
canonical sign condition, the switch of `D₀` at `y` or at `z` carries a `BigonData` whose bigon is
`{y, z}` with `K` the closed contact triangle `conv{y, c, z}`.  Inputs: the R-LOC-2 adjacency in the
form `ExactTriangleVisitOrders` (A7), the ownership of `y, z` by `q`, and the clearance of the
triangle from the other selected crossings (`hK_sel`: every other selected crossing has an edge
outside `{h_in, h_s, h_out}`; the vertices and the other edges of `P` are cleared by G11's A8
`gu2_clear_closed`). -/
theorem s174_core (hX : ExactTriangleVisitOrders P P' h_in h_s h_out hs')
    (hcS : xPair hceg ∈ S) (hy : xPair hcef ∈ geoCarrierCrossings hG.cg S q)
    (hz : xPair hcfg ∈ geoCarrierCrossings hG.cg S q)
    (hK_sel : ∀ c' ∈ S, c' ≠ xPair hceg → ∃ h ∈ c'.val, h ≠ h_in ∧ h ≠ h_s ∧ h ≠ h_out)
    (hord_in : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg))
    (hord_out : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg))
    (hsgn : crossingSign P h_in h_s = crossingSign P h_s h_out)
    (xs : (geoCarrierShadow hn hG hS q).Crossing)
    (hxs : xs = s174_lift hn hG hS q _ hy ∨ xs = s174_lift hn hG hS q _ hz) :
    ∃ B : BigonData ((geoPositiveLift hn hG hS q).switch xs),
      B.i = ⟨0, Nat.one_pos⟩ ∧ B.y = s174_lift hn hG hS q _ hy ∧ B.z = s174_lift hn hG hS q _ hz := by
  -- the corner and the three carrier edges
  have hown := s174_owner_cin hn hG hs' hcef hceg hcfg q hX hord_out hcS hz
  have hjy := s174_carrierEdge_yin hn hG hs' hcef hceg hcfg hS q hX hord_in hcS hy hown
  have hjz := s174_carrierEdge_zout hn hG hs' hcef hceg hcfg hS q hX hord_out hcS hz hown
  have hjs : G11_carrierEdge hn hG hS q (G11_vfg hcfg) hz =
      G11_carrierEdge hn hG hS q (G11_vfe hcef) hy :=
    G11_carrierEdge_eq_of_adjacent hn hG hS q hz hy rfl
      (fun y hy' => (s174_adj_s hs' hcef hceg hcfg hX y hy').symm)
  have hcpt := s174_cornerPolygon_k₀ hG hceg q hown hcS
  set k₀ := s174_k₀ hG hceg q hown hcS with hk₀
  set jy := G11_carrierEdge hn hG hS q (G11_vef hcef) hy with hjy_def
  set js := G11_carrierEdge hn hG hS q (G11_vfe hcef) hy with hjs_def
  set ys := s174_lift hn hG hS q _ hy with hys
  set zs := s174_lift hn hG hS q _ hz with hzs
  have htwz : visitTwin (G11_vgf hcfg) = G11_vfg hcfg :=
    SEL_visitTwin_visitOn (mem_pair_left h_s h_out) (mem_pair_right h_s h_out)
      (s174_ne_of_isCrossing hcfg)
  -- the strands of the two lifted crossings
  have hyv : ys.val = {(⟨0, jy⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s174_lift_val hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy] at h
    exact h
  have hzv : zs.val = {(⟨0, k₀⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, js⟩} := by
    have h := s174_lift_val hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, hjz] at h
    exact h
  have hna_y : ¬ adjacent jy js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy] at h
    exact h
  have hna_z : ¬ adjacent k₀ js := by
    have h := gu1_carrierEdge_remote hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, hjz] at h
    exact h
  have hne_y : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, jy⟩ :=
    s174_strand_ne_of_not_adjacent (fun h => hna_y (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hne_z : (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ≠ ⟨0, k₀⟩ :=
    s174_strand_ne_of_not_adjacent (fun h => hna_z (by
      rcases h with h | h | h
      · exact Or.inr (Or.inr (by linear_combination -h))
      · exact Or.inr (Or.inl (by linear_combination -h))
      · exact Or.inl (by linear_combination -h)))
  have hyv' : ys.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, jy⟩} := by rw [hyv, Finset.pair_comm]
  have hzv' : zs.val = {(⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand), ⟨0, k₀⟩} := by rw [hzv, Finset.pair_comm]
  -- the two crossings are distinct
  have hyz_c : xPair hcef ≠ xPair hcfg := by
    intro h
    have hmem : h_in ∈ (xPair hcfg).val := by rw [← h]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h' | h'
    · exact s174_ne_of_isCrossing hcef h'
    · exact s174_ne_of_isCrossing hceg (Finset.mem_singleton.mp h')
  have hyz : ys ≠ zs := s174_lift_injective_pt hn hG hS q hy hz hyz_c
  -- the over strands of the positive lift at `y` and `z`
  have hA := s174_det_ne_zero_of_isCrossing hG.cg hcef
  have hB := s174_det_ne_zero_of_isCrossing hG.cg hcfg
  have hoy : (geoPositiveLift hn hG hS q).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < -det (edge P h_in) (edge P h_s) := by
    have h := s174_pos_over_lift_iff hn hG hS q (G11_vef hcef) hy hy
    rw [gu2_carrierEdge_congr hn hG hS q (gu2_visitTwin_vef hcef) hy hy, gu2_visitTwin_vef,
      det_swap] at h
    exact h
  have hoz : (geoPositiveLift hn hG hS q).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
      0 < det (edge P h_s) (edge P h_out) := by
    have h := s174_pos_over_lift_iff hn hG hS q (G11_vgf hcfg) hz hz
    rw [gu2_carrierEdge_congr hn hG hS q htwz hz hz, hjs, htwz] at h
    exact h
  have hsign : (0 < det (edge P h_in) (edge P h_s) ↔ 0 < det (edge P h_s) (edge P h_out)) :=
    s174_pos_iff_of_sign_eq hsgn
  have hsign' : (0 < -det (edge P h_in) (edge P h_s) ↔ 0 < -det (edge P h_s) (edge P h_out)) :=
    s174_neg_pos_iff_of_sign_eq hsgn
  -- `same_over` on the switched diagram
  have hsame : (((geoPositiveLift hn hG hS q).switch xs).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) ∨
      (((geoPositiveLift hn hG hS q).switch xs).overStrand ys ≠ (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ∧
        ((geoPositiveLift hn hG hS q).switch xs).overStrand zs ≠ (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand)) := by
    rcases hxs with rfl | rfl
    · -- the switch is at `y`
      have e1 : ((geoPositiveLift hn hG hS q).switch ys).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < det (edge P h_in) (edge P h_s) := by
        refine (s174_switch_over_self_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (s174_over_other_iff (geoPositiveLift hn hG hS q) ys hyv' hne_y).trans ?_
        refine (not_congr hoy).trans ?_
        rw [s174_not_pos_iff (neg_ne_zero.mpr hA), neg_neg]
      have e2 : ((geoPositiveLift hn hG hS q).switch ys).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < det (edge P h_s) (edge P h_out) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz.symm
        rw [h]
        exact hoz
      by_cases hp : 0 < det (edge P h_in) (edge P h_s)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign.mpr (e2.mp h))⟩
    · -- the switch is at `z`
      have e1 : ((geoPositiveLift hn hG hS q).switch zs).overStrand ys = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < -det (edge P h_in) (edge P h_s) := by
        have h := Diagram.switch_overStrand_of_ne (geoPositiveLift hn hG hS q) hyz
        rw [h]
        exact hoy
      have e2 : ((geoPositiveLift hn hG hS q).switch zs).overStrand zs = (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ↔
          0 < -det (edge P h_s) (edge P h_out) := by
        refine (s174_switch_over_self_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        refine (s174_over_other_iff (geoPositiveLift hn hG hS q) zs hzv' hne_z).trans ?_
        exact (not_congr hoz).trans (s174_not_pos_iff hB)
      by_cases hp : 0 < -det (edge P h_in) (edge P h_s)
      · exact Or.inl ⟨e1.mpr hp, e2.mpr (hsign'.mp hp)⟩
      · exact Or.inr ⟨fun h => hp (e1.mp h), fun h => hp (hsign'.mpr (e2.mp h))⟩
  -- clearance
  have hclear : ∀ u : (geoCarrierShadow hn hG hS q).Strand, u ≠ ⟨0, jy⟩ → u ≠ ⟨0, jy + 1⟩ → u ≠ ⟨0, js⟩ →
      Disjoint ((geoCarrierShadow hn hG hS q).seg u) (s174_K hcef hceg hcfg) := by
    rintro ⟨i₀, h⟩ h1 h2 h3
    obtain rfl : i₀ = 0 := Subsingleton.elim _ _
    have h1' : h ≠ jy := fun hh => h1 (by rw [hh])
    have h2' : h ≠ k₀ := fun hh => h2 (by rw [hh, ← hjy])
    have h3' : h ≠ js := fun hh => h3 (by rw [hh])
    exact s174_clear hn hG hs' hcef hceg hcfg hS q hX hcS hy hz hown hK_sel hjy hjz hjs h h1' h2' h3'
  have hk : 4 ≤ geoCornerCount hG.cg S q := s174_four_le_cornerCount hn hG hS q (G11_vef hcef) hy hy
  have hpy : (geoCarrierShadow hn hG hS q).crossingPoint ys = crossingPoint (xPair hcef) :=
    s174_lift_crossingPoint hn hG hS q _ hy
  have hpz : (geoCarrierShadow hn hG hS q).crossingPoint zs = crossingPoint (xPair hcfg) :=
    s174_lift_crossingPoint hn hG hS q _ hz
  have hK : convexHull ℝ {(geoCarrierShadow hn hG hS q).crossingPoint ys, geoCornerPolygon hG.cg S q (jy + 1),
      (geoCarrierShadow hn hG hS q).crossingPoint zs} = s174_K hcef hceg hcfg := by
    rw [hpy, hpz, hjy, hcpt]
  rw [← hjy] at hzv
  -- the triangle builder
  obtain ⟨B, hBi, hBy, hBz⟩ := exists_bigonData_of_triangle ((geoPositiveLift hn hG hS q).switch xs)
    ⟨0, Nat.one_pos⟩ jy hk (⟨0, js⟩ : (geoCarrierShadow hn hG hS q).Strand) ys zs hyv hzv hsame (by
      intro u h1 h2 h3
      have hK' : convexHull ℝ {((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint ys,
          (((geoPositiveLift hn hG hS q).switch xs).Γ.comp ⟨0, Nat.one_pos⟩).P
            ((jy + 1 : ZMod (geoCornerCount hG.cg S q))),
          ((geoPositiveLift hn hG hS q).switch xs).Γ.crossingPoint zs} = s174_K hcef hceg hcfg := by
        rw [← hK]; rfl
      exact (hclear u h1 h2 h3).mono_right (le_of_eq hK'))
  exact ⟨B, hBi, hBy, hBz⟩


end S174Core

/-! ### The `GT_Endpoint` wrapper: the traversal order at the `m`-corner from the sign condition -/

section S174Site

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}

omit [NeZero n] in
/-- the real-arithmetic core of the order lemma: from `a B = r C`, `r A = -(b B)` with `A, C` of one
sign and `B ≠ 0`, the numbers `a, b` (both nonzero) have opposite signs -/
theorem s174_order_alg {A B C a b r : ℝ} (hB : B ≠ 0) (hAC : 0 < A * C) (ha : a ≠ 0)
    (I1 : a * B = r * C) (I2 : r * A = -(b * B)) : 0 < a ↔ b < 0 := by
  have key : a * A + b * C = 0 := by
    have h3 : B * (a * A + b * C) = 0 := by linear_combination A * I1 + C * I2
    rcases mul_eq_zero.mp h3 with h | h
    · exact absurd h hB
    · exact h
  have hC : C ≠ 0 := right_ne_zero_of_mul hAC.ne'
  have hab : a * b < 0 := by
    have h4 : a * b * C ^ 2 = -(a ^ 2 * (A * C)) := by linear_combination (a * C) * key
    have h5 : 0 < a ^ 2 := lt_of_le_of_ne (sq_nonneg a) (Ne.symm (pow_ne_zero 2 ha))
    have h6 : 0 < a ^ 2 * (A * C) := mul_pos h5 hAC
    have h7 : 0 < C ^ 2 := lt_of_le_of_ne (sq_nonneg C) (Ne.symm (pow_ne_zero 2 hC))
    by_contra hcon
    have h8 : 0 ≤ a * b := not_lt.mp hcon
    nlinarith
  rcases mul_neg_iff.mp hab with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h (not_lt.mpr h1.le), fun h => absurd h (not_lt.mpr h2.le)⟩

omit [NeZero n] in
theorem s174_mul_pos_of_sign_eq {a b : ℝ} (ha : a ≠ 0) (h : SignType.sign a = SignType.sign b) :
    0 < a * b := by
  rcases lt_or_gt_of_ne ha with hneg | hpos
  · have hb : b < 0 := sign_eq_neg_one_iff.mp (h.symm.trans (sign_eq_neg_one_iff.mpr hneg))
    exact mul_pos_of_neg_of_neg hneg hb
  · have hb : 0 < b := sign_eq_one_iff.mp (h.symm.trans (sign_eq_one_iff.mpr hpos))
    exact mul_pos hpos hb

omit [NeZero n] in
theorem s174_param_congr {c c' : Crossing P} (h : c = c') {i : ZMod n} (hi : i ∈ c.val)
    (hi' : i ∈ c'.val) : crossingParameter c i hi = crossingParameter c' i hi' := by
  subst h; rfl

omit [NeZero n] in
/-- distinct crossings on one edge have distinct parameters (tier 0) -/
theorem s174_param_ne (hP : CrossingGeometry P) {ℓ : ZMod n} {c c' : Crossing P} (hne : c ≠ c')
    (hℓ : ℓ ∈ c.val) (hℓ' : ℓ ∈ c'.val) : crossingParameter c ℓ hℓ ≠ crossingParameter c' ℓ hℓ' := by
  intro h
  apply hne
  apply crossingPoint_injective_of_geometry hP
  rw [gu2_xpt c ℓ hℓ, gu2_xpt c' ℓ hℓ', h]

omit [NeZero n] in
theorem s174_xPair_ne_of_mem {a b b' : ZMod n} (h : IsCrossing P {a, b}) (h' : IsCrossing P {a, b'})
    (hbb : b ≠ b') : xPair h ≠ xPair h' := by
  intro heq
  have hmem : b ∈ (xPair h').val := by rw [← heq]; exact mem_pair_right _ _
  rcases Finset.mem_insert.mp hmem with h1 | h1
  · exact s174_ne_of_isCrossing h h1.symm
  · exact hbb (Finset.mem_singleton.mp h1)

omit [NeZero n] in
/-- **The order at the corner from the canonical sign condition.**  With `x' = x_{ℓ₁ℓ₂}`, `m' = x_{ℓ₁ℓ₃}`,
`w' = x_{ℓ₂ℓ₃}` and `sgn det(u₁,u₂) = sgn det(u₁,u₃) = sgn det(u₂,u₃)`: `m'` precedes `x'` on `ℓ₁` iff
`w'` precedes `m'` on `ℓ₃` (the corner polygon enters `m'` along `ℓ₃` and leaves along `ℓ₁`, or the
reverse). -/
theorem s174_order (hP : CrossingGeometry P) {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
    (hc12 : IsCrossing P {ℓ₁, ℓ₂}) (hc13 : IsCrossing P {ℓ₁, ℓ₃}) (hc23 : IsCrossing P {ℓ₂, ℓ₃})
    (hs12 : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hs23 : crossingSign P ℓ₂ ℓ₃ = crossingSign P ℓ₁ ℓ₃) :
    (crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) <
        crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) ↔
      crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _)) := by
  have hne12 : xPair hc12 ≠ xPair hc13 :=
    s174_xPair_ne_of_mem hc12 hc13 (s174_ne_of_isCrossing hc23)
  have ha := sub_ne_zero.mpr (s174_param_ne hP hne12 (mem_pair_left ℓ₁ ℓ₂) (mem_pair_left ℓ₁ ℓ₃))
  have hA := s174_det_ne_zero_of_isCrossing hP hc12
  have hB := s174_det_ne_zero_of_isCrossing hP hc13
  have hAC : 0 < det (edge P ℓ₁) (edge P ℓ₂) * det (edge P ℓ₂) (edge P ℓ₃) :=
    s174_mul_pos_of_sign_eq hA (hs12.trans hs23.symm)
  have ex1 := gu2_xpt (xPair hc12) ℓ₁ (mem_pair_left _ _)
  have ex2 := gu2_xpt (xPair hc12) ℓ₂ (mem_pair_right _ _)
  have em1 := gu2_xpt (xPair hc13) ℓ₁ (mem_pair_left _ _)
  have em3 := gu2_xpt (xPair hc13) ℓ₃ (mem_pair_right _ _)
  have ew2 := gu2_xpt (xPair hc23) ℓ₂ (mem_pair_left _ _)
  have ew3 := gu2_xpt (xPair hc23) ℓ₃ (mem_pair_right _ _)
  generalize crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) = tx at ex1 ha ⊢
  generalize crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) = tm at em1 ha ⊢
  generalize crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) = sm at em3 ⊢
  generalize crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) = sw at ew3 ⊢
  generalize crossingParameter (xPair hc12) ℓ₂ (mem_pair_right _ _) = rx at ex2
  generalize crossingParameter (xPair hc23) ℓ₂ (mem_pair_left _ _) = rw at ew2
  have hvec : (tx - tm) • edge P ℓ₁ - (sw - sm) • edge P ℓ₃ = (rx - rw) • edge P ℓ₂ := by
    rw [← gu2_edgePoint_sub, ← gu2_edgePoint_sub, ← gu2_edgePoint_sub, ← ex1, ← em1, ← ew3, ← em3,
      ← ex2, ← ew2]
    abel
  have h1 := congrArg Prod.fst hvec
  have h2 := congrArg Prod.snd hvec
  simp only [Prod.fst_sub, Prod.snd_sub, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at h1 h2
  have I1 : (tx - tm) * det (edge P ℓ₁) (edge P ℓ₃) = (rx - rw) * det (edge P ℓ₂) (edge P ℓ₃) := by
    unfold det; linear_combination (edge P ℓ₃).2 * h1 - (edge P ℓ₃).1 * h2
  have I2 : (rx - rw) * det (edge P ℓ₁) (edge P ℓ₂) = -((sw - sm) * det (edge P ℓ₁) (edge P ℓ₃)) := by
    unfold det; linear_combination (edge P ℓ₁).2 * h1 - (edge P ℓ₁).1 * h2
  have key := s174_order_alg hB hAC ha I1 I2
  rw [sub_pos, sub_neg] at key
  exact key

variable {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the three bundle labels of a `GT_Endpoint` configuration are `{e, f, g}` -/
theorem s174_labels_eq (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃) :
    ({ℓ₁, ℓ₂, ℓ₃} : Finset (ZMod n)) = {e, f, g} := by
  have hx := D.xT
  rw [D.xval] at hx
  have hw := D.wT
  rw [D.wval] at hw
  have hmem : ∀ a b : ZMod n, ({a, b} : Finset (ZMod n)) ∈ triangleSupports e f g →
      a ∈ ({e, f, g} : Finset (ZMod n)) ∧ b ∈ ({e, f, g} : Finset (ZMod n)) := by
    intro a b h
    unfold triangleSupports at h
    have ha : a ∈ ({a, b} : Finset (ZMod n)) := Finset.mem_insert_self _ _
    have hb : b ∈ ({a, b} : Finset (ZMod n)) := Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    simp only [Finset.mem_insert, Finset.mem_singleton] at h ⊢
    rcases h with h | h | h <;> rw [h] at ha hb <;>
      simp only [Finset.mem_insert, Finset.mem_singleton] at ha hb <;> tauto
  have h12 := hmem _ _ hx
  have h23 := hmem _ _ hw
  apply Finset.eq_of_subset_of_card_le
  · intro ℓ hℓ
    simp only [Finset.mem_insert, Finset.mem_singleton] at hℓ
    rcases hℓ with rfl | rfl | rfl
    · exact h12.1
    · exact h12.2
    · exact h23.2
  · rw [Finset.card_eq_three.mpr ⟨ℓ₁, ℓ₂, ℓ₃, D.l12, D.l13, D.l23, rfl⟩]
    exact Finset.card_le_three

/-- every selected crossing of the centre row other than `m'` has an edge outside the bundle -/
theorem s174_foreign_edge (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (c' : Crossing P') (hc' : c' ∈ transportSupport hs (Q ∪ {m}))
    (hne : c' ≠ crossingTransport hs m) :
    ∃ h ∈ c'.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃ := by
  obtain ⟨c₀, hc₀, rfl⟩ := Finset.mem_map.mp hc'
  have hc₀Q : c₀ ∈ Q := by
    rcases Finset.mem_union.mp hc₀ with h | h
    · exact h
    · exact absurd (congrArg (crossingTransport hs) (Finset.mem_singleton.mp h)) hne
  have hout := D.Q_out c₀ hc₀Q
  change ∃ h ∈ c₀.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃
  by_contra hcon
  apply hout
  have hlab : ∀ h ∈ c₀.val, h = e ∨ h = f ∨ h = g := by
    intro h hh
    have hℓ : h ∈ ({ℓ₁, ℓ₂, ℓ₃} : Finset (ZMod n)) := by
      by_contra hnot
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hnot
      exact hcon ⟨h, hh, hnot⟩
    rw [s174_labels_eq D] at hℓ
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hℓ
  obtain ⟨a, b, hab, hval⟩ := Finset.card_eq_two.mp (crossing_card_two c₀)
  have ha : a ∈ c₀.val := by rw [hval]; exact Finset.mem_insert_self _ _
  have hb : b ∈ c₀.val := by rw [hval]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hval]
  exact gu2_pair_mem_triangleSupports hab (hlab a ha) (hlab b hb)

end S174Site

/-! ### The site theorem on a `GT_Endpoint` configuration -/

section S174SiteMain

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the tier-1 carrier geometry of the `E`-side polygon, as `CV.carrierDiagram` reads it -/
abbrev s174_cg : CarrierGeometry P' := CarrierGeometry.ofDiagrammatic (hG'.diagrammatic hn)

/-- Sanity: `carrierDiagram` is the positive lift on `s174_cg`, definitionally. -/
theorem s174_carrierDiagram_eq {S' : Finset (Crossing P')} (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry S') :
    CV.carrierDiagram hn hG' hS' q' =
      geoPositiveLift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hS') q' := rfl

/-- **The site theorem of row 174 (PLAN_FINAL §4.2).**  On a `GT_Endpoint` configuration in the canonical
sign branch, for any carrier `q'` of the transported centre row that owns the visits of `x'` and `w'`
(the residual crossings `a, c` of the `E-b` carrier `AB'`), the switch of `D_H = carrierDiagram q'` at
`x'` carries a `BigonData` with bigon `{x', w'}` and `K` the closed contact triangle `conv{x', m', w'}`:
depending on the traversal direction at the corner `m'`, `(y, z) = (w', x')` (entering along `ℓ₃`) or
`(x', w')` (entering along `ℓ₁`).  `s174_lift` is the crossing of the carrier shadow at a retained crossing. -/
theorem s174_site (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    ∃ B : BigonData ((CV.carrierDiagram hn hG' hSm' q').switch
        (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')),
      B.i = ⟨0, Nat.one_pos⟩ ∧
      ((B.y = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw' ∧
        B.z = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') ∨
       (B.y = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx' ∧
        B.z = s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw')) := by
  have hs' : ∀ s, IsCrossing P' s ↔ IsCrossing P s := fun s => (hs s).symm
  have hc12 : IsCrossing P' {ℓ₁, ℓ₂} := (hs _).mp (D.xval ▸ x.property)
  have hc13 : IsCrossing P' {ℓ₁, ℓ₃} := (hs _).mp (D.mval ▸ m.property)
  have hc23 : IsCrossing P' {ℓ₂, ℓ₃} := (hs _).mp (D.wval ▸ w.property)
  have hX' : ExactTriangleVisitOrders P' P ℓ₁ ℓ₂ ℓ₃ hs' :=
    gu2_exact_of_eq hs' (s174_labels_eq D).symm (s174_exact_symm hs D.gauss)
  have hs12 : crossingSign P' ℓ₁ ℓ₂ = crossingSign P' ℓ₁ ℓ₃ := by
    rw [D.sign_eq _ _ (D.xval ▸ x.property), D.sign_eq _ _ (D.mval ▸ m.property)]
    exact hsgn
  have hs23 : crossingSign P' ℓ₂ ℓ₃ = crossingSign P' ℓ₁ ℓ₃ := by
    rw [D.sign_eq _ _ (D.wval ▸ w.property), D.sign_eq _ _ (D.mval ▸ m.property)]
    exact D.sgn
  have hxeq : crossingTransport hs x = xPair hc12 := Subtype.ext D.xval
  have hmeq : crossingTransport hs m = xPair hc13 := Subtype.ext D.mval
  have hweq : crossingTransport hs w = xPair hc23 := Subtype.ext D.wval
  have hmS : xPair hc13 ∈ transportSupport hs (Q ∪ {m}) := by
    rw [← hmeq]
    exact Finset.mem_map_of_mem _ (Finset.mem_union_right _ (Finset.mem_singleton_self m))
  have hx'' : xPair hc12 ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
    rw [← hxeq]; exact hx'
  have hw'' : xPair hc23 ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
    rw [← hweq]; exact hw'
  have hsel : ∀ c' ∈ transportSupport hs (Q ∪ {m}), c' ≠ xPair hc13 →
      ∃ h ∈ c'.val, h ≠ ℓ₁ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₃ :=
    fun c' hc' hne => s174_foreign_edge D c' hc' (by rw [hmeq]; exact hne)
  have hord := s174_order hG'.crossingGeometry hc12 hc13 hc23 hs12 hs23
  have hne_x : crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) ≠
      crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) :=
    s174_param_ne hG'.crossingGeometry (s174_xPair_ne_of_mem hc12 hc13 (s174_ne_of_isCrossing hc23)) _ _
  have hne_w : crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) ≠
      crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) := by
    refine s174_param_ne hG'.crossingGeometry ?_ _ _
    intro heq
    have hmem : ℓ₂ ∈ (xPair hc13).val := by rw [← heq]; exact mem_pair_left _ _
    rcases Finset.mem_insert.mp hmem with h1 | h1
    · exact s174_ne_of_isCrossing hc12 h1.symm
    · exact s174_ne_of_isCrossing hc23 (Finset.mem_singleton.mp h1)
  rcases lt_or_gt_of_ne hne_x with hlt | hgt
  · -- `x'` precedes `m'` on `ℓ₁`: the corner polygon enters along `ℓ₁`, leaves along `ℓ₃`; `(y, z) = (x', w')`
    have hsw : crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) := by
      rcases lt_or_gt_of_ne hne_w with h | h
      · exact absurd (hord.mpr h) (not_lt.mpr hlt.le)
      · exact h
    have hsgnC : crossingSign P' ℓ₁ ℓ₂ = crossingSign P' ℓ₂ ℓ₃ := hs12.trans hs23.symm
    obtain ⟨B, hBi, hBy, hBz⟩ := s174_core hn (s174_cg hn hG') hs' hc12 hc13 hc23
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' hX' hmS hx'' hw'' hsel hlt hsw hsgnC
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')
      (Or.inl (s174_lift_congr hn _ _ q' hxeq hx' hx''))
    exact ⟨B, hBi, Or.inr ⟨hBy.trans (s174_lift_congr hn _ _ q' hxeq.symm hx'' hx'),
      hBz.trans (s174_lift_congr hn _ _ q' hweq.symm hw'' hw')⟩⟩
  · -- `m'` precedes `x'` on `ℓ₁`: the corner polygon enters along `ℓ₃`, leaves along `ℓ₁`; `(y, z) = (w', x')`
    have hsw : crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) <
        crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) := hord.mp hgt
    have hcef : IsCrossing P' {ℓ₃, ℓ₂} := gu2_isCrossing_comm hc23
    have hceg : IsCrossing P' {ℓ₃, ℓ₁} := gu2_isCrossing_comm hc13
    have hcfg : IsCrossing P' {ℓ₂, ℓ₁} := gu2_isCrossing_comm hc12
    have hXA : ExactTriangleVisitOrders P' P ℓ₃ ℓ₂ ℓ₁ hs' :=
      gu2_exact_of_eq hs' (by ext y; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX'
    have e_ef : xPair hcef = xPair hc23 := gu2_xPair_comm hc23
    have e_eg : xPair hceg = xPair hc13 := gu2_xPair_comm hc13
    have e_fg : xPair hcfg = xPair hc12 := gu2_xPair_comm hc12
    have hsgnA : crossingSign P' ℓ₃ ℓ₂ = crossingSign P' ℓ₂ ℓ₁ := by
      rw [crossingSign_swap P' ℓ₂ ℓ₃, crossingSign_swap P' ℓ₁ ℓ₂, hs23, hs12]
    have hord_in : visitParameter (G11_vef hcef) < visitParameter (G11_veg hceg) := by
      have h1 : visitParameter (G11_vef hcef) = crossingParameter (xPair hc23) ℓ₃ (mem_pair_right _ _) :=
        s174_param_congr e_ef _ _
      have h2 : visitParameter (G11_veg hceg) = crossingParameter (xPair hc13) ℓ₃ (mem_pair_right _ _) :=
        s174_param_congr e_eg _ _
      rw [h1, h2]
      exact hsw
    have hord_out : visitParameter (G11_vge hceg) < visitParameter (G11_vgf hcfg) := by
      have h1 : visitParameter (G11_vge hceg) = crossingParameter (xPair hc13) ℓ₁ (mem_pair_left _ _) :=
        s174_param_congr e_eg _ _
      have h2 : visitParameter (G11_vgf hcfg) = crossingParameter (xPair hc12) ℓ₁ (mem_pair_left _ _) :=
        s174_param_congr e_fg _ _
      rw [h1, h2]
      exact hgt
    have hmS' : xPair hceg ∈ transportSupport hs (Q ∪ {m}) := by rw [e_eg]; exact hmS
    have hyA : xPair hcef ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
      rw [e_ef]; exact hw''
    have hzA : xPair hcfg ∈ geoCarrierCrossings (s174_cg hn hG').cg (transportSupport hs (Q ∪ {m})) q' := by
      rw [e_fg]; exact hx''
    have hselA : ∀ c' ∈ transportSupport hs (Q ∪ {m}), c' ≠ xPair hceg →
        ∃ h ∈ c'.val, h ≠ ℓ₃ ∧ h ≠ ℓ₂ ∧ h ≠ ℓ₁ := by
      intro c' hc' hne
      obtain ⟨h, hh, h1, h2, h3⟩ := hsel c' hc' (by rw [← e_eg]; exact hne)
      exact ⟨h, hh, h3, h2, h1⟩
    obtain ⟨B, hBi, hBy, hBz⟩ := s174_core hn (s174_cg hn hG') hs' hcef hceg hcfg
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' hXA hmS' hyA hzA hselA
      hord_in hord_out hsgnA
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx')
      (Or.inr (s174_lift_congr hn _ _ q' (hxeq.trans e_fg.symm) hx' hzA))
    exact ⟨B, hBi, Or.inl ⟨hBy.trans (s174_lift_congr hn _ _ q' (e_ef.trans hweq.symm) hyA hw'),
      hBz.trans (s174_lift_congr hn _ _ q' (e_fg.trans hxeq.symm) hzA hx')⟩⟩

end S174SiteMain

/-! ### (b) the record identification `hrec`, stated; (c) the `fulltwist` field from (a) + (b) -/

section S174Consumer

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- the reduced record of a bigon site with crossings `y₀, z₀`, written without the `BigonData` -/
def s174_reducedRecordOf (D : Diagram) (y₀ z₀ : D.Γ.Crossing) : Record :=
  D.record.restrictCrossings
    {c | c ≠ D.record.crossingOf (D.overVisit y₀) ∧ c ≠ D.record.crossingOf (D.overVisit z₀)}

theorem s174_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hy : B.y = y₀) (hz : B.z = z₀) : B.reducedRecord = s174_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s174_reducedRecordOf
  rw [hy, hz]

/-- the reduced record does not depend on which bigon crossing is called `y` -/
theorem s174_reducedRecord_eq_swap {D : Diagram} (B : BigonData D) {y₀ z₀ : D.Γ.Crossing}
    (hy : B.y = z₀) (hz : B.z = y₀) : B.reducedRecord = s174_reducedRecordOf D y₀ z₀ := by
  unfold BigonData.reducedRecord BigonData.keep s174_reducedRecordOf
  rw [hy, hz]
  congr 1
  ext c
  exact and_comm

/-- **(b) `hrec` of PLAN_FINAL §4.2, STATED** (the wall transport of the carried marks, G11 Unit-F
pattern / `GT_owner_transport` on good marks): the record of `D_H.switch x'` with the four occurrences
of `x', w'` deleted is the record of the `P-b` lift `D_L = carrierDiagram qAB`.  Not proved here;
cost estimate in Site_174_REPORT.md. -/
def s174_hrec_prop (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') : Prop :=
  Nonempty (RecordIso
    (s174_reducedRecordOf ((CV.carrierDiagram hn hG' hSm' q').switch
        (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'))
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hw')
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'))
    (CV.carrierDiagram hn hG hSm qAB).record)

/-- **(c) The `fulltwist` field of `gsc_Ledger` from (a) `s174_site` and (b) `s174_hrec_prop`**, through
the PROVED glue `gsc_fulltwist_of_bigon`: `qx` is the lifted `x'`, `D₀` the library smoothing
(`exists_smoothing`).  `gsc_fulltwist_triple` is `moves_fulltwist_triple` verbatim. -/
theorem s174_fulltwist_of_hrec
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw') :
    ∃ D₀ : Diagram, gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q') D₀
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') := by
  obtain ⟨B, -, hB⟩ := s174_site hn hG hG' D hsgn hSm' q' hx' hw'
  have hq : (CV.carrierDiagram hn hG' hSm' q').IsPositive
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') :=
    geoPositiveLift_isPositive hn _ _ q' _
  have hrec' : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hSm qAB).record) := by
    rcases hB with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · rw [s174_reducedRecord_eq B hy hz]; exact hrec
    · rw [s174_reducedRecord_eq_swap B hy hz]; exact hrec
  exact gsc_fulltwist_of_bigon _ _ _ hq rfl rfl B hrec'

end S174Consumer

end

end SM.Link

/-! ## HREC (Wave 2, I-174 (b)): the wall record transport `hrec` of row 174 — PROVED

Prover of unit HREC, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the
prefix `r174h_`.  Content: `s174_hrec_prop` (Site_174_REPORT §3) is proved for the ledger's carrier
`q' = τ qAB = GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` on a `GT_Endpoint` configuration
(`r174h__s174_hrec_prop_proof`).  Route: the CV:cor:groupedknot §2 pattern `liftRestrictRecordIso`
(CV/GroupedKnot.lean, "the record of the lift of a smaller carrier is the restricted record of the
lift of a larger one") across the wall — the identity on parent visits, transported by
`visitTransport`, is a named record isomorphism from the record of the `P-b` lift `D_L` onto the
record of `D_H.switch x'` restricted to the crossings other than `x', w'`:
* the retained crossings correspond (`r174h_mem_retained'`, `r174h_retained_of_mem'`): a retained
  crossing of `AB` is outside the triangle (it lies in `U(S)`, and `x, w` interlace the selected `m`),
  so its visits are good marks and `GT_owner_transport` carries their owner to `τ qAB`; conversely a
  retained crossing of `AB'` other than `x', w'` is outside the triangle and comes from `AB`;
* the successor clause is `cycNext_unique_on` on the parent keys (`visitBetween_iff_key`,
  `arcBetween_iff_key`, `not_arcBetween_firstReturn`), the key order of outside visits being carried
  by `GT_Wall.key_lt` (no reversed pair: `r174h_cyc`);
* pairing is `liftVisit_twin` + `visitTransport_visitTwin`; the over bits are the divide signs
  `sign det(edge ℓ, edge ℓ')`, carried by `GT_Endpoint.sign_eq` (`overBit_eq_true_iff_parent`); the
  signs are all `+1` (`geoPositiveLift_sign`); the switch at `x'` touches only deleted occurrences
  (`r174h_switch_overBit_of_ne`, `switch_sign_of_ne`). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

/-! ### Record-level helpers: a switched diagram's record has the same occurrences, successor, pairing
and arc order; the crossing of an occurrence is the crossing of `overVisit y₀` iff it visits `y₀` -/

section R174HRecord

variable (E : Diagram)

theorem r174h_switch_record_succ (x₀ : E.Γ.Crossing) (v : E.Γ.Visit) :
    (E.switch x₀).record.succ v = E.record.succ v := rfl

theorem r174h_switch_record_pair (x₀ : E.Γ.Crossing) (v : E.Γ.Visit) :
    (E.switch x₀).record.pair v = E.record.pair v := rfl

theorem r174h_switch_arcBetween (x₀ : E.Γ.Crossing) (v w u : E.Γ.Visit) :
    (E.switch x₀).record.ArcBetween v w u ↔ E.record.ArcBetween v w u := Iff.rfl

/-- The over bit of an occurrence of an unswitched crossing is unchanged by the switch. -/
theorem r174h_switch_overBit_of_ne {x₀ : E.Γ.Crossing} {v : E.Γ.Visit} (hv : v.1 ≠ x₀) :
    (E.switch x₀).overBit v = E.overBit v := by
  have h3 : (E.switch x₀).isOver v ↔ E.isOver v := by
    unfold Diagram.isOver
    rw [Diagram.switch_overStrand_of_ne E hv]
    exact Iff.rfl
  exact Bool.eq_iff_iff.mpr ((Diagram.overBit_eq_true_iff (E.switch x₀) v).trans
    (h3.trans (Diagram.overBit_eq_true_iff E v).symm))

/-- The record crossing of an occurrence is the record crossing of `overVisit y₀` iff the occurrence
visits `y₀`. -/
theorem r174h_crossingOf_overVisit_eq_iff (v : E.Γ.Visit) (y₀ : E.Γ.Crossing) :
    E.record.crossingOf v = E.record.crossingOf (E.overVisit y₀) ↔ v.1 = y₀ := by
  rw [Record.crossingOf_eq_iff]
  change v ∈ ({E.overVisit y₀, E.twin (E.overVisit y₀)} : Finset E.Γ.Visit) ↔ _
  rw [Diagram.mem_pair_twin_iff]
  exact Iff.rfl

end R174HRecord

/-! ### The configuration: the centre row `S = Q ∪ {m}`, its wall `𝑾` and the `E-b` carrier `τ qAB` -/

section R174H

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
  (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))

local notation "𝑻" => triangleCrossings P e f g
local notation "𝑺" => Q ∪ (Singleton.singleton m : Finset (Crossing P))
local notation "𝑺'" => transportSupport hs (Q ∪ (Singleton.singleton m : Finset (Crossing P)))
local notation "𝑾" => gsc_wall_of_endpoint hG hG' D hSm hSm'
local notation "qAB'" => GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB

/-! #### The retained crossings of `AB` and of `AB' = τ AB` correspond, up to `x', w'` -/

include D hSm in
/-- A retained crossing of the carrier `AB` of the centre row is outside the triangle: it lies in
`U(S)`, while `x, w` interlace the selected `m` and `m` is selected. -/
theorem r174h_not_tri_of_retained {c : Crossing P}
    (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) : c.val ∉ triangleSupports e f g := by
  intro hT
  have hU := geoCarrierCrossings_subset_U hG.crossingGeometry
    (CV.geoIndependent_of_mem_Ind _ hSm) qAB hc
  rw [mem_geoSupportUnselected_iff] at hU
  have hmS : m ∈ 𝑺 := Finset.mem_union_right _ (Finset.mem_singleton_self m)
  rcases D.tri_cases c hT with h | h | h
  · subst h; exact hU.2 m hmS D.hxm
  · subst h; exact hU.2 m hmS D.hwm
  · subst h; exact hU.1 hmS

include D hSm in
/-- The visits of a retained crossing of `AB` are good marks of the wall. -/
theorem r174h_good {v : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    GT_Good 𝑻 𝑺 (Sum.inr v) :=
  GT_good_of_not_mem _ _ (fun h => r174h_not_tri_of_retained hG hG' D hSm qAB hv
    ((F1.mem_triangleCrossings e f g v.1).mp h))

include D hSm in
theorem r174h_ne_x' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ≠ crossingTransport hs x := fun h =>
  r174h_not_tri_of_retained hG hG' D hSm qAB hc (((crossingTransport hs).injective h) ▸ D.xT)

include D hSm in
theorem r174h_ne_w' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ≠ crossingTransport hs w := fun h =>
  r174h_not_tri_of_retained hG hG' D hSm qAB hc (((crossingTransport hs).injective h) ▸ D.wT)

/-- The transported visit of a retained crossing of `AB` is owned by `τ AB` (`GT_owner_transport`). -/
theorem r174h_owner' {v : Visit P} (hv : v.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    geoOwner hG'.crossingGeometry 𝑺' (Sum.inr (visitTransport hs v)) = qAB' := by
  rw [← markTransport_visit, GT_owner_transport 𝑾 (r174h_good hG hG' D hSm qAB hv),
    ((mem_geoCarrierCrossings _ _ _ _).mp hv).2 v rfl]

/-- A retained crossing of `AB` is transported to a retained crossing of `τ AB`. -/
theorem r174h_mem_retained' {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB' := by
  rw [mem_geoCarrierCrossings]
  refine ⟨?_, fun v' hv' => ?_⟩
  · rw [mem_transportSupport_iff]
    exact ((mem_geoCarrierCrossings _ _ _ _).mp hc).1
  · obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hvc : v.1 = c := (crossingTransport hs).injective hv'
    exact r174h_owner' hG hG' D hSm hSm' qAB (hvc ▸ hc)

/-- Conversely, a retained crossing of `τ AB` other than `x', w'` comes from a retained crossing of
`AB`: it is outside the triangle (not `m'`, which is selected), so its visits are good marks. -/
theorem r174h_retained_of_mem' {c : Crossing P}
    (hc : crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB')
    (hcx : crossingTransport hs c ≠ crossingTransport hs x)
    (hcw : crossingTransport hs c ≠ crossingTransport hs w) :
    c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  rw [mem_geoCarrierCrossings] at hc ⊢
  have hcS : c ∉ 𝑺 := by rw [← mem_transportSupport_iff hs]; exact hc.1
  have hcT : c.val ∉ triangleSupports e f g := by
    intro hT
    rcases D.tri_cases c hT with h | h | h
    · exact hcx (by rw [h])
    · exact hcw (by rw [h])
    · exact hcS (by rw [h]; exact Finset.mem_union_right _ (Finset.mem_singleton_self _))
  refine ⟨hcS, fun v hv => ?_⟩
  have hgood : GT_Good 𝑻 𝑺 (Sum.inr v) :=
    GT_good_of_not_mem _ _ (fun h => hcT (by rw [← hv]; exact (F1.mem_triangleCrossings e f g v.1).mp h))
  have h1 := hc.2 (visitTransport hs v) (by rw [visitTransport_crossing, hv])
  rw [← markTransport_visit, GT_owner_transport 𝑾 hgood] at h1
  exact (GT_carrierEquiv 𝑾).injective h1

theorem r174h_retained_of_mem'' {c' : Crossing P'}
    (hc : c' ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' qAB')
    (hcx : c' ≠ crossingTransport hs x) (hcw : c' ≠ crossingTransport hs w) :
    (crossingTransport hs).symm c' ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  obtain ⟨c, rfl⟩ := (crossingTransport hs).surjective c'
  rw [Equiv.symm_apply_apply]
  exact r174h_retained_of_mem' hG hG' D hSm hSm' qAB hc hcx hcw

/-! #### The key order of the visits of retained crossings is carried across the wall -/

include D hSm hSm' in
/-- The visits of retained crossings of `AB` form no reversed pair with anything (they are outside the
triangle), so their key order is carried (`GT_Wall.key_lt`). -/
theorem r174h_key_lt {a b : Visit P} (ha : a.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    geometricVisitKey hG.crossingGeometry a < geometricVisitKey hG.crossingGeometry b ↔
      geometricVisitKey hG'.crossingGeometry (visitTransport hs a) <
        geometricVisitKey hG'.crossingGeometry (visitTransport hs b) :=
  𝑾.key_lt a b (GT_not_rev_of_not_mem_left (fun h => r174h_not_tri_of_retained hG hG' D hSm qAB ha
    ((F1.mem_triangleCrossings e f g a.1).mp h)))

include D hSm hSm' in
/-- The cyclic order of three visits of retained crossings of `AB` is carried across the wall. -/
theorem r174h_cyc {a b c : Visit P} (ha : a.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB)
    (hb : b.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB)
    (hc : c.1 ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    cycBetween (geometricVisitKey hG.crossingGeometry a) (geometricVisitKey hG.crossingGeometry b)
        (geometricVisitKey hG.crossingGeometry c) ↔
      cycBetween (geometricVisitKey hG'.crossingGeometry (visitTransport hs a))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs b))
        (geometricVisitKey hG'.crossingGeometry (visitTransport hs c)) :=
  GT_cyc_congr_of_lt (r174h_key_lt hG hG' D hSm hSm' qAB ha) (r174h_key_lt hG hG' D hSm hSm' qAB hb)
    (r174h_key_lt hG hG' D hSm hSm' qAB hc)

/-! ### The two lifts, the switched `E`-side diagram and the keep-set

The `E-b` carrier is a variable `q'` with `hq' : q' = τ qAB`, as `s174_hrec_prop` binds it: the carrier
shadow `geoCarrierShadow … q'` is an `abbrev`, and with the compound term `τ qAB` in place of `q'` the
unifier unfolds it on every type ascription of a lifted crossing and times out; with the variable it is
stuck at once.  Every declaration of this section takes the eleven arguments
`hn hG hG' D hSm hSm' qAB q' hq' hx' hw'` in this order. -/

section R174HLift

variable (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
  (hq' : q' = GT_carrierEquiv (gsc_wall_of_endpoint hG hG' D hSm hSm') qAB)
  (hx' : crossingTransport hs x ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
  (hw' : crossingTransport hs w ∈
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')

include hn hG hG' D hSm hSm' qAB q' hq' hx' hw'

set_option linter.unusedSectionVars false

local notation "hGc" => s174_cg hn hG
local notation "hGc'" => s174_cg hn hG'
local notation "hSg" => CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSm
local notation "hSg'" => CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm'
/-- `D_L`, the `P-b` lift -/
local notation "𝓓L" => geoPositiveLift hn (s174_cg hn hG)
  (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSm) qAB
/-- `D_H`, the `E-b` lift -/
local notation "𝓓H" => geoPositiveLift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
local notation "𝓵x" => s174_lift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' (crossingTransport hs x) hx'
local notation "𝓵w" => s174_lift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' (crossingTransport hs w) hw'
/-- `D_H.switch x'` -/
local notation "𝓓sw" => Diagram.switch (geoPositiveLift hn (s174_cg hn hG')
  (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q')
  (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
    (crossingTransport hs x) hx')

/-- The retained crossings of `AB` are transported into those of `q' = τ AB`. -/
theorem r174h_mem_retained_q {c : Crossing P} (hc : c ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB) :
    crossingTransport hs c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q' := by
  rw [hq']
  exact r174h_mem_retained' hG hG' D hSm hSm' qAB hc

/-- A retained crossing of `q' = τ AB` other than `x', w'` comes from a retained crossing of `AB`. -/
theorem r174h_retained_of_mem_q {c' : Crossing P'}
    (hc : c' ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q')
    (hcx : c' ≠ crossingTransport hs x) (hcw : c' ≠ crossingTransport hs w) :
    (crossingTransport hs).symm c' ∈ geoCarrierCrossings hG.crossingGeometry 𝑺 qAB := by
  rw [hq'] at hc
  exact r174h_retained_of_mem'' hG hG' D hSm hSm' qAB hc hcx hcw

/-- the record crossings kept by the deletion of `x', w'`: the keep-set of `s174_reducedRecordOf` -/
def r174h_keep : Set (𝓓sw).record.Crossing :=
  {c | c ≠ (𝓓sw).record.crossingOf ((𝓓sw).overVisit 𝓵w) ∧
    c ≠ (𝓓sw).record.crossingOf ((𝓓sw).overVisit 𝓵x)}

local notation "𝓚" => r174h_keep hn hG' hSm' q' hx' hw'

/-- Sanity (`rfl`): the reduced record of the site is the restriction to the keep-set. -/
theorem r174h_reducedRecordOf_eq :
    s174_reducedRecordOf 𝓓sw 𝓵w 𝓵x = (𝓓sw).record.restrictCrossings 𝓚 := rfl

theorem r174h_crossKeep_iff (v : (𝓓sw).Γ.Visit) :
    (𝓓sw).record.CrossKeep 𝓚 v ↔ v.1 ≠ 𝓵w ∧ v.1 ≠ 𝓵x := by
  change ((𝓓sw).record.crossingOf v ≠ _ ∧ (𝓓sw).record.crossingOf v ≠ _) ↔ _
  exact and_congr (not_congr (r174h_crossingOf_overVisit_eq_iff _ v _))
    (not_congr (r174h_crossingOf_overVisit_eq_iff _ v _))

/-- An occurrence of the lift sits at the lifted crossing `s174_lift c` iff its parent visit is a visit
of `c`. -/
theorem r174h_lift_eq_iff (v : (𝓓H).Γ.Visit) {c : Crossing P'}
    (hc : c ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺' q') :
    v.1 = s174_lift hn hGc' hSg' q' c hc ↔ (CV.liftVisit hn hGc' hSg' q' v).1 = c := by
  rw [CV.liftVisit_fst]
  exact (Equiv.eq_symm_apply _).trans ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/-- The kept occurrences are those whose parent crossing is neither `w'` nor `x'`. -/
theorem r174h_crossKeep_iff' (v : (𝓓sw).Γ.Visit) :
    (𝓓sw).record.CrossKeep 𝓚 v ↔
      (CV.liftVisit hn hGc' hSg' q' v).1 ≠ crossingTransport hs w ∧
      (CV.liftVisit hn hGc' hSg' q' v).1 ≠ crossingTransport hs x := by
  rw [r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw']
  exact and_congr (not_congr (r174h_lift_eq_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v hw'))
    (not_congr (r174h_lift_eq_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v hx'))

/-! ### The transfer: the identity on parent visits, transported across the wall -/

/-- The occurrence bijection: an occurrence of `D_L` (a visit of a retained crossing of `AB`) goes to
the occurrence of `D_H` at the transported visit, which is kept (`x', w'` are not transports of retained
crossings of `AB`). -/
noncomputable def r174h_transfer :
    (𝓓L).Γ.Visit ≃ {v : (𝓓sw).Γ.Visit // (𝓓sw).record.CrossKeep 𝓚 v} where
  toFun v' := ⟨(CV.liftVisitEquiv hn hGc' hSg' q').symm
      ⟨visitTransport hs (CV.liftVisit hn hGc hSg qAB v'),
        r174h_mem_retained_q hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
          (CV.liftVisit_mem hn hGc hSg qAB v')⟩,
    (r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mpr
      ⟨by
        rw [CV.liftVisit_symm]
        exact r174h_ne_w' hG hG' D hSm qAB (CV.liftVisit_mem hn hGc hSg qAB v'),
       by
        rw [CV.liftVisit_symm]
        exact r174h_ne_x' hG hG' D hSm qAB (CV.liftVisit_mem hn hGc hSg qAB v')⟩⟩
  invFun v := (CV.liftVisitEquiv hn hGc hSg qAB).symm
    ⟨(visitTransport hs).symm (CV.liftVisit hn hGc' hSg' q' v.1),
      r174h_retained_of_mem_q hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
        (CV.liftVisit_mem hn hGc' hSg' q' v.1)
        ((r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v.1).mp v.2).2
        ((r174h_crossKeep_iff' hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v.1).mp v.2).1⟩
  left_inv v' := by
    apply CV.liftVisit_injective hn hGc hSg qAB
    rw [CV.liftVisit_symm]
    simp only [CV.liftVisit_symm, Equiv.symm_apply_apply]
  right_inv v := by
    apply Subtype.ext
    apply CV.liftVisit_injective hn hGc' hSg' q'
    rw [CV.liftVisit_symm]
    simp only [CV.liftVisit_symm, Equiv.apply_symm_apply]

local notation "𝚽" => r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'

theorem r174h_liftVisit_transfer (v' : (𝓓L).Γ.Visit) :
    CV.liftVisit hn hGc' hSg' q' (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v').1 =
      visitTransport hs (CV.liftVisit hn hGc hSg qAB v') := by
  show CV.liftVisit hn hGc' hSg' q' ((CV.liftVisitEquiv hn hGc' hSg' q').symm _) = _
  rw [CV.liftVisit_symm]

theorem r174h_record_componentCount : (𝓓sw).record.componentCount = 1 :=
  CV.record_componentCount_one _ (geoPositiveLift_componentCount hn hGc' hSg' q')

/-- **The successor clause**: the transfer carries the successor of `D_L` to the first-return successor
of the restricted record (both are the cyclic successor among the kept occurrences in the parent key
order, which is carried across the wall on the visits of retained crossings; `cycNext_unique_on`). -/
theorem r174h_transfer_succ (v' : (𝓓L).Γ.Visit) :
    (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' ((𝓓L).nextVisit v')).1 =
      (((𝓓sw).record.restrictCrossings 𝓚).succ
        (r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v')).1 := by
  set Φ := r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw' with hΦdef
  have hΦ : ∀ y, CV.liftVisit hn hGc' hSg' q' (Φ y).1 =
      visitTransport hs (CV.liftVisit hn hGc hSg qAB y) :=
    r174h_liftVisit_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  have h1 : (𝓓sw).record.componentCount = 1 :=
    r174h_record_componentCount hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  have hD' : (𝓓L).componentCount = 1 := geoPositiveLift_componentCount hn hGc hSg qAB
  refine cycNext_unique_on
    (p := fun u : (𝓓sw).Γ.Visit => (𝓓sw).record.CrossKeep 𝓚 u)
    (k := fun u => geometricVisitKey hG'.crossingGeometry (CV.liftVisit hn hGc' hSg' q' u))
    (fun a b _ _ hab => CV.liftVisit_injective hn hGc' hSg' q' (geometricVisitKey_injective _ hab))
    (Φ v').2 (Φ ((𝓓L).nextVisit v')).2 (((𝓓sw).record.restrictCrossings 𝓚).succ (Φ v')).2 ?_ ?_ ?_ ?_
  · intro h
    have h' := Φ.injective (Subtype.ext h)
    exact (𝓓L).nextVisit_ne_self v' ((𝓓L).twin v') (CV.compOf_eq_of_single hD' _ _)
      ((𝓓L).twin_ne v') h'
  · exact (((𝓓sw).record.restrictCrossings_succ_val_eq_iff h1 _ (Φ v').2 _).mp rfl).2.1
  · intro u hu hb
    obtain ⟨u', hu'⟩ := Φ.surjective ⟨u, hu⟩
    have hu'' : u = (Φ u').1 := by rw [hu']
    rw [hu'', hΦ, hΦ, hΦ] at hb
    have hb' := (r174h_cyc hG hG' D hSm hSm' qAB (CV.liftVisit_mem hn hGc hSg qAB v')
      (CV.liftVisit_mem hn hGc hSg qAB u') (CV.liftVisit_mem hn hGc hSg qAB _)).mpr hb
    exact (𝓓L).not_visitBetween_nextVisit v' u' (CV.compOf_eq_of_single hD' _ _)
      ((CV.visitBetween_iff_key hn hGc hSg qAB v' u' _).mpr hb')
  · intro u hu hb
    have harc := (CV.arcBetween_iff_key hn hGc' hSg' q' (Φ v').1 u _).mpr hb
    exact (𝓓sw).record.not_arcBetween_firstReturn _ h1 (Φ v') hu harc

/-- **The record of the `P-b` lift is the reduced record of the switched `E-b` lift** (the wall record
transport of row 174): the transfer is a named record isomorphism.  Clauses: successor
(`r174h_transfer_succ`), pairing (`liftVisit_twin`, `visitTransport_visitTwin`), over/under
(`overBit_eq_true_iff_parent` and the carried divide signs `GT_Endpoint.sign_eq`), signs (all `+1`,
the switch touching only the deleted occurrences of `x'`). -/
noncomputable def r174h_recordIso :
    RecordIso (𝓓L).record ((𝓓sw).record.restrictCrossings 𝓚) where
  e := finCongr (show (𝓓L).Γ.c = (𝓓sw).Γ.c from
    (geoPositiveLift_componentCount hn hGc hSg qAB).trans
      (geoPositiveLift_componentCount hn hGc' hSg' q').symm)
  Φ := r174h_transfer hn hG hG' D hSm hSm' qAB q' hq' hx' hw'
  comp_eq _ :=
    have : Subsingleton (Fin (𝓓sw).Γ.c) :=
      Fin.subsingleton_iff_le_one.mpr (le_of_eq (geoPositiveLift_componentCount hn hGc' hSg' q'))
    @Subsingleton.elim (Fin (𝓓sw).Γ.c) this _ _
  succ_eq v' := Subtype.ext (r174h_transfer_succ hn hG hG' D hSm hSm' qAB q' hq' hx' hw' v')
  pair_eq v' := by
    apply Subtype.ext
    apply CV.liftVisit_injective hn hGc' hSg' q'
    have ht : CV.liftVisit hn hGc' hSg' q' ((𝓓H).twin (𝚽 v').1) =
        visitTwin (CV.liftVisit hn hGc' hSg' q' (𝚽 v').1) :=
      CV.liftVisit_twin hn hGc' hSg' q' _
    change CV.liftVisit hn hGc' hSg' q' (𝚽 ((𝓓L).twin v')).1 =
      CV.liftVisit hn hGc' hSg' q' ((𝓓H).twin (𝚽 v').1)
    rw [ht, r174h_liftVisit_transfer, r174h_liftVisit_transfer, CV.liftVisit_twin,
      visitTransport_visitTwin]
  bit_eq v' := by
    have hne : (𝚽 v').1.1 ≠ 𝓵x :=
      ((r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mp (𝚽 v').2).2
    have h1 : (𝓓sw).overBit (𝚽 v').1 = (𝓓H).overBit (𝚽 v').1 :=
      r174h_switch_overBit_of_ne (𝓓H) hne
    have h2 := CV.overBit_eq_true_iff_parent hn hGc' hSg' q' (𝚽 v').1
    have h3 := CV.overBit_eq_true_iff_parent hn hGc hSg qAB v'
    change (𝓓sw).overBit (𝚽 v').1 = (𝓓L).overBit v'
    rw [h1, Bool.eq_iff_iff, h2, h3, r174h_liftVisit_transfer, ← visitTransport_visitTwin,
      visitTransport_edge, visitTransport_edge]
    exact (GT_det_pos_iff_of_sign (D.sign_eq _ _ (by
      rw [← visit_crossing_val_eq_pair]
      exact (CV.liftVisit hn hGc hSg qAB v').1.property))).symm
  sgn_eq v' := by
    have hne : (𝚽 v').1.1 ≠ 𝓵x :=
      ((r174h_crossKeep_iff hn hG hG' D hSm hSm' qAB q' hq' hx' hw' _).mp (𝚽 v').2).2
    have h1 : (𝓓sw).sign (𝚽 v').1.1 = (𝓓H).sign (𝚽 v').1.1 := Diagram.switch_sign_of_ne (𝓓H) hne
    change (𝓓sw).sign (𝚽 v').1.1 = (𝓓L).sign v'.1
    exact h1.trans ((geoPositiveLift_sign hn hGc' hSg' q' (𝚽 v').1.1).trans
      (geoPositiveLift_sign hn hGc hSg qAB v'.1).symm)

/-! ### The stated Prop `s174_hrec_prop`, PROVED for the ledger's carrier `q' = τ qAB` -/

set_option linter.style.nameCheck false in
/-- **`hrec` of row 174 (PLAN_FINAL §4.2, Site_174_REPORT §3), PROVED** for the carrier
`q' = τ qAB = GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` of the ledger (`gsc_wallData_of_endpoint`).
The bare Prop `s174_hrec_prop … qAB q' …` binds an arbitrary carrier `q'` of the transported centre row,
unrelated to `qAB`; it holds exactly for the wall copy of `qAB` (for another `q'` the two records have
different crossing sets in general), so the `GT_Endpoint` configuration `D` and the identification
`hq'` are the hypotheses under which the consumer `s174_fulltwist_of_hrec` is invoked (`W.τ qAB` is
`GT_carrierEquiv (gsc_wall_of_endpoint …) qAB` by `rfl`). -/
theorem r174h__s174_hrec_prop_proof : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw' :=
  Nonempty.intro (r174h_recordIso hn hG hG' D hSm hSm' qAB q' hq' hx' hw').symm

/-- **The `fulltwist` field of `gsc_Ledger` for row 174**, from (a) `s174_site` and (b) `hrec` (both
PROVED): given the site inputs `hx', hw'` (the four visits of `x', w'` are owned by `τ qAB`, the
remaining consumer obligation of Site_174_REPORT §5), `gsc_fulltwist_triple` holds with `qx` the lifted
`x'` and `D₀` the library smoothing.  The realiser instantiates `q' := W.τ qAB`, `hq' := rfl`
(`gsc_wallData_of_endpoint`). -/
theorem r174h_fulltwist (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    ∃ D₀ : Diagram, gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB)
      (CV.carrierDiagram hn hG' hSm' q') D₀
      (s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx') :=
  s174_fulltwist_of_hrec hn hG hG' D hsgn hSm hSm' qAB q' hx' hw'
    (r174h__s174_hrec_prop_proof hn hG hG' D hSm hSm' qAB q' hq' hx' hw')

end R174HLift

/-- `hrec` in the ledger's binding `q' := W.τ qAB` (`gsc_wallData_of_endpoint`): `hq'` is `rfl`. -/
theorem r174h_hrec_tau
    (hx' : crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB))
    (hw' : crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry 𝑺'
      ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB)) :
    s174_hrec_prop hn hG hG' hSm hSm' qAB ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB) hx' hw' :=
  r174h__s174_hrec_prop_proof hn hG hG' D hSm hSm' qAB _ rfl hx' hw'

end R174H

end

end SM.Link
