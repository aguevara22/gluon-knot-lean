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


/-! ## Unit SMOOTH (Wave 2, R174_SMOOTH): the oriented smoothing `D₀` of the `E`-side lift at `x'` and the
ledger fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` (U_R174_REPORT §4 items 5–6,
`gsc_smoothing_split`)

Prover of unit SMOOTH, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the prefix
`r174s_`.  Plan: `D₀ := r174s_D₀ D_H qx` is the library smoothing `smoothDiagram` (the `D₀` of
`exists_smoothing`, so the SAME `D₀` as `gsc_fulltwist_of_bigon` / `s174_fulltwist_of_hrec` produce), with
its record clause `D₀.record ≅ D_H.record.smooth (overVisit qx)`.  Since `D_H` has one circle, `qx` is a
self crossing and the smoothing has two circles, the `s₁`-cycles of the two occurrences of `qx`; the
occurrences on each circle are exactly the occurrences strictly inside one of the two open arcs of
`D_H.record` cut at the two occurrences of `qx` (B).  The knot restriction of `D₀` to a circle has the
record `D₀.record.restrict {i}` (`restrict_record`), which is `(D_H.record.smooth v).restrict {circle}`
along the record clause (`RecordIso.restrict`), and that is `D_H.record.restrictCrossings K` for `K` the
crossings of `D_H` internal to the arc (B: the first-return successor along `s₁ = s ∘ swap(v, τ v)` on the
arc-internal occurrences is the first return along `s`, `r174s_firstReturn_reconnect_eq`).  The geometric
content — that these two arc records are the `P-ac` records of `A` and `B` — is the wall/ownership
transport of U_R174 §4 items 1–2 and is the one BLACK BOX here (`r174s_arc_rec_prop`, §D).  From it and
ax:gausscode: `componentCount = 2`, `i ≠ j`, `homfly (knotRestrict i/j) = Q_A / Q_B`, the linking number
(`exists_linkingNumber`), and the writhe count `w_H − 1 = w(D₀) = w_A + w_B + 2ℓ` (all crossings positive;
`writhe_wall` turns it into (10)). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

namespace Record

variable (ρ : Record)

/-- The crossings both of whose occurrences lie strictly inside the forward arc from `u` to `τ u`
(the "`A`-string" of the smoothing at the crossing of `u`). -/
def r174s_KeepArc (u : ρ.M) : Set ρ.Crossing :=
  {c | ∀ w ∈ c.1, ρ.ArcBetween u w (ρ.pair u)}

theorem r174s_crossKeep_keepArc_iff (u w : ρ.M) :
    ρ.CrossKeep (ρ.r174s_KeepArc u) w ↔
      ρ.ArcBetween u w (ρ.pair u) ∧ ρ.ArcBetween u (ρ.pair w) (ρ.pair u) := by
  show (∀ z ∈ ({w, ρ.pair w} : Finset ρ.M), ρ.ArcBetween u z (ρ.pair u)) ↔ _
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- The circle of the smoothing at `u` carrying the open arc `(a, τ a)` (`a ∈ {u, τ u}`): the
`s₁`-cycle of `τ a`. -/
def r174s_arcComp (u a : ρ.M) : (ρ.smooth u).comps :=
  Sum.inl (Quotient.mk (Equiv.Perm.SameCycle.setoid (ρ.reconnect u)) (ρ.pair a))

section OneCircle

variable (h1 : ρ.componentCount = 1)
include h1

/-- On one circle every crossing is a self crossing. -/
theorem r174s_isSelfCrossing (u : ρ.M) : ρ.IsSelfCrossing u :=
  ρ.comp_eq_of_one_circle h1 u (ρ.pair u)

theorem r174s_arcBetween_pair_iff (u w : ρ.M) :
    ρ.ArcBetween u w (ρ.pair u) ↔ 0 < ρ.steps u w ∧ ρ.steps u w < ρ.steps u (ρ.pair u) := by
  rw [ρ.arcBetween_iff_posBetween h1 u, ρ.steps_self]
  unfold PosBetween
  omega

/-- An occurrence of the open arc `(u, τ u)` lies on the `s₁`-cycle of `τ u` ("(x A y B) ↦ (x B), (y A)":
the cycle `(y A)`). -/
theorem r174s_reconnect_sameCycle_pair_of_arc {u w : ρ.M} (hw : ρ.ArcBetween u w (ρ.pair u)) :
    (ρ.reconnect u).SameCycle w (ρ.pair u) := by
  obtain ⟨hpos, hlt⟩ := (ρ.r174s_arcBetween_pair_iff h1 u w).mp hw
  have hwk : (ρ.succ ^ ρ.steps u w) u = w := ρ.pow_steps h1 u w
  have hpL : (ρ.succ ^ ρ.steps u (ρ.pair u)) u = ρ.pair u := ρ.pow_steps h1 u (ρ.pair u)
  have hcard : ρ.steps u (ρ.pair u) < Fintype.card ρ.M := ρ.steps_lt_card h1 u (ρ.pair u)
  have avoid : ∀ j, j < ρ.steps u (ρ.pair u) - ρ.steps u w →
      (ρ.succ ^ j) w ≠ u ∧ (ρ.succ ^ j) w ≠ ρ.pair u := by
    intro j hj
    have e : (ρ.succ ^ j) w = (ρ.succ ^ (j + ρ.steps u w)) u := by
      rw [pow_add, Equiv.Perm.mul_apply, hwk]
    rw [e]
    constructor
    · intro h
      have h0 : (ρ.succ ^ (j + ρ.steps u w)) u = (ρ.succ ^ 0) u := by
        rw [h, pow_zero, Equiv.Perm.one_apply]
      have := (ρ.pow_apply_eq_pow_apply_iff h1 u (by omega) (by omega)).mp h0
      omega
    · intro h
      have := ρ.steps_le_of_pow h
      omega
  have key : (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w = ρ.pair u := by
    calc (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w
        = (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) ((ρ.succ ^ ρ.steps u w) u) := by rw [hwk]
      _ = (ρ.succ ^ (ρ.steps u (ρ.pair u) - ρ.steps u w + ρ.steps u w)) u := by
          rw [pow_add, Equiv.Perm.mul_apply]
      _ = ρ.pair u := by rw [Nat.sub_add_cancel hlt.le, hpL]
  refine ⟨((ρ.steps u (ρ.pair u) - ρ.steps u w : ℕ) : ℤ), ?_⟩
  rw [zpow_natCast]
  show ((ρ.succ * Equiv.swap u (ρ.pair u)) ^ (ρ.steps u (ρ.pair u) - ρ.steps u w)) w = ρ.pair u
  rw [mul_swap_pow_apply_of_forall_ne ρ.succ u (ρ.pair u) w _ avoid, key]

theorem r174s_reconnect_sameCycle_self_of_arc {u w : ρ.M} (hw : ρ.ArcBetween (ρ.pair u) w u) :
    (ρ.reconnect u).SameCycle w u := by
  have := ρ.r174s_reconnect_sameCycle_pair_of_arc h1 (u := ρ.pair u) (w := w)
    (by rw [ρ.pair_invol]; exact hw)
  rw [ρ.reconnect_pair, ρ.pair_invol] at this
  exact this

/-- For a retained occurrence: on the `s₁`-cycle of `τ u` iff strictly inside the arc `(u, τ u)`. -/
theorem r174s_reconnect_sameCycle_pair_iff {u w : ρ.M} (hw : ρ.SmoothKeep u w) :
    (ρ.reconnect u).SameCycle w (ρ.pair u) ↔ ρ.ArcBetween u w (ρ.pair u) := by
  obtain ⟨hwu, hwp⟩ := (ρ.smoothKeep_iff u w).mp hw
  refine ⟨fun h => ?_, ρ.r174s_reconnect_sameCycle_pair_of_arc h1⟩
  rcases ρ.arcBetween_or_arcBetween h1 (Ne.symm hwu) (ρ.ne_pair u) hwp with h' | h'
  · exact h'
  · exfalso
    have h2 : (ρ.reconnect u).SameCycle w u :=
      ρ.r174s_reconnect_sameCycle_self_of_arc h1 ((ρ.arcBetween_rotate h1 u (ρ.pair u) w).mp h')
    exact ρ.not_reconnect_sameCycle_pair_of_self u (ρ.r174s_isSelfCrossing h1 u) (h2.symm.trans h)

/-- The circle of a retained occurrence of the smoothing at `u` is the arc circle of `a ∈ {u, τ u}`
exactly when the occurrence lies strictly inside the arc `(a, τ a)`. -/
theorem r174s_smooth_comp_eq_iff {u a : ρ.M} (ha : a = u ∨ a = ρ.pair u) (w : (ρ.smooth u).M) :
    (ρ.smooth u).comp w = ρ.r174s_arcComp u a ↔ ρ.ArcBetween a w.1 (ρ.pair a) := by
  have hr : ρ.reconnect a = ρ.reconnect u := by
    rcases ha with rfl | rfl
    · rfl
    · exact ρ.reconnect_pair u
  have hk : ρ.SmoothKeep a w.1 := by
    rcases ha with rfl | rfl
    · exact w.2
    · exact (ρ.smoothKeep_pair_eq u w.1).mpr w.2
  rw [ρ.smooth_comp]
  unfold r174s_arcComp
  constructor
  · intro h
    have h' : (ρ.reconnect u).SameCycle w.1 (ρ.pair a) := Quotient.exact (Sum.inl.inj h)
    rw [← hr] at h'
    exact (ρ.r174s_reconnect_sameCycle_pair_iff h1 hk).mp h'
  · intro h
    have h' := (ρ.r174s_reconnect_sameCycle_pair_iff h1 hk).mpr h
    rw [hr] at h'
    exact congrArg Sum.inl (Quotient.sound h')

/-- The two arc circles are distinct. -/
theorem r174s_arcComp_ne (u : ρ.M) : ρ.r174s_arcComp u u ≠ ρ.r174s_arcComp u (ρ.pair u) := by
  unfold r174s_arcComp
  rw [ρ.pair_invol]
  exact (ρ.smooth_comps_ne_of_self u (ρ.r174s_isSelfCrossing h1 u)).symm

end OneCircle

end Record

/-- **First return after swapping a non-retained point with its non-retained predecessor.**  If `g b = a`
with `a, b` outside the retained set `p`, the permutation `g * swap a b` (which fixes `a` and sends `b`
to `g a`) has the same first return to `p` as `g`: both first returns to `(· ≠ a)` agree pointwise
(`firstReturn_apply_of_mem` / `_of_not_mem`), and the first return to `p` factors through it
(`firstReturn_firstReturn`). -/
theorem r174s_firstReturn_mul_swap_of_apply_eq {β : Type*} [Fintype β] [DecidableEq β]
    (g : Equiv.Perm β) (p : β → Prop) [DecidablePred p] {a b : β} (hgb : g b = a) (hab : a ≠ b)
    (ha : ¬ p a) :
    firstReturn (g * Equiv.swap a b) p = firstReturn g p := by
  have hga : g a ≠ a := fun h => hab (g.injective (h.trans hgb.symm))
  have hq : ∀ m, p m → m ≠ a := fun m hm h => ha (h ▸ hm)
  have key : firstReturn (g * Equiv.swap a b) (fun m => m ≠ a) = firstReturn g (fun m => m ≠ a) := by
    refine Equiv.ext fun m => Subtype.ext ?_
    by_cases hmb : m.1 = b
    · rw [firstReturn_apply_of_mem (g * Equiv.swap a b) _ m
          (by rw [Equiv.Perm.mul_apply, hmb, Equiv.swap_apply_right]; exact hga),
        firstReturn_apply_of_not_mem g _ m (by rw [hmb, hgb]; exact not_not.mpr rfl)
          (by rw [hmb, hgb]; exact hga),
        Equiv.Perm.mul_apply, hmb, Equiv.swap_apply_right, hgb]
    · have hsw : (g * Equiv.swap a b) m.1 = g m.1 := by
        rw [Equiv.Perm.mul_apply, Equiv.swap_apply_of_ne_of_ne m.2 hmb]
      have hgm : g m.1 ≠ a := fun h => hmb (g.injective (h.trans hgb.symm))
      rw [firstReturn_apply_of_mem _ _ m (by rw [hsw]; exact hgm),
        firstReturn_apply_of_mem g _ m hgm, hsw]
  refine Equiv.ext fun m => Subtype.ext ?_
  have hand : ∀ z, p z ↔ (z ≠ a ∧ p z) := fun z => ⟨fun h => ⟨hq z h, h⟩, fun h => h.2⟩
  have c1 : (firstReturn (g * Equiv.swap a b) p m).1 =
      (firstReturn (g * Equiv.swap a b) (fun z => z ≠ a ∧ p z) ⟨m.1, (hand _).mp m.2⟩).1 :=
    firstReturn_val_congr _ _ _ _ hand m (fun _ => rfl)
  have c2 : (firstReturn g p m).1 =
      (firstReturn g (fun z => z ≠ a ∧ p z) ⟨m.1, (hand _).mp m.2⟩).1 :=
    firstReturn_val_congr _ _ _ _ hand m (fun _ => rfl)
  have e1 := firstReturn_firstReturn (g * Equiv.swap a b) (fun z => z ≠ a) p ⟨⟨m.1, hq _ m.2⟩, m.2⟩
  have e2 := firstReturn_firstReturn g (fun z => z ≠ a) p ⟨⟨m.1, hq _ m.2⟩, m.2⟩
  rw [c1, c2, ← e1, ← e2, key]

namespace Record

variable (ρ : Record) (h1 : ρ.componentCount = 1)
include h1

/-- **The first return to the arc-internal crossings is the same for `s` and for `s₁ = s ∘ swap(u, τ u)`.**
Through the retained set `P⁺ = P ∪ {u, τ u}`: `firstReturn s₁ P⁺ = firstReturn s P⁺ * swap u (τ u)`
(`firstReturn_mul_swap`), the `P⁺`-first return of `τ u` along `s` is `u` (no `P`-point on the other arc),
so the swap is harmless (`r174s_firstReturn_mul_swap_of_apply_eq`), and both first returns to `P` factor
through `P⁺` (`firstReturn_firstReturn`). -/
theorem r174s_firstReturn_reconnect_eq (u : ρ.M) (P : ρ.M → Prop) [DecidablePred P]
    (hP : ∀ m, P m ↔ ρ.CrossKeep (ρ.r174s_KeepArc u) m) (w : {m // P m}) :
    (firstReturn (ρ.reconnect u) P w).1 = (firstReturn ρ.succ P w).1 := by
  classical
  have hPu : ¬ P u := by
    intro h
    have h' := ((ρ.r174s_crossKeep_keepArc_iff u u).mp ((hP u).mp h)).1
    rw [ArcBetween, ρ.steps_self] at h'
    exact lt_irrefl 0 h'.1
  have hPp : ¬ P (ρ.pair u) := by
    intro h
    exact lt_irrefl _ ((ρ.r174s_crossKeep_keepArc_iff u _).mp ((hP _).mp h)).1.2
  let Pp : ρ.M → Prop := fun m => P m ∨ m = u ∨ m = ρ.pair u
  have hPpu : Pp u := Or.inr (Or.inl rfl)
  have hPpp : Pp (ρ.pair u) := Or.inr (Or.inr rfl)
  have hsub : ∀ m, P m → Pp m := fun m h => Or.inl h
  have hand : ∀ m, P m ↔ (Pp m ∧ P m) := fun m => ⟨fun h => ⟨Or.inl h, h⟩, fun h => h.2⟩
  have hL : 0 < ρ.steps u (ρ.pair u) := (ρ.steps_pos_iff h1 u _).mpr (ρ.ne_pair u)
  have hcard := ρ.steps_lt_card h1 u (ρ.pair u)
  -- the `P⁺`-first return of `τ u` is `u`
  have hg : firstReturn ρ.succ Pp ⟨ρ.pair u, hPpp⟩ = ⟨u, hPpu⟩ := by
    apply Subtype.ext
    show (firstReturn ρ.succ Pp ⟨ρ.pair u, hPpp⟩).1 = u
    rw [ρ.firstReturn_val_eq_iff Pp h1 ⟨ρ.pair u, hPpp⟩ ⟨u, hPpu, ρ.ne_pair u⟩ u]
    refine ⟨hPpu, ρ.ne_pair u, fun k hk hku => ?_⟩
    rcases hk with hk | rfl | rfl
    · have hk' := (ρ.r174s_arcBetween_pair_iff h1 u k).mp
        ((ρ.r174s_crossKeep_keepArc_iff u k).mp ((hP k).mp hk)).1
      rw [ρ.steps_eq_of_base h1 u (ρ.pair u) u, ρ.steps_eq_of_base h1 u (ρ.pair u) k, ρ.steps_self]
      split_ifs <;> omega
    · exact le_refl _
    · exact absurd rfl hku
  have e1 : (firstReturn (ρ.reconnect u) P w).1 =
      ((firstReturn (firstReturn (ρ.reconnect u) Pp) (fun m => P m.1))
        ⟨⟨w.1, hsub _ w.2⟩, w.2⟩).1.1 := by
    rw [firstReturn_firstReturn]
    exact firstReturn_val_congr _ _ P (fun m => Pp m ∧ P m) hand w (fun _ => rfl)
  have e2 : (firstReturn ρ.succ P w).1 =
      ((firstReturn (firstReturn ρ.succ Pp) (fun m => P m.1)) ⟨⟨w.1, hsub _ w.2⟩, w.2⟩).1.1 := by
    rw [firstReturn_firstReturn]
    exact firstReturn_val_congr _ _ P (fun m => Pp m ∧ P m) hand w (fun _ => rfl)
  have e3 : firstReturn (ρ.reconnect u) Pp =
      firstReturn ρ.succ Pp * Equiv.swap ⟨u, hPpu⟩ ⟨ρ.pair u, hPpp⟩ :=
    firstReturn_mul_swap ρ.succ Pp u (ρ.pair u) hPpu hPpp
  have e4 : firstReturn (firstReturn ρ.succ Pp * Equiv.swap ⟨u, hPpu⟩ ⟨ρ.pair u, hPpp⟩)
      (fun m => P m.1) = firstReturn (firstReturn ρ.succ Pp) (fun m => P m.1) :=
    r174s_firstReturn_mul_swap_of_apply_eq (firstReturn ρ.succ Pp) (fun m => P m.1) hg
      (fun h => ρ.ne_pair u (congrArg Subtype.val h)) hPu
  rw [e1, e2, e3, e4]

/-- **Restricting the smoothing at `u` to an arc circle is the arc-internal crossing record**:
`(ρ.smooth u).restrict {arc circle of a} ≅ ρ.restrictCrossings (r174s_KeepArc a)` for `a ∈ {u, τ u}`
(occurrences: `r174s_smooth_comp_eq_iff`; successor: `firstReturn_firstReturn` and
`r174s_firstReturn_reconnect_eq`; both records have one circle). -/
theorem r174s_restrict_smooth_iso {u a : ρ.M} (ha : a = u ∨ a = ρ.pair u) :
    Nonempty (RecordIso ((ρ.smooth u).restrict {ρ.r174s_arcComp u a})
      (ρ.restrictCrossings (ρ.r174s_KeepArc a))) := by
  classical
  have hr : ρ.reconnect a = ρ.reconnect u := by
    rcases ha with rfl | rfl
    · rfl
    · exact ρ.reconnect_pair u
  have hk : ∀ m, ρ.SmoothKeep u m ↔ ρ.SmoothKeep a m := by
    intro m
    rcases ha with rfl | rfl
    · exact Iff.rfl
    · exact (ρ.smoothKeep_pair_eq u m).symm
  have hkeep : ∀ w : (ρ.smooth u).M,
      (ρ.smooth u).RestrictKeep {ρ.r174s_arcComp u a} w ↔ ρ.CrossKeep (ρ.r174s_KeepArc a) w.1 := by
    intro w
    rw [ρ.r174s_crossKeep_keepArc_iff]
    show ((ρ.smooth u).comp w ∈ ({ρ.r174s_arcComp u a} : Finset _) ∧
      (ρ.smooth u).comp ((ρ.smooth u).pair w) ∈ ({ρ.r174s_arcComp u a} : Finset _)) ↔ _
    rw [Finset.mem_singleton, Finset.mem_singleton, ρ.r174s_smooth_comp_eq_iff h1 ha,
      ρ.r174s_smooth_comp_eq_iff h1 ha]
    exact Iff.rfl
  have hsk : ∀ m, ρ.CrossKeep (ρ.r174s_KeepArc a) m → ρ.SmoothKeep u m := by
    intro m hm
    rw [hk, ρ.smoothKeep_iff]
    obtain ⟨h1', -⟩ := (ρ.r174s_crossKeep_keepArc_iff a m).mp hm
    obtain ⟨hpos, hlt⟩ := (ρ.r174s_arcBetween_pair_iff h1 a m).mp h1'
    constructor
    · rintro rfl
      rw [ρ.steps_self] at hpos
      exact lt_irrefl _ hpos
    · rintro rfl
      exact lt_irrefl _ hlt
  let Φ : ((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).M ≃
      (ρ.restrictCrossings (ρ.r174s_KeepArc a)).M :=
    { toFun := fun w => ⟨w.1.1, (hkeep w.1).mp w.2⟩
      invFun := fun m => ⟨⟨m.1, hsk m.1 m.2⟩, (hkeep ⟨m.1, hsk m.1 m.2⟩).mpr m.2⟩
      left_inv := fun w => rfl
      right_inv := fun m => rfl }
  refine ⟨RecordIso.ofOccOfCard Φ ?_ (fun w => rfl) (fun w => rfl) (fun w => rfl) ?_⟩
  · intro w
    apply Subtype.ext
    have s1 : (((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).succ w).1.1 =
        (firstReturn (ρ.reconnect u) (fun m => ρ.SmoothKeep u m ∧ ρ.CrossKeep (ρ.r174s_KeepArc a) m)
          ⟨w.1.1, w.1.2, (hkeep w.1).mp w.2⟩).1 := by
      refine Eq.trans ?_ (firstReturn_firstReturn (ρ.reconnect u) (ρ.SmoothKeep u)
        (ρ.CrossKeep (ρ.r174s_KeepArc a)) ⟨w.1, (hkeep w.1).mp w.2⟩)
      exact congrArg Subtype.val (firstReturn_val_congr _ _ _ _ hkeep w (fun _ => rfl))
    have s2 : (firstReturn (ρ.reconnect u)
        (fun m => ρ.SmoothKeep u m ∧ ρ.CrossKeep (ρ.r174s_KeepArc a) m)
          ⟨w.1.1, w.1.2, (hkeep w.1).mp w.2⟩).1 =
        (firstReturn (ρ.reconnect a) (ρ.CrossKeep (ρ.r174s_KeepArc a))
          ⟨w.1.1, (hkeep w.1).mp w.2⟩).1 :=
      firstReturn_val_congr _ _ _ _ (fun m => ⟨fun h => h.2, fun h => ⟨hsk m h, h⟩⟩) _
        (fun n => by rw [hr])
    have s3 := ρ.r174s_firstReturn_reconnect_eq h1 a (ρ.CrossKeep (ρ.r174s_KeepArc a))
      (fun _ => Iff.rfl) ⟨w.1.1, (hkeep w.1).mp w.2⟩
    exact s1.trans (s2.trans s3)
  · show ((ρ.smooth u).restrict {ρ.r174s_arcComp u a}).componentCount =
      (ρ.restrictCrossings (ρ.r174s_KeepArc a)).componentCount
    rw [ρ.componentCount_restrictCrossings, h1, (ρ.smooth u).componentCount_restrict,
      Finset.card_singleton]

end Record

/-! ## C. Diagram level: the library smoothing `D₀`, its two components and their knot restrictions

The counting lemmas `r174s_writhe_restrict … r174s_writhe_two_component` and `r174s_record_writhe_smooth`
are the U110-H lemmas `s7h_*` of SM/CornerChainUnits.lean (accepted library material not in this file's
import chain), reproduced verbatim under the `r174s_` prefix. -/

/-- The writhe of a block restriction is the sum of the signs of the internal crossings of the block
(`Shadow.restrictCrossingEquiv`, `Diagram.restrict_sign`). -/
theorem r174s_writhe_restrict (D : Diagram) (B : Finset (Fin D.Γ.c)) (hB : B.Nonempty) :
    (D.restrict B hB).writhe =
      ∑ x : {x : D.Γ.Crossing // ∀ s ∈ x.val, s.1 ∈ B}, (D.sign x.1 : ℤ) := by
  unfold Diagram.writhe
  exact Fintype.sum_equiv (D.Γ.restrictCrossingEquiv B hB) _ _
    (fun y => by rw [D.restrict_sign B hB y]; rfl)

/-- The self crossings of the component `i`: both strands on `i` (`val_eq_pair`). -/
theorem r174s_self_iff (D : Diagram) (i : Fin D.Γ.c) (x : D.Γ.Crossing) :
    (∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) ↔
      (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i := by
  rw [D.val_eq_pair x]
  simp only [Finset.mem_insert, Finset.mem_singleton, forall_eq_or_imp, forall_eq]

/-- "their actual knot restrictions" (mp:lowest): the writhe of `D.knotRestrict i` is the sum of the
signs of the self crossings of component `i` (eq. s7c:crossing-partition, first two rows). -/
theorem r174s_writhe_knotRestrict (D : Diagram) (i : Fin D.Γ.c) :
    (D.knotRestrict i).writhe =
      ∑ x ∈ Finset.univ.filter
        (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i),
        (D.sign x : ℤ) := by
  unfold Diagram.knotRestrict
  rw [r174s_writhe_restrict]
  have hfilt : Finset.univ.filter
      (fun x : D.Γ.Crossing => (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i) =
      Finset.univ.filter
        (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))) :=
    Finset.filter_congr fun x _ => (r174s_self_iff D i x).symm
  rw [hfilt]
  exact (Finset.sum_subtype (Finset.univ.filter
    (fun x : D.Γ.Crossing => ∀ s ∈ x.val, s.1 ∈ ({i} : Finset (Fin D.Γ.c))))
    (fun x => by simp) (fun x => (D.sign x : ℤ))).symm

/-- `2ℓ_ij` as a sum over the mixed crossings (each mixed crossing is exactly one ordered strand pair
`(s, t)` with `s` on `i`, `t` on `j`; eq. s7c:crossing-partition, third row). -/
theorem r174s_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (fun x : D.Γ.Crossing =>
        ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
        ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)), (D.sign x : ℤ) := by
  classical
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  -- the term of an ordered pair is nonzero only when it is a mixed pair
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · -- lands in the mixed crossings
    intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · -- injective: the pair is recovered from the crossing by the components
    intro p₁ _ hne₁ p₂ _ hne₂ e
    have hm₁ := hmp p₁ hne₁
    have hm₂ := hmp p₂ hne₂
    have e' : ({p₁.1, p₁.2} : Finset D.Γ.Strand) = {p₂.1, p₂.2} := congrArg Subtype.val e
    have hs : p₁.1 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_self _ _
    have ht : p₁.2 ∈ ({p₂.1, p₂.2} : Finset D.Γ.Strand) := by
      rw [← e']; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    rw [Finset.mem_insert, Finset.mem_singleton] at hs ht
    refine Prod.ext ?_ ?_
    · exact hs.resolve_right fun h => hij (by rw [← hm₁.1, h, hm₂.2.1])
    · exact ht.resolve_left fun h => hij (by rw [← hm₂.1, ← h, hm₁.2.1])
  · -- surjective onto the mixed crossings
    intro x hx _
    have hx' := (Finset.mem_filter.mp hx).2
    have hsgn : ((D.sign x : SignType) : ℤ) ≠ 0 := by
      rcases D.sign_eq_one_or_neg_one x with h | h <;> rw [h] <;> decide
    rcases hx' with ⟨ho, hu⟩ | ⟨ho, hu⟩
    · have hm : D.Γ.MixedPair i j (D.overStrand x) (D.underStrand x) :=
        ⟨ho, hu, by rw [← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.overStrand x, D.underStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.overStrand x, D.underStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext (D.val_eq_pair x).symm
        rw [e]; exact hsgn
      · exact Subtype.ext (D.val_eq_pair x).symm
    · have hm : D.Γ.MixedPair i j (D.underStrand x) (D.overStrand x) :=
        ⟨hu, ho, by rw [Finset.pair_comm, ← D.val_eq_pair x]; exact x.2⟩
      refine ⟨(D.underStrand x, D.overStrand x), Finset.mem_univ _, ?_, ?_⟩
      · rw [dite_eq_left hm]
        have e : (⟨{D.underStrand x, D.overStrand x}, hm.2.2⟩ : D.Γ.Crossing) = x :=
          Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
        rw [e]; exact hsgn
      · exact Subtype.ext ((Finset.pair_comm _ _).trans (D.val_eq_pair x).symm)
  · -- the terms agree
    intro p _ hne
    rw [dite_eq_left (hmp p hne)]

/-- With two components `i ≠ j`, every component is `i` or `j`. -/
theorem r174s_comp_eq_or (D : Diagram) {i j : Fin D.Γ.c} (h2 : D.componentCount = 2) (hij : i ≠ j)
    (c : Fin D.Γ.c) : c = i ∨ c = j := by
  have huniv : ({i, j} : Finset (Fin D.Γ.c)) = Finset.univ := by
    apply Finset.eq_of_subset_of_card_le (Finset.subset_univ _)
    rw [Finset.card_pair hij, Finset.card_univ, Fintype.card_fin]
    exact h2.le
  have hc : c ∈ ({i, j} : Finset (Fin D.Γ.c)) := by rw [huniv]; exact Finset.mem_univ c
  simpa only [Finset.mem_insert, Finset.mem_singleton] using hc

/-- A two-component diagram has two distinct component indices. -/
theorem r174s_exists_two_components (D : Diagram) (h2 : D.componentCount = 2) :
    ∃ i j : Fin D.Γ.c, i ≠ j := by
  unfold Diagram.componentCount at h2
  refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ?_⟩
  intro h
  have := congrArg Fin.val h
  simp at this

/-- **eq. s7c:crossing-partition as a writhe identity**: for a two-component diagram the writhe is the
sum of the writhes of the two knot restrictions plus `2ℓ` ("the self crossings contribute `w₁ + w₂`,
the mixed crossings of `D_A` contribute `2ℓ`", sm-4:649-651). -/
theorem r174s_writhe_two_component (D : Diagram) (i j : Fin D.Γ.c) (h2 : D.componentCount = 2)
    (hij : i ≠ j) :
    D.writhe = (D.knotRestrict i).writhe + (D.knotRestrict j).writhe + twoLinking D i j := by
  have key : ∀ x : D.Γ.Crossing, (D.sign x : ℤ) =
      (if (D.overStrand x).1 = i ∧ (D.underStrand x).1 = i then (D.sign x : ℤ) else 0) +
      (if (D.overStrand x).1 = j ∧ (D.underStrand x).1 = j then (D.sign x : ℤ) else 0) +
      (if ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
          ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i) then (D.sign x : ℤ) else 0) := by
    intro x
    have hji : j ≠ i := hij.symm
    rcases r174s_comp_eq_or D h2 hij (D.overStrand x).1 with ho | ho <;>
      rcases r174s_comp_eq_or D h2 hij (D.underStrand x).1 with hu | hu <;>
      simp [ho, hu, hij, hji]
  rw [r174s_writhe_knotRestrict, r174s_writhe_knotRestrict, twoLinking, r174s_mixedSignSum_eq D i j hij]
  unfold Diagram.writhe
  rw [Finset.sum_congr rfl (fun x _ => key x), Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.sum_filter, ← Finset.sum_filter, ← Finset.sum_filter]


/-- The record-level smoothing drops the writhe by the sign of the smoothed crossing (the two erased
occurrences carry that sign; `smooth_sgn`, `sgn_pair`). -/
theorem r174s_record_writhe_smooth (ρ : Record) (v : ρ.M) :
    (ρ.smooth v).writhe = ρ.writhe - (ρ.sgn v : ℤ) := by
  have h2 := ρ.two_mul_writhe
  -- the retained occurrences: the sum over the smoothing's occurrence set is the filtered sum
  have h1 : 2 * (ρ.smooth v).writhe = ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) := by
    rw [Record.two_mul_writhe]
    refine (Fintype.sum_equiv
      (Equiv.refl _ : (ρ.smooth v).M ≃ {w : ρ.M // ρ.SmoothKeep v w}) _
      (fun w => (ρ.sgn w.1 : ℤ)) (fun w => rfl)).trans ?_
    exact (Finset.sum_subtype (Finset.univ.filter (ρ.SmoothKeep v)) (fun w => by simp)
      (fun w => (ρ.sgn w : ℤ))).symm
  -- the two erased occurrences carry the sign of `v`
  have h4 : ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      2 * (ρ.sgn v : ℤ) := by
    have hf : Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w) = {v, ρ.pair v} := by
      ext w
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Record.SmoothKeep, not_not]
    rw [hf, Finset.sum_pair (ρ.pair_ne v).symm, ρ.sgn_pair]
    ring
  have h5 : ∑ w ∈ Finset.univ.filter (ρ.SmoothKeep v), (ρ.sgn w : ℤ) +
      ∑ w ∈ Finset.univ.filter (fun w => ¬ ρ.SmoothKeep v w), (ρ.sgn w : ℤ) =
      ∑ w, (ρ.sgn w : ℤ) :=
    Finset.sum_filter_add_sum_filter_not Finset.univ (ρ.SmoothKeep v) (fun w => (ρ.sgn w : ℤ))
  omega



/-- A diagram with the record of the smoothing of a one-component diagram has two components
("A self crossing splits one parameter circle into two"; `componentCount_smooth_of_self`). -/
theorem r174s_componentCount_of_smooth_iso (D D₀ : Diagram) (hD : D.componentCount = 1)
    (v : D.Γ.Visit) (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.componentCount = 2 := by
  obtain ⟨ι⟩ := h
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  rw [← D₀.record_componentCount, ι.componentCount_eq,
    D.record.componentCount_smooth_of_self v (D.record.r174s_isSelfCrossing h1 v), h1]

/-- Any diagram with the record of the smoothing of `D` at `v` has writhe `w(D) − σ(v)`. -/
theorem r174s_writhe_of_smooth_iso (D D₀ : Diagram) (v : D.Γ.Visit)
    (h : Nonempty (RecordIso D₀.record (D.record.smooth v))) :
    D₀.writhe = D.writhe - (D.sign v.1 : ℤ) := by
  obtain ⟨ι⟩ := h
  rw [← D₀.record_writhe, ι.writhe_eq, r174s_record_writhe_smooth, D.record_writhe, D.record_sgn]

/-- **The knot restriction of a smoothing to an arc circle is the arc-internal crossing record of the
parent** (`restrict_record` → `RecordIso.restrict` along the smoothing clause → `r174s_restrict_smooth_iso`). -/
theorem r174s_knotRestrict_record_iso (D₀ D : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (ι : RecordIso D₀.record (D.record.smooth v)) {a : D.Γ.Visit} (ha : a = v ∨ a = D.record.pair v)
    (i : Fin D₀.Γ.c) (hi : ι.e i = D.record.r174s_arcComp v a) :
    Nonempty (RecordIso (D₀.knotRestrict i).record
      (D.record.restrictCrossings (D.record.r174s_KeepArc a))) := by
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  have e1 : RecordIso (D₀.knotRestrict i).record (D₀.record.restrict {i}) :=
    D₀.restrictRecordIso {i} (Finset.singleton_nonempty i)
  have e2 : RecordIso (D₀.record.restrict {i})
      ((D.record.smooth v).restrict {D.record.r174s_arcComp v a}) :=
    ι.restrict {i} {D.record.r174s_arcComp v a} (fun c => by
      rw [Finset.mem_singleton, Finset.mem_singleton, ← hi]
      exact ι.e.injective.eq_iff)
  obtain ⟨e3⟩ := D.record.r174s_restrict_smooth_iso h1 (u := v) (a := a) ha
  exact ⟨e1.trans (e2.trans e3)⟩

/-- `gsc_smoothing_split` is symmetric in the two components (`mixedSignSum_comm`). -/
theorem r174s_smoothing_split_swap {D₀ : Diagram} {i j : Fin D₀.Γ.c} {QA QB : R} {ℓ : ℤ}
    (h : gsc_smoothing_split D₀ i j QA QB ℓ) : gsc_smoothing_split D₀ j i QB QA ℓ := by
  obtain ⟨h2, hij, hA, hB, hℓ⟩ := h
  refine ⟨h2, hij.symm, hB, hA, ?_⟩
  unfold CV.IsLinkingNumber at hℓ ⊢
  rw [mixedSignSum_comm]
  exact hℓ

/-- **The smoothing split from the two arc records.**  If `D₀` has the record of the smoothing of the
one-component `D` at `v`, and the arc-internal crossing records of the two arcs of `v` are the records of
the one-component diagrams `K₁`, `K₂`, then `D₀` has two components `i ≠ j` whose knot restrictions have
the polynomials of `K₁`, `K₂` (ax:gausscode), with the linking number `ℓ` and the writhe count
`w(D₀) = w(K₁) + w(K₂) + 2ℓ`. -/
theorem r174s_split_of_arc_isos (D₀ D : Diagram) (hD : D.componentCount = 1) (v : D.Γ.Visit)
    (hι : Nonempty (RecordIso D₀.record (D.record.smooth v)))
    (K₁ K₂ : Diagram) (h₁ : K₁.componentCount = 1) (h₂ : K₂.componentCount = 1)
    (hA : Nonempty (RecordIso (D.record.restrictCrossings (D.record.r174s_KeepArc v)) K₁.record))
    (hB : Nonempty (RecordIso (D.record.restrictCrossings
      (D.record.r174s_KeepArc (D.record.pair v))) K₂.record)) :
    ∃ (i j : Fin D₀.Γ.c) (ℓ : ℤ), gsc_smoothing_split D₀ i j (homfly K₁) (homfly K₂) ℓ ∧
      D₀.writhe = K₁.writhe + K₂.writhe + 2 * ℓ := by
  obtain ⟨ι⟩ := hι
  obtain ⟨κ₁⟩ := hA
  obtain ⟨κ₂⟩ := hB
  have h1 : D.record.componentCount = 1 := by rw [D.record_componentCount]; exact hD
  have h2 : D₀.componentCount = 2 := r174s_componentCount_of_smooth_iso D D₀ hD v ⟨ι⟩
  obtain ⟨i, hi⟩ : ∃ i : Fin D₀.Γ.c, ι.e i = D.record.r174s_arcComp v v :=
    ⟨ι.e.symm _, ι.e.apply_symm_apply _⟩
  obtain ⟨j, hj⟩ : ∃ j : Fin D₀.Γ.c, ι.e j = D.record.r174s_arcComp v (D.record.pair v) :=
    ⟨ι.e.symm _, ι.e.apply_symm_apply _⟩
  have hij : i ≠ j := by
    intro h
    apply D.record.r174s_arcComp_ne h1 v
    rw [← hi, ← hj, h]
  obtain ⟨ε₁⟩ := r174s_knotRestrict_record_iso D₀ D hD v ι (Or.inl rfl) i hi
  obtain ⟨ε₂⟩ := r174s_knotRestrict_record_iso D₀ D hD v ι (Or.inr rfl) j hj
  obtain ⟨ℓ, hℓ⟩ := CV.exists_linkingNumber D₀ i j hij
  refine ⟨i, j, ℓ, ⟨h2, hij, ?_, ?_, hℓ⟩, ?_⟩
  · exact CV.gausscode_polynomial _ _ (D₀.knotRestrict_componentCount i) h₁ (ε₁.trans κ₁)
  · exact CV.gausscode_polynomial _ _ (D₀.knotRestrict_componentCount j) h₂ (ε₂.trans κ₂)
  · rw [r174s_writhe_two_component D₀ i j h2 hij, hℓ.twoLinking_eq,
      ← (D₀.knotRestrict i).record_writhe, (ε₁.trans κ₁).writhe_eq, K₁.record_writhe,
      ← (D₀.knotRestrict j).record_writhe, (ε₂.trans κ₂).writhe_eq, K₂.record_writhe]

/-! ## A. The library smoothing `D₀ := smoothDiagram` at `qx`, with its record clause -/

/-- **The oriented smoothing `D₀` of the ledger** (GSC §3 "let `D_0` be its oriented smoothing"): the
library construction `smoothDiagram` at the crossing `qx` (the `D₀` of `exists_smoothing`,
`exists_smoothing_record_visit`, `exists_smoothing_counts`). -/
def r174s_D₀ (D_H : Diagram) (qx : D_H.Γ.Crossing) : Diagram :=
  Smoothing.smoothDiagram D_H qx (Smoothing.eps D_H qx) (Smoothing.eps_small D_H qx)

theorem r174s_D₀_isOrientedSmoothing (D_H : Diagram) (qx : D_H.Γ.Crossing) :
    IsOrientedSmoothing D_H qx (r174s_D₀ D_H qx) :=
  Smoothing.isOrientedSmoothing_smoothDiagram D_H qx _ (Smoothing.eps_small D_H qx)

/-- The record clause of the library smoothing (`smoothDiagram_record`). -/
theorem r174s_D₀_record (D_H : Diagram) (qx : D_H.Γ.Crossing) :
    Nonempty (RecordIso (r174s_D₀ D_H qx).record (D_H.record.smooth (D_H.overVisit qx))) :=
  Smoothing.smoothDiagram_record D_H qx _ (Smoothing.eps_small D_H qx)

theorem r174s_D₀_componentCount (D_H : Diagram) (hH : D_H.componentCount = 1) (qx : D_H.Γ.Crossing) :
    (r174s_D₀ D_H qx).componentCount = 2 :=
  r174s_componentCount_of_smooth_iso D_H _ hH _ (r174s_D₀_record D_H qx)

/-- The writhe of the smoothing at a positive crossing: `w(D₀) = w(D_H) − 1`. -/
theorem r174s_D₀_writhe (D_H : Diagram) (qx : D_H.Γ.Crossing) (hpos : D_H.IsPositive qx) :
    (r174s_D₀ D_H qx).writhe = D_H.writhe - 1 := by
  rw [r174s_writhe_of_smooth_iso D_H _ _ (r174s_D₀_record D_H qx), D_H.overVisit_fst,
    (D_H.isPositive_iff_sign_eq_one qx).mp hpos]
  rfl

/-- **The smoothing split of `D₀ = r174s_D₀ D_H qx` from an arc-record identification**: if for one of
the two occurrences `u` of `qx` the arc-internal crossing records of the arcs `(u, τ u)`, `(τ u, u)` of
`D_H.record` are the records of the one-component diagrams `K₁`, `K₂`, then `D₀` splits with the
polynomials of `K₁`, `K₂` and `w(D_H) = w(K₁) + w(K₂) + 2ℓ + 1`. -/
theorem r174s_split_of_arc_prop (D_H : Diagram) (hH : D_H.componentCount = 1) (qx : D_H.Γ.Crossing)
    (hpos : D_H.IsPositive qx) (K₁ K₂ : Diagram) (h₁ : K₁.componentCount = 1)
    (h₂ : K₂.componentCount = 1)
    (hsplit : ∃ u : D_H.Γ.Visit, u.1 = qx ∧
      Nonempty (RecordIso (D_H.record.restrictCrossings (D_H.record.r174s_KeepArc u)) K₁.record) ∧
      Nonempty (RecordIso (D_H.record.restrictCrossings
        (D_H.record.r174s_KeepArc (D_H.record.pair u))) K₂.record)) :
    ∃ (i j : Fin (r174s_D₀ D_H qx).Γ.c) (ℓ : ℤ),
      gsc_smoothing_split (r174s_D₀ D_H qx) i j (homfly K₁) (homfly K₂) ℓ ∧
      D_H.writhe = K₁.writhe + K₂.writhe + 2 * ℓ + 1 := by
  obtain ⟨u, hu, hA, hB⟩ := hsplit
  have hrec := r174s_D₀_record D_H qx
  have hw := r174s_D₀_writhe D_H qx hpos
  rcases D_H.visit_eq_over_or_under u with huv | huv
  · rw [hu] at huv
    subst huv
    obtain ⟨i, j, ℓ, hs, hw'⟩ := r174s_split_of_arc_isos (r174s_D₀ D_H qx) D_H hH
      (D_H.overVisit qx) hrec K₁ K₂ h₁ h₂ hA hB
    exact ⟨i, j, ℓ, hs, by omega⟩
  · rw [hu] at huv
    subst huv
    have hp : D_H.record.pair (D_H.overVisit qx) = D_H.underVisit qx := D_H.twin_overVisit qx
    have hpp : D_H.record.pair (D_H.underVisit qx) = D_H.overVisit qx := by
      rw [← hp, D_H.record.pair_invol]
    rw [hpp] at hB
    rw [← hp] at hA
    obtain ⟨i, j, ℓ, hs, hw'⟩ := r174s_split_of_arc_isos (r174s_D₀ D_H qx) D_H hH
      (D_H.overVisit qx) hrec K₂ K₁ h₂ h₁ hB hA
    exact ⟨j, i, ℓ, r174s_smoothing_split_swap hs, by omega⟩

/-! ## D. The ledger fields of row 174: `D₀`, `qx`, `fulltwist`, `i`, `j`, `ℓ`, `smoothing`, `writhe_count` -/

/-- `gsc_fulltwist_of_bigon` with the smoothing pinned to `r174s_D₀` (the same proof: the `D₀` of
`exists_smoothing` IS `r174s_D₀ D_H q`). -/
theorem r174s_fulltwist_triple_of_bigon (D_L D_H : Diagram) (q : D_H.Γ.Crossing) (hq : D_H.IsPositive q)
    (hH : D_H.componentCount = 1) (hL : D_L.componentCount = 1) (B : BigonData (D_H.switch q))
    (hrec : Nonempty (RecordIso B.reducedRecord D_L.record)) :
    gsc_fulltwist_triple D_L D_H (r174s_D₀ D_H q) q := by
  obtain ⟨D', hR, hc, ⟨ι⟩⟩ := exists_rii_deletion _ B
  obtain ⟨κ⟩ := hrec
  exact ⟨hq, r174s_D₀_isOrientedSmoothing D_H q, D', Relation.ReflTransGen.single hR.symm,
    CV.gausscode_polynomial D' D_L (hc.trans hH) hL (ι.trans κ)⟩

section R174SConsumer

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}

/-- The positive crossing `a = x'` of `D_H = carrierDiagram q'` — the ledger's `qx`: the lifted `x'`
(`s174_lift`), as in `s174_site` and `s174_fulltwist_of_hrec`. -/
abbrev r174s_qx (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q') :
    (CV.carrierDiagram hn hG' hSm' q').Γ.Crossing :=
  s174_lift hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' _ hx'

/-- **(c′) The `fulltwist` field with `D₀ := r174s_D₀`** — `s174_fulltwist_of_hrec` with the smoothing
named (no existential): from (a) `s174_site` and (b) `s174_hrec_prop`. -/
theorem r174s_fulltwist_of_hrec
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
    gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q')
      (r174s_D₀ _ (r174s_qx hn hG' hSm' q' hx')) (r174s_qx hn hG' hSm' q' hx') := by
  obtain ⟨B, -, hB⟩ := s174_site hn hG hG' D hsgn hSm' q' hx' hw'
  have hq : (CV.carrierDiagram hn hG' hSm' q').IsPositive (r174s_qx hn hG' hSm' q' hx') :=
    geoPositiveLift_isPositive hn _ _ q' _
  have hrec' : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hSm qAB).record) := by
    rcases hB with ⟨hy, hz⟩ | ⟨hy, hz⟩
    · rw [s174_reducedRecord_eq B hy hz]; exact hrec
    · rw [s174_reducedRecord_eq_swap B hy hz]; exact hrec
  exact r174s_fulltwist_triple_of_bigon _ _ _ hq rfl rfl B hrec'

/-- **BLACK BOX (consumer obligation — U_R174_REPORT §4 items 1–2 in arc form; STATED, not proved):
the two arcs of `x'` on the `E`-side lift carry the `P-ac` records of `A` and `B`.**  For one of the two
occurrences `u` of `x'` on `D_H = carrierDiagram q'` (`q' = τ qAB`), the crossings of `D_H` internal to
the open arc `(u, τ u)` — the residual crossings of the `A`-string, GSC masks (9a) "a mask-zero survivor
is a residual crossing of the corresponding `P-ac` carrier, a mask-`xw` survivor is a mixed crossing" —
form, with the first-return cyclic order, bits and signs, the record of the `P-ac` lift of `A`
(`carrierDiagram hn hG hSxw qA`), and those internal to the other arc the record of the lift of `B`.
Content: `E = b a A c a B c b C`; the carrier `AB'` of `E-b` reads `x'(ℓ₁) [A] w'(ℓ₂) x'(ℓ₂) [B] w'(ℓ₃)`
(lem:carrierword: on the independent support the carrier inherits the order of `P'`, `arcBetween_iff_key`),
the `P-ac` carriers `A = (m(ℓ₁) [A])`, `B = ([B] m(ℓ₃))` read the same strings on `P` (A7 exactness of the
non-triangle visits, `D.gauss`; `D.sign_eq` for the divide bits; both lifts positive).  Route:
`GT_owner_transport` on good marks for the crossing correspondence, `GT_homfly_wall_gen`-shaped visit
bijections (twin-, key-order- and sign-compatible) → `CV.recordIsoOfData`; estimate 1.5–2.5k lines
(Site_174_REPORT §3 route, steps 2–5, applied to both arcs).  Consumed only as a hypothesis. -/
def r174s_arc_rec_prop (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w})) : Prop :=
  ∃ u : (CV.carrierDiagram hn hG' hSm' q').Γ.Visit, u.1 = r174s_qx hn hG' hSm' q' hx' ∧
    Nonempty (RecordIso ((CV.carrierDiagram hn hG' hSm' q').record.restrictCrossings
        ((CV.carrierDiagram hn hG' hSm' q').record.r174s_KeepArc u))
      (CV.carrierDiagram hn hG hSxw qA).record) ∧
    Nonempty (RecordIso ((CV.carrierDiagram hn hG' hSm' q').record.restrictCrossings
        ((CV.carrierDiagram hn hG' hSm' q').record.r174s_KeepArc
          ((CV.carrierDiagram hn hG' hSm' q').record.pair u)))
      (CV.carrierDiagram hn hG hSxw qB).record)

/-- **Items 5–6 of U_R174 §4 on the `GT_Endpoint` configuration**: from the arc-record black box, the
library smoothing `D₀ = r174s_D₀ D_H qx` of `D_H = carrierDiagram q'` at `qx = x'` has two components
`i ≠ j` with `homfly (D₀.knotRestrict i) = Q_A`, `homfly (D₀.knotRestrict j) = Q_B` (the pair-row
grouped polynomials, `GT_groupedPoly_eq_homfly`), the linking number `ℓ`, and the writhe count
`w_H = w_A + w_B + 2ℓ + 1` (all crossings positive: `w(D₀) = w_H − 1 = w_A + w_B + 2ℓ`). -/
theorem r174s_smoothing_split_of_arc (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hsplit : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB) :
    ∃ (i j : Fin (r174s_D₀ (CV.carrierDiagram hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx')).Γ.c)
      (ℓ : ℤ),
      gsc_smoothing_split (r174s_D₀ (CV.carrierDiagram hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx'))
        i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ ∧
      CV.groupedWrithe hG' q' = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ + 1 := by
  obtain ⟨i, j, ℓ, hs, hw⟩ := r174s_split_of_arc_prop (CV.carrierDiagram hn hG' hSm' q')
    (gsc_carrierDiagram_componentCount hn hG' hSm' q') (r174s_qx hn hG' hSm' q' hx')
    (geoPositiveLift_isPositive hn _ _ q' _)
    (CV.carrierDiagram hn hG hSxw qA) (CV.carrierDiagram hn hG hSxw qB)
    (gsc_carrierDiagram_componentCount hn hG hSxw qA) (gsc_carrierDiagram_componentCount hn hG hSxw qB)
    hsplit
  refine ⟨i, j, ℓ, ?_, ?_⟩
  · rw [GT_groupedPoly_eq_homfly hn hG hSxw qA, GT_groupedPoly_eq_homfly hn hG hSxw qB]
    exact hs
  · rw [← gsc_carrierDiagram_writhe hn hG' hSm' q', ← gsc_carrierDiagram_writhe hn hG hSxw qA,
      ← gsc_carrierDiagram_writhe hn hG hSxw qB]
    exact hw

/-- **The ledger fields `D₀, qx, fulltwist, i, j, ℓ, smoothing, writhe_count` of `gsc_Ledger`**, from the
site (`s174_site`), the two record black boxes (`s174_hrec_prop`, `r174s_arc_rec_prop`) and the wall count
`writhe_wall` (U_R174 §4 item 2, `w_H = w_L + 2`, a hypothesis here): with `q' := W.τ qAB` these are exactly
the fields, `D₀ := r174s_D₀`, `qx := r174s_qx`; (10) `w_L = w_A + w_B + 2ℓ − 1` is `w_H − 1 = w_A + w_B + 2ℓ`
read through (9). -/
theorem r174s_ledger_fields
    (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (hw' : crossingTransport hs w ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hrec : s174_hrec_prop hn hG hG' hSm hSm' qAB q' hx' hw')
    (hsplit : r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB)
    (hwall : CV.groupedWrithe hG' q' = CV.groupedWrithe hG qAB + 2) :
    ∃ (D₀ : Diagram) (qx : (CV.carrierDiagram hn hG' hSm' q').Γ.Crossing) (i j : Fin D₀.Γ.c) (ℓ : ℤ),
      gsc_fulltwist_triple (CV.carrierDiagram hn hG hSm qAB) (CV.carrierDiagram hn hG' hSm' q') D₀ qx ∧
      gsc_smoothing_split D₀ i j (CV.groupedPoly hn hG hSxw qA) (CV.groupedPoly hn hG hSxw qB) ℓ ∧
      CV.groupedWrithe hG qAB = CV.groupedWrithe hG qA + CV.groupedWrithe hG qB + 2 * ℓ - 1 := by
  obtain ⟨i, j, ℓ, hs, hw⟩ := r174s_smoothing_split_of_arc hn hG hG' hSxw hSm' q' hx' qA qB hsplit
  exact ⟨_, _, i, j, ℓ, r174s_fulltwist_of_hrec hn hG hG' D hsgn hSm hSm' qAB q' hx' hw' hrec, hs,
    by omega⟩

end R174SConsumer

/-! ## E. The arc record from visit-level transport data (the `GT_homfly_wall_gen` shape)

The black box `r174s_arc_rec_prop` asks for record isomorphisms; here it is reduced to a VISIT-level
datum: a bijection `ψ` from the retained visits of a carrier `q` (on `P`) onto the retained visits of a
carrier `q'` (on `P'`) lying strictly inside an open arc `(u₀, twin u₀)` of the traversal order of `P'`
together with their twins, compatible with twins, with the cyclic key order and with the divide signs —
exactly the shape of the hypotheses of `GT_homfly_wall_gen` (`GT_owner_transport` output).  Then the
arc-internal crossing record of the lift of `q'` is the record of the lift of `q`
(`r174s_recordIso_of_arcVisitData`): occurrences by `liftVisitEquiv` on both sides, twins by
`liftVisit_twin`, bits by `overBit_eq_true_iff_parent`, signs `+1` on both positive lifts, and the
first-return successor by the uniqueness of the cyclic successor (`cycNext_unique`): no retained
occurrence lies strictly inside a gap (`not_arcBetween_firstReturn`, read through `arcBetween_iff_key`
and `ψ`), and no occurrence lies strictly between a visit and its successor on the lift of `q`
(`record_succ_no_between`, `visitBetween_iff_key`). -/

section R174SArcData

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n}

/-- `v` lies strictly inside the open arc from `u₀` to `twin u₀` in the traversal-key order of `P'`. -/
def r174s_InArc (hP' : CrossingGeometry P') (u₀ v : Visit P') : Prop :=
  cycBetween (geometricVisitKey hP' u₀) (geometricVisitKey hP' v)
    (geometricVisitKey hP' (visitTwin u₀))

variable (hn : 3 ≤ n) (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')}
  (hT : GeoIndependent hG.cg T) (hT' : GeoIndependent hG'.cg T')
  (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')

/-- **The visit-level transport datum of an arc record.**  `ψ` maps the retained visits of `q` onto the
retained visits of `q'` that lie, with their twins, strictly inside the arc `(u₀, twin u₀)`; it is
compatible with twins, with the cyclic key order and with the divide signs. -/
structure r174s_ArcVisitData (u₀ : Visit P') where
  ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q} ≃
    {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg u₀ v ∧ r174s_InArc hG'.cg u₀ (visitTwin v))}
  twin : ∀ (v : Visit P) (hv : v.1 ∈ geoCarrierCrossings hG.cg T q),
    (ψ ⟨visitTwin v, by rw [visitTwin_crossing]; exact hv⟩).1 = visitTwin (ψ ⟨v, hv⟩).1
  cyc : ∀ a b c : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
    cycBetween (geometricVisitKey hG.cg a.1) (geometricVisitKey hG.cg b.1)
      (geometricVisitKey hG.cg c.1) →
    cycBetween (geometricVisitKey hG'.cg (ψ a).1) (geometricVisitKey hG'.cg (ψ b).1)
      (geometricVisitKey hG'.cg (ψ c).1)
  det : ∀ v : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.cg T q},
    (0 < det (edge P v.1.2.val) (edge P (visitTwin v.1).2.val) ↔
      0 < det (edge P' (ψ v).1.2.val) (edge P' (visitTwin (ψ v).1).2.val))

/-- **The arc-internal crossing record of the lift of `q'` is the record of the lift of `q`**, from the
visit-level datum at `u₀ = liftVisit u`. -/
theorem r174s_recordIso_of_arcVisitData (u : (geoPositiveLift hn hG' hT' q').Γ.Visit)
    (A : r174s_ArcVisitData hG hG' q q' (CV.liftVisit hn hG' hT' q' u)) :
    Nonempty (RecordIso ((geoPositiveLift hn hG' hT' q').record.restrictCrossings
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u))
      (geoPositiveLift hn hG hT q).record) := by
  have h1 : (geoPositiveLift hn hG' hT' q').record.componentCount = 1 := by
    rw [Diagram.record_componentCount]; exact geoPositiveLift_componentCount hn hG' hT' q'
  have hK1 : (geoPositiveLift hn hG hT q).record.componentCount = 1 := by
    rw [Diagram.record_componentCount]; exact geoPositiveLift_componentCount hn hG hT q
  have hsub : ∀ a b : Fin (geoPositiveLift hn hG hT q).Γ.c, a = b := by
    intro a b
    have hc : (geoPositiveLift hn hG hT q).Γ.c = 1 := geoPositiveLift_componentCount hn hG hT q
    apply Fin.ext
    have := a.2
    have := b.2
    omega
  -- the arc condition, read on the parent visits
  have hkeep : ∀ vh : (geoPositiveLift hn hG' hT' q').Γ.Visit,
      (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) vh ↔
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (CV.liftVisit hn hG' hT' q' vh) ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u)
          (visitTwin (CV.liftVisit hn hG' hT' q' vh))) := by
    intro vh
    rw [Record.r174s_crossKeep_keepArc_iff, CV.arcBetween_iff_key, CV.arcBetween_iff_key,
      Diagram.record_pair_apply, Diagram.record_pair_apply, CV.liftVisit_twin, CV.liftVisit_twin]
    exact Iff.rfl
  -- the codomain of `ψ` is closed under twins
  have hcod : ∀ b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))},
      (visitTwin b.1).1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin b.1) ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin (visitTwin b.1))) := by
    intro b
    refine ⟨by rw [visitTwin_crossing]; exact b.2.1, b.2.2.2, ?_⟩
    rw [visitTwin_involutive]; exact b.2.2.1
  -- `ψ⁻¹` commutes with twins
  have hpsymm : ∀ b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q' ∧
      (r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))},
      (A.ψ.symm ⟨visitTwin b.1, hcod b⟩).1 = visitTwin (A.ψ.symm b).1 := by
    intro b
    have h := A.twin (A.ψ.symm b).1 (A.ψ.symm b).2
    rw [Equiv.apply_symm_apply] at h
    have h' : A.ψ ⟨visitTwin (A.ψ.symm b).1, by rw [visitTwin_crossing]; exact (A.ψ.symm b).2⟩ =
        ⟨visitTwin b.1, hcod b⟩ := Subtype.ext h
    exact congrArg Subtype.val ((Equiv.symm_apply_eq A.ψ).mpr h'.symm)
  -- the occurrence bijection
  let e₁ : {vh : (geoPositiveLift hn hG' hT' q').Γ.Visit //
      (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) vh} ≃
      {b : {v : Visit P' // v.1 ∈ geoCarrierCrossings hG'.cg T' q'} //
        r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) b.1 ∧
          r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin b.1)} :=
    Equiv.subtypeEquiv (CV.liftVisitEquiv hn hG' hT' q') (fun vh => hkeep vh)
  let e₂ := Equiv.subtypeSubtypeEquivSubtypeInter
    (fun v : Visit P' => v.1 ∈ geoCarrierCrossings hG'.cg T' q')
    (fun v : Visit P' => r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) v ∧
      r174s_InArc hG'.cg (CV.liftVisit hn hG' hT' q' u) (visitTwin v))
  let Φ : ((geoPositiveLift hn hG' hT' q').record.restrictCrossings
      ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).M ≃
      (geoPositiveLift hn hG hT q).Γ.Visit :=
    e₁.trans (e₂.trans (A.ψ.symm.trans (CV.liftVisitEquiv hn hG hT q).symm))
  have hlv : ∀ vh, CV.liftVisit hn hG hT q (Φ vh) = (A.ψ.symm (e₂ (e₁ vh))).1 :=
    fun vh => CV.liftVisit_symm hn hG hT q _
  have hΦ : ∀ vh, (A.ψ (CV.liftVisitEquiv hn hG hT q (Φ vh))).1 = CV.liftVisit hn hG' hT' q' vh.1 := by
    intro vh
    show (A.ψ (CV.liftVisitEquiv hn hG hT q
      ((CV.liftVisitEquiv hn hG hT q).symm (A.ψ.symm (e₂ (e₁ vh)))))).1 = _
    rw [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
    rfl
  -- assembly
  refine ⟨RecordIso.ofOccOfCard Φ ?_ ?_ ?_ ?_ ?_⟩
  · -- successor: uniqueness of the cyclic successor on the lift of `q`
    intro vh
    have hk : Function.Injective
        (fun z : (geoPositiveLift hn hG hT q).Γ.Visit =>
          geometricVisitKey hG.cg (CV.liftVisit hn hG hT q z)) :=
      (geometricVisitKey_injective hG.cg).comp (CV.liftVisit_injective hn hG hT q)
    have hpk : (geoPositiveLift hn hG' hT' q').record.CrossKeep
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)
        ((geoPositiveLift hn hG' hT' q').record.pair vh.1) :=
      ((geoPositiveLift hn hG' hT' q').record.crossKeep_pair_iff _ _).mpr vh.2
    refine cycNext_unique hk (v := Φ vh) ?_ ?_ ?_ ?_
    · intro h
      have h' := congrArg Subtype.val (Φ.injective h)
      exact (geoPositiveLift hn hG' hT' q').record.firstReturn_val_ne _ h1 vh hpk
        ((geoPositiveLift hn hG' hT' q').record.pair_ne vh.1) h'
    · intro h
      have h' := ((geoPositiveLift hn hG hT q).record_succ_eq_self_iff (Φ vh)).mp h
        ((geoPositiveLift hn hG hT q).twin (Φ vh)) (hsub _ _)
      exact (geoPositiveLift hn hG hT q).twin_ne (Φ vh) h'
    · intro z hz
      have hc := A.cyc (CV.liftVisitEquiv hn hG hT q (Φ vh)) (CV.liftVisitEquiv hn hG hT q z)
        (CV.liftVisitEquiv hn hG hT q
          (Φ (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
            ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).succ vh))) hz
      rw [hΦ, hΦ] at hc
      set b := A.ψ (CV.liftVisitEquiv hn hG hT q z) with hb
      let zh : (geoPositiveLift hn hG' hT' q').Γ.Visit :=
        (CV.liftVisitEquiv hn hG' hT' q').symm ⟨b.1, b.2.1⟩
      have hzh : CV.liftVisit hn hG' hT' q' zh = b.1 := CV.liftVisit_symm hn hG' hT' q' _
      have hzk : (geoPositiveLift hn hG' hT' q').record.CrossKeep
          ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u) zh := by
        rw [hkeep, hzh]; exact b.2.2
      have harc : (geoPositiveLift hn hG' hT' q').record.ArcBetween vh.1 zh
          (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
            ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).succ vh).1 := by
        rw [CV.arcBetween_iff_key, hzh]; exact hc
      exact (geoPositiveLift hn hG' hT' q').record.not_arcBetween_firstReturn _ h1 vh hzk harc
    · intro z hz
      exact (geoPositiveLift hn hG hT q).record_succ_no_between (Φ vh) z (hsub _ _)
        ((CV.visitBetween_iff_key hn hG hT q _ _ _).mpr hz)
  · -- pairing
    intro vh
    apply CV.liftVisit_injective hn hG hT q
    rw [Diagram.record_pair_apply, CV.liftVisit_twin, hlv, hlv]
    have e : e₂ (e₁ (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
        ((geoPositiveLift hn hG' hT' q').record.r174s_KeepArc u)).pair vh)) =
        ⟨visitTwin (CV.liftVisit hn hG' hT' q' vh.1), hcod (e₂ (e₁ vh))⟩ :=
      Subtype.ext (CV.liftVisit_twin hn hG' hT' q' vh.1)
    rw [e]
    exact hpsymm (e₂ (e₁ vh))
  · -- bits
    intro vh
    show (geoPositiveLift hn hG hT q).overBit (Φ vh) = (geoPositiveLift hn hG' hT' q').overBit vh.1
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, hlv]
    have h := A.det (A.ψ.symm (e₂ (e₁ vh)))
    rw [Equiv.apply_symm_apply] at h
    exact h
  · -- signs: both lifts are positive
    intro vh
    show (geoPositiveLift hn hG hT q).sign (Φ vh).1 = (geoPositiveLift hn hG' hT' q').sign vh.1.1
    rw [geoPositiveLift_sign, geoPositiveLift_sign]
  · -- circles
    show ((geoPositiveLift hn hG' hT' q').record.restrictCrossings _).componentCount =
      (geoPositiveLift hn hG hT q).record.componentCount
    rw [Record.componentCount_restrictCrossings, h1, hK1]

end R174SArcData

section R174SArcInstance

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {Q : Finset (Crossing P)} {x w m : Crossing P}

/-- **The black box `r174s_arc_rec_prop` from visit-level transport data**: two data `A`, `B`
(`r174s_ArcVisitData`) for the arcs `(u, τ u)` and `(τ u, u)` of an occurrence `u` of `x'` on
`D_H = carrierDiagram q'` — `ψ_A` from the retained visits of the `P-ac` carrier `qA` onto the retained
visits of `AB'` inside the `A`-arc, `ψ_B` likewise for `qB` and the `B`-arc, both twin-, key-order- and
sign-compatible — give the two record isomorphisms.  What remains for the realiser of items 1–2 is exactly
these visit bijections (ownership transport, `GT_owner_transport`; A7 exactness for the key order,
`GT_Endpoint.sign_eq` for the signs). -/
theorem r174s_arc_rec_of_visitData (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})))
    (hx' : crossingTransport hs x ∈
      geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q')
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (u : (CV.carrierDiagram hn hG' hSm' q').Γ.Visit) (hu : u.1 = r174s_qx hn hG' hSm' q' hx')
    (A : r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') qA q'
      (CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q' u))
    (B : r174s_ArcVisitData (s174_cg hn hG) (s174_cg hn hG') qB q'
      (CV.liftVisit hn (s174_cg hn hG') (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') q'
        ((CV.carrierDiagram hn hG' hSm' q').record.pair u))) :
    r174s_arc_rec_prop hn hG hG' hSxw hSm' q' hx' qA qB :=
  ⟨u, hu,
    r174s_recordIso_of_arcVisitData hn (s174_cg hn hG) (s174_cg hn hG')
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSxw)
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') qA q' u A,
    r174s_recordIso_of_arcVisitData hn (s174_cg hn hG) (s174_cg hn hG')
      (CV.geoIndependent_of_mem_Ind hG.crossingGeometry hSxw)
      (CV.geoIndependent_of_mem_Ind hG'.crossingGeometry hSm') qB q' _ B⟩

end R174SArcInstance

end

end SM.Link
