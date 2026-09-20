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


/-! ## R174 WALL (unit WALL of row 174, Wave 2): `gsc_Ledger` items 2–3

Prover of unit WALL, 2026-09-15.  Everything below is NEW (nothing above changed); names carry the prefix
`r174w_`.  Contents (see `R174_WALL_REPORT.md`):
* **Part A — item 2 (the wall)**: the retained-crossing correspondence of the centre row `Q ∪ {m}` across the
  RIII wall (`r174w_retained_eq_of_ne`, `r174w_retained_qAB`: every carrier keeps its retained crossings
  transported, `AB` gains exactly `x', w'`), hence `writhe_wall` (`r174w_writhe_wall_ledger`) and `omega_wall`
  (`r174w_omega_wall_ledger`, through `EXT_homfly_wall`).  `qAB` is the carrier of the `ℓ₂`-visit `x₂`.
* **Part B — the corner-mark reformulation** of the selector `wt` and of `2π·rot` of a carrier (sums and
  quantifiers over the set of corner marks, with the intrinsic turn sign `r174w_tau` and principal turn
  `r174w_theta` of a mark), the angle identity of a triangle of directions (`r174w_angle_add_of_pos/neg`), the
  selector algebra on split corner sets (`r174w_F_split`, `r174w_F_two`) and the rotation sums
  (`r174w_rot_add`, `r174w_rot_eq_two`, `r174w_carrierR_add_of`).
* **Part C — the carrier structure of the two rows on the two-edge side** (`Q ∪ {m}` and `Q ∪ {x, w}`) from the
  geo layer's insertion data (`geoSmoothingSuccessor_insert_child_data`, `geoOwner_insert_iff_of_unaffected`),
  in both traversal orientations (`r174w_split_caseB` = the printed word `a b A a c B b c C`, `r174w_split_caseA`
  = the reversed traversal): the distribution of the six local visits over `A, B, C'` and `AB, C`, and the
  three regular containments (`r174w_Split`).
* **Part D — item 3**: `weight_AB` (`r174w_weight_AB`), `weight_C` (`r174w_weight_C`), `carrierR_add`
  (`r174w_carrierR_add`), `hσ` (`r174w_hsigma`) with the canonical sign `r174w_sigma` (which is
  `crossingSign ℓ₁ ℓ₂` in the printed orientation and its NEGATIVE in the reversed one — the ledger's `σ` is a
  free field, so this is not a defect of the ledger, but the realiser must choose `σ` this way), and the bonus
  `omega_C` (`r174w_omega_C`: `C` and `C'` retain the same crossings, `r174w_retained_C`). -/

namespace SM.Link

open SM SM.GeoCarrier SM.Carrier RProof

noncomputable section

section R174W_Wall

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)
  (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
  (hSm' : transportSupport hs (Q ∪ {m}) ∈ CV.Ind hG'.crossingGeometry)

omit [NeZero n] in
theorem r174w_mem_Sm_iff (y : Crossing P) : y ∈ Q ∪ {m} ↔ y ∈ Q ∨ y = m := by
  simp only [Finset.mem_union, Finset.mem_singleton]

include D in
theorem r174w_x_not_mem_Sm : x ∉ Q ∪ {m} := by
  rw [r174w_mem_Sm_iff]
  rintro (h | h)
  · exact D.Q_out x h D.xT
  · exact D.xm h

include D in
theorem r174w_w_not_mem_Sm : w ∉ Q ∪ {m} := by
  rw [r174w_mem_Sm_iff]
  rintro (h | h)
  · exact D.Q_out w h D.wT
  · exact D.wm h

omit [NeZero n] in
theorem r174w_m_mem_Sm : m ∈ Q ∪ {m} := (r174w_mem_Sm_iff m).mpr (Or.inr rfl)

include D in
/-- `x` is a neighbour of the selected centre `m`: not in `U(Q ∪ {m})`. -/
theorem r174w_x_not_mem_U : x ∉ CV.U hG.crossingGeometry (Q ∪ {m}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h m r174w_m_mem_Sm D.hxm

include D in
theorem r174w_w_not_mem_U : w ∉ CV.U hG.crossingGeometry (Q ∪ {m}) := by
  rw [CV.mem_U_iff]
  rintro ⟨-, h⟩
  exact h m r174w_m_mem_Sm D.hwm

include D in
/-- On the one-edge side `x'` no longer interlaces `m'`: `x' ∈ U(Q' ∪ {m'})`. -/
theorem r174w_x'_mem_U' :
    crossingTransport hs x ∈ CV.U hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => r174w_x_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ x).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases (r174w_mem_Sm_iff s).mp hs' with h | rfl
  · rw [D.toggle x s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h x D.xT (geometricInterlaces_symm _ h')
  · rw [D.compl x s D.xT D.mT D.xm]
    exact fun h' => h' D.hxm

include D in
theorem r174w_w'_mem_U' :
    crossingTransport hs w ∈ CV.U hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) := by
  rw [CV.mem_U_iff]
  refine ⟨fun h => r174w_w_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ w).mp h), fun s' hs' => ?_⟩
  obtain ⟨s, rfl⟩ := (crossingTransport hs).surjective s'
  rw [mem_transportSupport_iff] at hs'
  rcases (r174w_mem_Sm_iff s).mp hs' with h | rfl
  · rw [D.toggle w s (fun h' => D.Q_out s h h'.2)]
    exact fun h' => D.Q_avail s h w D.wT (geometricInterlaces_symm _ h')
  · rw [D.compl w s D.wT D.mT D.wm]
    exact fun h' => h' D.hwm

include D in
/-- The `ℓ₂`-visits of `x` and `w` are adjacent unselected visits of the centre row: one carrier (`AB`). -/
theorem r174w_owner_x₂_eq_w₂ :
    geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) =
      geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hG.crossingGeometry _ D.adj2 rfl (r174w_x_not_mem_Sm hG hG' D) (r174w_w_not_mem_Sm hG hG' D)

include D in
/-- `x₂` is a good mark of the centre row: its only reversed partner is `w₂`, and `w` is not selected. -/
theorem r174w_good_x₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.x₂) := by
  intro v hv u hrev hu
  obtain rfl := Sum.inr.inj hv
  have huS : u.1 ∈ Q ∪ {m} := hu
  have huT : u.1.val ∈ triangleSupports e f g := (F1.mem_triangleCrossings e f g u.1).mp hrev.2.1
  have hum : u.1 = m := by
    rcases (r174w_mem_Sm_iff u.1).mp huS with h | h
    · exact absurd huT (D.Q_out u.1 h)
    · exact h
  apply D.l2_not_mem_m
  have h2 : u.2.val = ℓ₂ := hrev.2.2.2.symm
  rw [← h2, ← hum]
  exact u.2.property

include D in
theorem r174w_good_w₂ : GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr D.w₂) := by
  intro v hv u hrev hu
  obtain rfl := Sum.inr.inj hv
  have huS : u.1 ∈ Q ∪ {m} := hu
  have huT : u.1.val ∈ triangleSupports e f g := (F1.mem_triangleCrossings e f g u.1).mp hrev.2.1
  have hum : u.1 = m := by
    rcases (r174w_mem_Sm_iff u.1).mp huS with h | h
    · exact absurd huT (D.Q_out u.1 h)
    · exact h
  apply D.l2_not_mem_m
  have h2 : u.2.val = ℓ₂ := hrev.2.2.2.symm
  rw [← h2, ← hum]
  exact u.2.property

/-- The carrier `AB` of the centre row: the owner of the `ℓ₂`-visits of `x, w` (item 1's `qAB`). -/
abbrev r174w_qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}) :=
  geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂)

/-- The wall of the centre row (the ledger's `W`). -/
abbrev r174w_W : GT_Wall hG.crossingGeometry hG'.crossingGeometry hs (triangleCrossings P e f g) (Q ∪ {m}) :=
  gsc_wall_of_endpoint hG hG' D hSm hSm'

/-- The carrier bijection `τ` of the ledger. -/
abbrev r174w_τ : GeoComponent hG.crossingGeometry (Q ∪ {m}) ≃
    GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) :=
  GT_carrierEquiv (r174w_W hG hG' D hSm hSm')

theorem r174w_τ_eq : (gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ = r174w_τ hG hG' D hSm hSm' := rfl

/-- **The `ℓ₂`-visit of `x'` lies on the copy of `AB`** (ownership transport of the good mark `x₂`). -/
theorem r174w_owner'_x₂' :
    geoOwner hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (Sum.inr (visitTransport hs D.x₂)) =
      r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D) := by
  rw [← markTransport_visit]
  exact GT_owner_transport (r174w_W hG hG' D hSm hSm') (r174w_good_x₂ hG hG' D)

theorem r174w_owner'_w₂' :
    geoOwner hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (Sum.inr (visitTransport hs D.w₂)) =
      r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D) := by
  rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (r174w_good_w₂ hG hG' D)]
  unfold r174w_qAB
  rw [r174w_owner_x₂_eq_w₂ hG hG' D]

/-- **`x'` is a retained crossing of `AB'`** (the ledger's residual crossing `a` of `D_H`). -/
theorem r174w_x'_mem_retained :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
      (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨fun h => r174w_x_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ x).mp h), fun v hv => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174w_x'_mem_U' hG hG' D) v (visitTransport hs D.x₂) hv rfl]
  exact r174w_owner'_x₂' hG hG' D hSm hSm'

theorem r174w_w'_mem_retained :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
      (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) := by
  rw [mem_geoCarrierCrossings]
  refine ⟨fun h => r174w_w_not_mem_Sm hG hG' D ((mem_transportSupport_iff hs _ w).mp h), fun v hv => ?_⟩
  rw [CV.owner_eq_of_mem_U hG'.crossingGeometry hSm' (r174w_w'_mem_U' hG hG' D) v (visitTransport hs D.w₂) hv rfl]
  exact r174w_owner'_w₂' hG hG' D hSm hSm'

include D hSm in
theorem r174w_x_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    x ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q :=
  GT_retained_of_not_mem_U (CV.geoIndependent_of_mem_Ind _ hSm) (r174w_x_not_mem_U hG hG' D) q

include D hSm in
theorem r174w_w_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    w ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q :=
  GT_retained_of_not_mem_U (CV.geoIndependent_of_mem_Ind _ hSm) (r174w_w_not_mem_U hG hG' D) q

theorem r174w_m_not_retained (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    m ∉ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q := fun h =>
  ((mem_geoCarrierCrossings _ _ q m).mp h).1 r174w_m_mem_Sm

theorem r174w_m'_not_retained (q' : GeoComponent hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))) :
    crossingTransport hs m ∉ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) q' :=
  fun h => ((mem_geoCarrierCrossings _ _ q' _).mp h).1
    ((mem_transportSupport_iff hs _ m).mpr r174w_m_mem_Sm)

include D hSm in
/-- A retained crossing of a carrier of the centre row is an outside crossing. -/
theorem r174w_outside_of_retained {q : GeoComponent hG.crossingGeometry (Q ∪ {m})} {y : Crossing P}
    (hy : y ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q) :
    y.val ∉ triangleSupports e f g :=
  D.outside_of_ne (fun h => r174w_x_not_retained hG hG' D hSm q (h ▸ hy))
    (fun h => r174w_w_not_retained hG hG' D hSm q (h ▸ hy)) (fun h => r174w_m_not_retained hG q (h ▸ hy))

/-- Retained outside crossings are carried (their visits are good marks). -/
theorem r174w_retained_iff_of_outside (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) {y : Crossing P}
    (hy : y.val ∉ triangleSupports e f g) :
    crossingTransport hs y ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔
      y ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q := by
  have hgood : ∀ v : Visit P, v.1 = y → GT_Good (triangleCrossings P e f g) (Q ∪ {m}) (Sum.inr v) :=
    fun v hv => GT_good_of_not_mem _ _ (fun h => hy ((F1.mem_triangleCrossings e f g v.1).mp (hv ▸ h) |>
      fun h' => by rw [hv] at h'; exact h'))
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings, mem_transportSupport_iff]
  apply and_congr Iff.rfl
  constructor
  · intro hall v hv
    have := hall (visitTransport hs v) (by rw [visitTransport_crossing, hv])
    rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (hgood v hv)] at this
    exact (GT_carrierEquiv _).injective this
  · intro hall v' hv'
    obtain ⟨v, rfl⟩ := (visitTransport hs).surjective v'
    rw [visitTransport_crossing] at hv'
    have hv : v.1 = y := (crossingTransport hs).injective hv'
    rw [← markTransport_visit, GT_owner_transport (r174w_W hG hG' D hSm hSm') (hgood v hv), hall v hv]

/-- `x'` is retained exactly by the copy of `AB`. -/
theorem r174w_x'_retained_iff (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    crossingTransport hs x ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔ q = r174w_qAB hG hG' D := by
  constructor
  · intro h
    have h1 := ((mem_geoCarrierCrossings _ _ _ _).mp h).2 (visitTransport hs D.x₂) rfl
    have h2 := ((mem_geoCarrierCrossings _ _ _ _).mp
      (r174w_x'_mem_retained hG hG' D hSm hSm')).2 (visitTransport hs D.x₂) rfl
    exact (GT_carrierEquiv _).injective (h1.symm.trans h2)
  · rintro rfl
    exact r174w_x'_mem_retained hG hG' D hSm hSm'

theorem r174w_w'_retained_iff (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) :
    crossingTransport hs w ∈ geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' q) ↔ q = r174w_qAB hG hG' D := by
  constructor
  · intro h
    have h1 := ((mem_geoCarrierCrossings _ _ _ _).mp h).2 (visitTransport hs D.w₂) rfl
    have h2 := ((mem_geoCarrierCrossings _ _ _ _).mp
      (r174w_w'_mem_retained hG hG' D hSm hSm')).2 (visitTransport hs D.w₂) rfl
    exact (GT_carrierEquiv _).injective (h1.symm.trans h2)
  · rintro rfl
    exact r174w_w'_mem_retained hG hG' D hSm hSm'

/-- **Retained crossings of a spectator (or of `C`) are carried across the wall.** -/
theorem r174w_retained_eq_of_ne (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m})) (r174w_τ hG hG' D hSm hSm' q) =
      (geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) q).map (crossingTransport hs).toEmbedding := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyx : y = x
  · subst hyx
    exact iff_of_false (fun h => hq ((r174w_x'_retained_iff hG hG' D hSm hSm' q).mp h))
      (r174w_x_not_retained hG hG' D hSm q)
  by_cases hyw : y = w
  · subst hyw
    exact iff_of_false (fun h => hq ((r174w_w'_retained_iff hG hG' D hSm hSm' q).mp h))
      (r174w_w_not_retained hG hG' D hSm q)
  by_cases hym : y = m
  · subst hym
    exact iff_of_false (r174w_m'_not_retained hG' _) (r174w_m_not_retained hG q)
  exact r174w_retained_iff_of_outside hG hG' D hSm hSm' q (D.outside_of_ne hyx hyw hym)

/-- **Retained crossings of `AB'`: those of `AB`, transported, plus `x'` and `w'`.** -/
theorem r174w_retained_qAB :
    geoCarrierCrossings hG'.crossingGeometry (transportSupport hs (Q ∪ {m}))
        (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) =
      insert (crossingTransport hs x) (insert (crossingTransport hs w)
        ((geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
          (crossingTransport hs).toEmbedding)) := by
  classical
  ext y'
  obtain ⟨y, rfl⟩ := (crossingTransport hs).surjective y'
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_map_equiv, Equiv.symm_apply_apply]
  by_cases hyx : y = x
  · subst hyx
    exact iff_of_true (r174w_x'_mem_retained hG hG' D hSm hSm') (Or.inl rfl)
  by_cases hyw : y = w
  · subst hyw
    exact iff_of_true (r174w_w'_mem_retained hG hG' D hSm hSm') (Or.inr (Or.inl rfl))
  have hne1 : crossingTransport hs y ≠ crossingTransport hs x := (crossingTransport hs).injective.ne hyx
  have hne2 : crossingTransport hs y ≠ crossingTransport hs w := (crossingTransport hs).injective.ne hyw
  simp only [hne1, hne2, false_or]
  by_cases hym : y = m
  · subst hym
    exact iff_of_false (r174w_m'_not_retained hG' _) (r174w_m_not_retained hG _)
  exact r174w_retained_iff_of_outside hG hG' D hSm hSm' _ (D.outside_of_ne hyx hyw hym)

/-- **`writhe_wall` (GSC (9)): `w_H = w_L + 2`.** -/
theorem r174w_writhe_wall :
    CV.groupedWrithe hG' (r174w_τ hG hG' D hSm hSm' (r174w_qAB hG hG' D)) =
      CV.groupedWrithe hG (r174w_qAB hG hG' D) + 2 := by
  classical
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hSm',
    CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm, r174w_retained_qAB hG hG' D hSm hSm']
  have hwm : crossingTransport hs w ∉ (geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
      (crossingTransport hs).toEmbedding := by
    rw [Finset.mem_map_equiv, Equiv.symm_apply_apply]
    exact r174w_w_not_retained hG hG' D hSm _
  have hxm : crossingTransport hs x ∉ insert (crossingTransport hs w)
      ((geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) (r174w_qAB hG hG' D)).map
        (crossingTransport hs).toEmbedding) := by
    rw [Finset.mem_insert, Finset.mem_map_equiv, Equiv.symm_apply_apply]
    rintro (h | h)
    · exact D.xw ((crossingTransport hs).injective h)
    · exact r174w_x_not_retained hG hG' D hSm _ h
  rw [Finset.card_insert_of_notMem hxm, Finset.card_insert_of_notMem hwm, Finset.card_map]
  push_cast
  ring

/-- **The grouped polynomial of every carrier but `AB` is carried across the wall** (record isomorphism
of the two positive lifts, `EXT_homfly_wall`: retained crossings correspond, key orders of their visits
are carried — no reversed pair among outside crossings — and the divide signs agree). -/
theorem r174w_groupedPoly_wall (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    CV.groupedPoly hn hG' hSm' (r174w_τ hG hG' D hSm hSm' q) = CV.groupedPoly hn hG hSm q := by
  have hX := r174w_retained_eq_of_ne hG hG' D hSm hSm' q hq
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine EXT_homfly_wall hn _ _ hs _ _ q _ hX ?_ ?_
  · intro v u hv hu
    have hvT : v.1.val ∉ triangleSupports e f g := r174w_outside_of_retained hG hG' D hSm hv
    exact (r174w_W hG hG' D hSm hSm').key_lt v u (GT_not_rev_of_not_mem_left
      (fun h => hvT ((F1.mem_triangleCrossings e f g v.1).mp h)))
  · intro v _
    exact GT_det_pos_iff_of_sign (D.sign_eq _ _ (by rw [← visit_crossing_val_eq_pair v]; exact v.1.property))

/-- **`omega_wall`: every carrier but `AB` keeps its read `Ω₁` across the wall.** -/
theorem r174w_omega_wall (q : GeoComponent hG.crossingGeometry (Q ∪ {m})) (hq : q ≠ r174w_qAB hG hG' D) :
    CV.Omega1 hn hG' hSm' (r174w_τ hG hG' D hSm hSm' q) = CV.Omega1 hn hG hSm q := by
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG' hSm', CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm,
    r174w_retained_eq_of_ne hG hG' D hSm hSm' q hq, Finset.card_map,
    GT_carrierR_eq hn hG hG' (r174w_W hG hG' D hSm hSm') hSm hSm' q, r174w_groupedPoly_wall hn hG hG' D hSm hSm' q hq]

/-- The carrier `AB` also keeps its grouped writhe transported set-wise: `w_{AB'} = w_{AB} + 2`, in the
ledger's own `W.τ` form. -/
theorem r174w_writhe_wall_ledger (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    CV.groupedWrithe hG' ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ qAB) =
      CV.groupedWrithe hG qAB + 2 := by
  subst hqAB
  exact r174w_writhe_wall hG hG' D hSm hSm'

/-- `omega_wall` in the ledger's own `W.τ` form. -/
theorem r174w_omega_wall_ledger (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) = qAB) :
    ∀ q, q ≠ qAB → CV.Omega1 hn hG' hSm' ((gsc_wallData_of_endpoint hn hG hG' D hSm hSm').τ q) =
      CV.Omega1 hn hG hSm q := by
  subst hqAB
  intro q hq
  exact r174w_omega_wall hn hG hG' D hSm hSm' q hq

end R174W_Wall


/-- Classical equality on crossings, aligned with the geo layer's `insert` (`SM/GeoCarrierCount.lean` reads
`insert v.1 S` with `Classical.propDecidable`); activated locally where `insert`/`Finset (Mark P)` appear. -/
@[instance_reducible] def r174w_decEqCrossing {n : ℕ} {P : LabelledTuple n} : DecidableEq (Crossing P) :=
  fun a b => Classical.propDecidable (a = b)

/-! ### B2. The angle identity at a triangle of directions -/

section R174W_Angle

/-- For three directions with `det(u₁,u₂), det(u₁,u₃), det(u₂,u₃) > 0` the principal angles add:
`∠(u₁,u₂) + ∠(u₂,u₃) = ∠(u₁,u₃)` (all three lie in `(0, π)`; the identity holds mod `2π` by
`arg (zw) = arg z + arg w`, and the bounds pin the integer). -/
theorem r174w_angle_add_of_pos {u₁ u₂ u₃ : Plane} (h12 : 0 < det u₁ u₂) (h13 : 0 < det u₁ u₃)
    (h23 : 0 < det u₂ u₃) :
    principalAngle u₁ u₂ + principalAngle u₂ u₃ = principalAngle u₁ u₃ := by
  have hp12 := CV.regularPair_of_det_ne_zero h12.ne'
  have hp13 := CV.regularPair_of_det_ne_zero h13.ne'
  have hp23 := CV.regularPair_of_det_ne_zero h23.ne'
  have hu1 : u₁ ≠ 0 := hp12.1
  have hu2 : u₂ ≠ 0 := hp12.2.1
  have hu3 : u₃ ≠ 0 := hp13.2.1
  have a12 := (CV.principalAngle_pos_iff hp12).mpr h12
  have a13 := (CV.principalAngle_pos_iff hp13).mpr h13
  have a23 := (CV.principalAngle_pos_iff hp23).mpr h23
  have b12 := (principalAngle_bounds hp12).2
  have b13 := (principalAngle_bounds hp13).2
  have b23 := (principalAngle_bounds hp23).2
  have hprod : cornerRotor u₁ u₂ * cornerRotor u₂ u₃ =
      ((Complex.normSq (planeComplex u₂) : ℝ) : ℂ) * cornerRotor u₁ u₃ := by
    apply Complex.ext
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
  have key : ((principalAngle u₁ u₂ + principalAngle u₂ u₃ : ℝ) : Real.Angle) =
      (principalAngle u₁ u₃ : Real.Angle) := by
    unfold principalAngle
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (cornerRotor_ne_zero hu1 hu2)
      (cornerRotor_ne_zero hu2 hu3), hprod,
      Complex.arg_real_mul _ (Complex.normSq_pos.mpr (planeComplex_ne_zero hu2))]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at key
  obtain ⟨k, hk⟩ := key
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

/-- The same with all three determinants negative (angles in `(−π, 0)`). -/
theorem r174w_angle_add_of_neg {u₁ u₂ u₃ : Plane} (h12 : det u₁ u₂ < 0) (h13 : det u₁ u₃ < 0)
    (h23 : det u₂ u₃ < 0) :
    principalAngle u₁ u₂ + principalAngle u₂ u₃ = principalAngle u₁ u₃ := by
  have hp12 := CV.regularPair_of_det_ne_zero h12.ne
  have hp13 := CV.regularPair_of_det_ne_zero h13.ne
  have hp23 := CV.regularPair_of_det_ne_zero h23.ne
  have hu1 : u₁ ≠ 0 := hp12.1
  have hu2 : u₂ ≠ 0 := hp12.2.1
  have hu3 : u₃ ≠ 0 := hp13.2.1
  have a12 := (principalAngle_neg_iff u₁ u₂).mpr h12
  have a13 := (principalAngle_neg_iff u₁ u₃).mpr h13
  have a23 := (principalAngle_neg_iff u₂ u₃).mpr h23
  have b12 := (principalAngle_bounds hp12).1
  have b13 := (principalAngle_bounds hp13).1
  have b23 := (principalAngle_bounds hp23).1
  have hprod : cornerRotor u₁ u₂ * cornerRotor u₂ u₃ =
      ((Complex.normSq (planeComplex u₂) : ℝ) : ℂ) * cornerRotor u₁ u₃ := by
    apply Complex.ext
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
    · simp only [cornerRotor, planeComplex, Complex.mul_re, Complex.mul_im, Complex.star_def,
        Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im, Complex.normSq_apply]
      ring
  have key : ((principalAngle u₁ u₂ + principalAngle u₂ u₃ : ℝ) : Real.Angle) =
      (principalAngle u₁ u₃ : Real.Angle) := by
    unfold principalAngle
    rw [Real.Angle.coe_add, ← Complex.arg_mul_coe_angle (cornerRotor_ne_zero hu1 hu2)
      (cornerRotor_ne_zero hu2 hu3), hprod,
      Complex.arg_real_mul _ (Complex.normSq_pos.mpr (planeComplex_ne_zero hu2))]
  rw [Real.Angle.angle_eq_iff_two_pi_dvd_sub] at key
  obtain ⟨k, hk⟩ := key
  have hpi := Real.pi_pos
  have hk1 : (k : ℝ) < 1 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk2 : (-1 : ℝ) < k := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have hk1' : k < 1 := by exact_mod_cast hk1
  have hk2' : -1 < k := by exact_mod_cast hk2
  have hk0 : k = 0 := by omega
  subst hk0
  simp only [Int.cast_zero, mul_zero] at hk
  linarith

end R174W_Angle

/-! ### B1. The weight and the rotation of a carrier through its corner marks -/

section R174W_Corners

attribute [local instance] Classical.propDecidable
attribute [local instance high] r174w_decEqCrossing

variable {n : ℕ} [NeZero n] {P : LabelledTuple n}

/-- The intrinsic turn sign of a corner mark: `turn P i` at a vertex, the crossing sign
`sgn det(edge of v, edge of twin v)` at a (selected) visit. -/
def r174w_tau (P : LabelledTuple n) : Mark P → SignType
  | Sum.inl i => turn P i
  | Sum.inr v => crossingSign P v.2.val (visitTwin v).2.val

/-- The intrinsic principal turn of a corner mark. -/
noncomputable def r174w_theta (P : LabelledTuple n) : Mark P → ℝ
  | Sum.inl i => principalAngle (edge P (i - 1)) (edge P i)
  | Sum.inr v => principalAngle (edge P v.2.val) (edge P (visitTwin v).2.val)

omit [NeZero n] in
theorem r174w_tau_vertex (i : ZMod n) : r174w_tau P (Sum.inl i) = turn P i := rfl
omit [NeZero n] in
theorem r174w_tau_visit (v : Visit P) :
    r174w_tau P (Sum.inr v) = crossingSign P v.2.val (visitTwin v).2.val := rfl
omit [NeZero n] in
theorem r174w_theta_vertex (i : ZMod n) :
    r174w_theta P (Sum.inl i) = principalAngle (edge P (i - 1)) (edge P i) := rfl
omit [NeZero n] in
theorem r174w_theta_visit (v : Visit P) :
    r174w_theta P (Sum.inr v) = principalAngle (edge P v.2.val) (edge P (visitTwin v).2.val) := rfl

omit [NeZero n] in
/-- The sign of the principal turn is the turn sign (when nonzero). -/
theorem r174w_sign_theta (a : Mark P) (h : r174w_tau P a ≠ 0) :
    SignType.sign (r174w_theta P a) = r174w_tau P a := by
  cases a with
  | inl i =>
    rw [r174w_tau_vertex, turn_det] at h ⊢
    exact principalAngle_sign (CV.regularPair_of_det_ne_zero (sign_ne_zero.mp h))
  | inr v =>
    rw [r174w_tau_visit] at h ⊢
    unfold crossingSign at h ⊢
    exact principalAngle_sign (CV.regularPair_of_det_ne_zero (sign_ne_zero.mp h))

/-- The corner marks of a carrier `q` of `S`: the owned original vertices and selected visits. -/
noncomputable def r174w_corners (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter (fun a => geoOwner hP S a = q ∧ IsTrueCorner S a)

theorem r174w_mem_corners (hP : CrossingGeometry P) (S : Finset (Crossing P)) (q : GeoComponent hP S)
    (a : Mark P) : a ∈ r174w_corners hP S q ↔ geoOwner hP S a = q ∧ IsTrueCorner S a := by
  unfold r174w_corners
  rw [Finset.mem_filter]
  exact ⟨fun h => h.2, fun h => ⟨Finset.mem_univ _, h⟩⟩

theorem r174w_corners_eq_image (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) :
    r174w_corners hP S q = Finset.univ.image (geoCornerMark hP S q) := by
  classical
  ext a
  rw [r174w_mem_corners, Finset.mem_image]
  constructor
  · rintro ⟨hq, hc⟩
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S q a hq hc
    exact ⟨k, Finset.mem_univ _, hk⟩
  · rintro ⟨k, -, rfl⟩
    exact geoCornerMark_mem hP S q k

theorem r174w_card_corners (hP : CrossingGeometry P) (S : Finset (Crossing P))
    (q : GeoComponent hP S) : (r174w_corners hP S q).card = geoCornerCount hP S q := by
  classical
  rw [r174w_corners_eq_image, Finset.card_image_of_injective _ (geoCornerMark_injective hP S q),
    Finset.card_univ, ZMod.card]

/-- The turn of the corner polygon at `c_k` is the intrinsic turn sign of the corner mark `c_k`. -/
theorem r174w_turn_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    turn (geoCornerPolygon hP S q) k = r174w_tau P (geoCornerMark hP S q k) := by
  have hc := isTrueCorner_geoCornerMark hP S q k
  cases hm : geoCornerMark hP S q k with
  | inl i =>
    rw [geoCornerPolygon_turn_vertex hn hP hS q k i hm]
    rfl
  | inr v =>
    rw [hm] at hc
    exact geoCornerPolygon_turn_visit hn hP hS q k v hc hm

/-- The principal turn of the corner polygon at `c_k` is the intrinsic principal turn of `c_k`
(the two incident edges are positive multiples of the original in/out edges). -/
theorem r174w_principalTurn_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (k : ZMod (geoCornerCount hP S q)) :
    CV.principalTurn (geoCornerPolygon hP S q) k = r174w_theta P (geoCornerMark hP S q k) := by
  obtain ⟨c, hc, he⟩ := geoCornerPolygon_edge_pred_smul hn hP hS q k
  obtain ⟨c', hc', he'⟩ := geoCornerPolygon_edge_smul hn hP hS q k
  unfold CV.principalTurn
  rw [he, he', principalAngle_smul hc hc']
  have hcorner := isTrueCorner_geoCornerMark hP S q k
  cases hm : geoCornerMark hP S q k with
  | inl i =>
    rw [geoInEdge_vertex hn hP i, geoOutSlot_vertex]
    rfl
  | inr v =>
    rw [hm] at hcorner
    rw [geoInEdge_visit hn hP v, geoOutSlot_selected hP S v hcorner]
    rfl

open Classical in
/-- The selector read on a set of corner marks: `1` if all right turns, `(−1)^|C|` if all left, else `0`. -/
noncomputable def r174w_F (P : LabelledTuple n) (C : Finset (Mark P)) : ℤ :=
  if (∀ a ∈ C, r174w_tau P a = -1) then 1
  else if (∀ a ∈ C, r174w_tau P a = 1) then (-1) ^ C.card else 0

/-- `wt(q)` is `F` of the corner-mark set. -/
theorem r174w_weight_eq (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) :
    CV.weight hP S q = r174w_F P (r174w_corners hP S q) := by
  classical
  have h1 : (∀ i, turn (geoCornerPolygon hP S q) i = -1) ↔
      (∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1) := by
    rw [r174w_corners_eq_image]
    constructor
    · intro h a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      rw [← r174w_turn_eq hn hP hS q k]
      exact h k
    · intro h k
      rw [r174w_turn_eq hn hP hS q k]
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  have h2 : (∀ i, turn (geoCornerPolygon hP S q) i = 1) ↔
      (∀ a ∈ r174w_corners hP S q, r174w_tau P a = 1) := by
    rw [r174w_corners_eq_image]
    constructor
    · intro h a ha
      obtain ⟨k, -, rfl⟩ := Finset.mem_image.mp ha
      rw [← r174w_turn_eq hn hP hS q k]
      exact h k
    · intro h k
      rw [r174w_turn_eq hn hP hS q k]
      exact h _ (Finset.mem_image_of_mem _ (Finset.mem_univ k))
  unfold CV.weight geoCarrierSelector cornerSelector r174w_F
  by_cases hA : ∀ i, turn (geoCornerPolygon hP S q) i = -1
  · rw [ite_eq_left hA, ite_eq_left (h1.mp hA)]
  · rw [ite_eq_right hA, ite_eq_right (fun h => hA (h1.mpr h))]
    by_cases hB : ∀ i, turn (geoCornerPolygon hP S q) i = 1
    · rw [ite_eq_left hB, ite_eq_left (h2.mp hB), r174w_card_corners]
    · rw [ite_eq_right hB, ite_eq_right (fun h => hB (h2.mpr h))]

/-- `2π · rot(q) = Σ_{corner marks a of q} θ(a)` (CV:lem:turnlift (ii) read on the corner marks). -/
theorem r174w_two_pi_rot (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    2 * Real.pi * (CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) : ℝ) =
      ∑ a ∈ r174w_corners hG.crossingGeometry S q, r174w_theta P a := by
  classical
  rw [CV.two_pi_mul_rot, r174w_corners_eq_image,
    Finset.sum_image (fun a _ b _ h => geoCornerMark_injective hG.crossingGeometry S q h)]
  exact Finset.sum_congr rfl fun k _ =>
    r174w_principalTurn_eq hn _ (CV.geoIndependent_of_mem_Ind _ hS) q k

/-- `R(q)` as an integer is `|rot|` of the corner polygon. -/
theorem r174w_carrierR_cast (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S) :
    (CV.carrierR hn hG hS q : ℤ) =
      |CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q)| :=
  CV.carrierR_cast hn hG hS q

/-- Under a nonzero selector every corner turn of `q` is the common sign `s = ±1`. -/
theorem r174w_uniform_of_weight_ne_zero (hn : 3 ≤ n) (hP : CrossingGeometry P) {S : Finset (Crossing P)}
    (hS : GeoIndependent hP S) (q : GeoComponent hP S) (h : CV.weight hP S q ≠ 0) :
    (∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1) ∨ (∀ a ∈ r174w_corners hP S q, r174w_tau P a = 1) := by
  classical
  rw [r174w_weight_eq hn hP hS q] at h
  unfold r174w_F at h
  by_cases hA : ∀ a ∈ r174w_corners hP S q, r174w_tau P a = -1
  · exact Or.inl hA
  · right
    rw [ite_eq_right hA] at h
    by_contra hB
    rw [ite_eq_right hB] at h
    exact h rfl

/-- All corner turns `= 1` gives `rot ≥ 1`; all `= −1` gives `rot ≤ −1` (CV:lem:uniformrot (i)). -/
theorem r174w_rot_of_uniform (hn : 3 ≤ n) (hG : CV.Generic P) {S : Finset (Crossing P)}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (q : GeoComponent hG.crossingGeometry S)
    (hu : (∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = -1) ∨
      (∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = 1)) :
    (CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) ≤ -1 ∧
        ∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = -1) ∨
    (1 ≤ CV.rot (geoCornerPolygon hG.crossingGeometry S q) (CV.carrierPolygon_cvRegular hn hG hS q) ∧
        ∀ a ∈ r174w_corners hG.crossingGeometry S q, r174w_tau P a = 1) := by
  have hSi := CV.geoIndependent_of_mem_Ind _ hS
  rcases hu with hu | hu
  · left
    refine ⟨CV.uniformrot.neg_le_neg_one _ _ _ fun k => ?_, hu⟩
    rw [r174w_principalTurn_eq hn _ hSi q k]
    have hk := hu _ ((r174w_mem_corners _ _ q _).mpr (geoCornerMark_mem _ S q k))
    have hs := r174w_sign_theta (P := P) (geoCornerMark hG.crossingGeometry S q k) (by rw [hk]; decide)
    rw [hk] at hs
    exact sign_eq_neg_one_iff.mp hs
  · right
    refine ⟨CV.uniformrot.pos_ge_one _ _ _ fun k => ?_, hu⟩
    rw [r174w_principalTurn_eq hn _ hSi q k]
    have hk := hu _ ((r174w_mem_corners _ _ q _).mpr (geoCornerMark_mem _ S q k))
    have hs := r174w_sign_theta (P := P) (geoCornerMark hG.crossingGeometry S q k) (by rw [hk]; decide)
    rw [hk] at hs
    exact sign_eq_one_iff.mp hs

/-! #### The selector on split corner sets, and the rotation sum -/

/-- `F` on `insert a C₁`, `insert b C₂` against `insert c (C₁ ∪ C₂)` with `τ(a) = τ(b) = τ(c) = τ ≠ 0`:
`F(A) F(B) = −τ F(AB)`. -/
theorem r174w_F_split (C₁ C₂ : Finset (Mark P)) (hdisj : Disjoint C₁ C₂) (a b c : Mark P)
    (ha : a ∉ C₁) (hb : b ∉ C₂) (hc : c ∉ C₁ ∪ C₂) (τ : SignType) (hτ : τ ≠ 0)
    (hta : r174w_tau P a = τ) (htb : r174w_tau P b = τ) (htc : r174w_tau P c = τ) :
    r174w_F P (insert a C₁) * r174w_F P (insert b C₂) = -(τ : ℤ) * r174w_F P (insert c (C₁ ∪ C₂)) := by
  unfold r174w_F
  simp only [Finset.forall_mem_insert, Finset.forall_mem_union, hta, htb, htc,
    Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem hc,
    Finset.card_union_of_disjoint hdisj]
  rcases τ with _ | _ | _
  · exact absurd rfl hτ
  · have e1 : ((SignType.neg : SignType) = -1) := rfl
    have e2 : ¬ ((-1 : SignType) = 1) := by decide
    have hneg : ((-1 : SignType) : ℤ) = -1 := rfl
    simp only [e1, e2, true_and, false_and, ↓reduceIte, hneg]
    by_cases h1 : ∀ x ∈ C₁, r174w_tau P x = -1 <;> by_cases h2 : ∀ x ∈ C₂, r174w_tau P x = -1
    · simp only [eq_true h1, eq_true h2, and_self, ↓reduceIte]; norm_num
    · simp only [eq_true h1, eq_false h2, and_false, ↓reduceIte]; norm_num
    · simp only [eq_false h1, eq_true h2, false_and, ↓reduceIte]; norm_num
    · simp only [eq_false h1, eq_false h2, and_self, ↓reduceIte]; norm_num
  · have e1 : ¬ ((1 : SignType) = -1) := by decide
    have e2 : ((SignType.pos : SignType) = 1) := rfl
    have hpos : ((1 : SignType) : ℤ) = 1 := rfl
    simp only [e2, e1, true_and, false_and, ↓reduceIte, hpos]
    by_cases h1 : ∀ x ∈ C₁, r174w_tau P x = 1 <;> by_cases h2 : ∀ x ∈ C₂, r174w_tau P x = 1
    · simp only [eq_true h1, eq_true h2, and_self, ↓reduceIte]; ring
    · simp only [eq_true h1, eq_false h2, and_false, ↓reduceIte]; ring
    · simp only [eq_false h1, eq_true h2, false_and, ↓reduceIte]; ring
    · simp only [eq_false h1, eq_false h2, and_self, ↓reduceIte]; ring

/-- `F` on `insert a (insert b C)` against `insert c C` with `τ(a) = τ(b) = τ(c) = τ ≠ 0`: `F(C') = −τ F(C)`. -/
theorem r174w_F_two (C : Finset (Mark P)) (a b c : Mark P) (ha : a ∉ insert b C) (hb : b ∉ C) (hc : c ∉ C)
    (τ : SignType) (hτ : τ ≠ 0) (hta : r174w_tau P a = τ) (htb : r174w_tau P b = τ) (htc : r174w_tau P c = τ) :
    r174w_F P (insert a (insert b C)) = -(τ : ℤ) * r174w_F P (insert c C) := by
  unfold r174w_F
  simp only [Finset.forall_mem_insert, hta, htb, htc, Finset.card_insert_of_notMem ha,
    Finset.card_insert_of_notMem hb, Finset.card_insert_of_notMem hc]
  rcases τ with _ | _ | _
  · exact absurd rfl hτ
  · have e1 : ((SignType.neg : SignType) = -1) := rfl
    have e2 : ¬ ((-1 : SignType) = 1) := by decide
    have hneg : ((-1 : SignType) : ℤ) = -1 := rfl
    simp only [e1, e2, true_and, false_and, ↓reduceIte, hneg]
    by_cases h1 : ∀ x ∈ C, r174w_tau P x = -1
    · simp only [eq_true h1, ↓reduceIte]; norm_num
    · simp only [eq_false h1, ↓reduceIte]; norm_num
  · have e1 : ¬ ((1 : SignType) = -1) := by decide
    have e2 : ((SignType.pos : SignType) = 1) := rfl
    have hpos : ((1 : SignType) : ℤ) = 1 := rfl
    simp only [e2, e1, true_and, false_and, ↓reduceIte, hpos]
    by_cases h1 : ∀ x ∈ C, r174w_tau P x = 1
    · simp only [eq_true h1, ↓reduceIte]; ring
    · simp only [eq_false h1, ↓reduceIte]; ring

/-- **The rotations add** when the corner sets split as `insert c (RA ∪ RB)` against `insert a RA`,
`insert b RB` with `θ(a) + θ(b) = θ(c)`. -/
theorem r174w_rot_add (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry S₁) (qA qB : GeoComponent hG.crossingGeometry S₂)
    (RA RB : Finset (Mark P)) (hdisj : Disjoint RA RB) (a b c : Mark P)
    (ha : a ∉ RA) (hb : b ∉ RB) (hc : c ∉ RA ∪ RB)
    (hA : r174w_corners hG.crossingGeometry S₂ qA = insert a RA)
    (hB : r174w_corners hG.crossingGeometry S₂ qB = insert b RB)
    (hAB : r174w_corners hG.crossingGeometry S₁ qAB = insert c (RA ∪ RB))
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c) :
    CV.rot (geoCornerPolygon hG.crossingGeometry S₁ qAB) (CV.carrierPolygon_cvRegular hn hG hS₁ qAB) =
      CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qA) (CV.carrierPolygon_cvRegular hn hG hS₂ qA) +
        CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qB) (CV.carrierPolygon_cvRegular hn hG hS₂ qB) := by
  classical
  have h1 := r174w_two_pi_rot hn hG hS₁ qAB
  have h2 := r174w_two_pi_rot hn hG hS₂ qA
  have h3 := r174w_two_pi_rot hn hG hS₂ qB
  rw [hAB, Finset.sum_insert hc, Finset.sum_union hdisj] at h1
  rw [hA, Finset.sum_insert ha] at h2
  rw [hB, Finset.sum_insert hb] at h3
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply Int.cast_injective (α := ℝ)
  apply mul_left_cancel₀ hpi
  rw [Int.cast_add, mul_add, h1, h2, h3, ← hθ]
  ring

/-- The same with `insert a (insert b RC)` against `insert c RC`: the rotations agree. -/
theorem r174w_rot_eq_two (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry S₁) (qC' : GeoComponent hG.crossingGeometry S₂)
    (RC : Finset (Mark P)) (a b c : Mark P) (ha : a ∉ insert b RC) (hb : b ∉ RC) (hc : c ∉ RC)
    (hC' : r174w_corners hG.crossingGeometry S₂ qC' = insert a (insert b RC))
    (hC : r174w_corners hG.crossingGeometry S₁ qC = insert c RC)
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c) :
    CV.rot (geoCornerPolygon hG.crossingGeometry S₂ qC') (CV.carrierPolygon_cvRegular hn hG hS₂ qC') =
      CV.rot (geoCornerPolygon hG.crossingGeometry S₁ qC) (CV.carrierPolygon_cvRegular hn hG hS₁ qC) := by
  classical
  have h1 := r174w_two_pi_rot hn hG hS₁ qC
  have h2 := r174w_two_pi_rot hn hG hS₂ qC'
  rw [hC, Finset.sum_insert hc] at h1
  rw [hC', Finset.sum_insert ha, Finset.sum_insert hb] at h2
  have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
  apply Int.cast_injective (α := ℝ)
  apply mul_left_cancel₀ hpi
  rw [h1, h2, ← hθ]
  ring

/-- `R(AB) = R(A) + R(B)` under a nonzero selector of `AB` (the split of `r174w_rot_add`, with
`τ(a) = τ(b) = τ(c)`: `A`, `B` inherit the uniform sign, so the rotations have one sign and the
absolute values add). -/
theorem r174w_carrierR_add_of (hn : 3 ≤ n) (hG : CV.Generic P) {S₁ S₂ : Finset (Crossing P)}
    (hS₁ : S₁ ∈ CV.Ind hG.crossingGeometry) (hS₂ : S₂ ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry S₁) (qA qB : GeoComponent hG.crossingGeometry S₂)
    (RA RB : Finset (Mark P)) (hdisj : Disjoint RA RB) (a b c : Mark P)
    (ha : a ∉ RA) (hb : b ∉ RB) (hc : c ∉ RA ∪ RB)
    (hA : r174w_corners hG.crossingGeometry S₂ qA = insert a RA)
    (hB : r174w_corners hG.crossingGeometry S₂ qB = insert b RB)
    (hAB : r174w_corners hG.crossingGeometry S₁ qAB = insert c (RA ∪ RB))
    (hθ : r174w_theta P a + r174w_theta P b = r174w_theta P c)
    (hτa : r174w_tau P a = r174w_tau P c) (hτb : r174w_tau P b = r174w_tau P c)
    (hw : CV.weight hG.crossingGeometry S₁ qAB ≠ 0) :
    CV.carrierR hn hG hS₁ qAB = CV.carrierR hn hG hS₂ qA + CV.carrierR hn hG hS₂ qB := by
  classical
  have hrot := r174w_rot_add hn hG hS₁ hS₂ qAB qA qB RA RB hdisj a b c ha hb hc hA hB hAB hθ
  have hcAB : c ∈ r174w_corners hG.crossingGeometry S₁ qAB := by rw [hAB]; exact Finset.mem_insert_self _ _
  have hRA : ∀ z ∈ RA, z ∈ r174w_corners hG.crossingGeometry S₁ qAB := fun z hz => by
    rw [hAB]; exact Finset.mem_insert_of_mem (Finset.mem_union_left _ hz)
  have hRB : ∀ z ∈ RB, z ∈ r174w_corners hG.crossingGeometry S₁ qAB := fun z hz => by
    rw [hAB]; exact Finset.mem_insert_of_mem (Finset.mem_union_right _ hz)
  have hu := r174w_uniform_of_weight_ne_zero hn hG.crossingGeometry (CV.geoIndependent_of_mem_Ind _ hS₁) qAB hw
  -- `A` and `B` inherit the uniform sign
  have huA : (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qA, r174w_tau P z = -1) ∨
      (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qA, r174w_tau P z = 1) := by
    rw [hA]
    rcases hu with hu | hu
    · left; rw [Finset.forall_mem_insert]; exact ⟨hτa.trans (hu c hcAB), fun z hz => hu z (hRA z hz)⟩
    · right; rw [Finset.forall_mem_insert]; exact ⟨hτa.trans (hu c hcAB), fun z hz => hu z (hRA z hz)⟩
  have huB : (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qB, r174w_tau P z = -1) ∨
      (∀ z ∈ r174w_corners hG.crossingGeometry S₂ qB, r174w_tau P z = 1) := by
    rw [hB]
    rcases hu with hu | hu
    · left; rw [Finset.forall_mem_insert]; exact ⟨hτb.trans (hu c hcAB), fun z hz => hu z (hRB z hz)⟩
    · right; rw [Finset.forall_mem_insert]; exact ⟨hτb.trans (hu c hcAB), fun z hz => hu z (hRB z hz)⟩
  have hsA := r174w_rot_of_uniform hn hG hS₂ qA huA
  have hsB := r174w_rot_of_uniform hn hG hS₂ qB huB
  unfold CV.carrierR CV.rotAbs
  rw [hrot]
  rcases hsA with ⟨hA1, hA2⟩ | ⟨hA1, hA2⟩ <;> rcases hsB with ⟨hB1, hB2⟩ | ⟨hB1, hB2⟩
  · exact Int.natAbs_add_of_nonpos (by omega) (by omega)
  · exfalso
    -- mixed signs: `c` would have both turn signs
    have h1 := hA2 a (by rw [hA]; exact Finset.mem_insert_self _ _)
    have h2 := hB2 b (by rw [hB]; exact Finset.mem_insert_self _ _)
    rw [hτa] at h1; rw [hτb] at h2; rw [h1] at h2; exact absurd h2 (by decide)
  · exfalso
    have h1 := hA2 a (by rw [hA]; exact Finset.mem_insert_self _ _)
    have h2 := hB2 b (by rw [hB]; exact Finset.mem_insert_self _ _)
    rw [hτa] at h1; rw [hτb] at h2; rw [h1] at h2; exact absurd h2 (by decide)
  · exact Int.natAbs_add_of_nonneg (by omega) (by omega)

end R174W_Corners


/-! ### C0. Real cyclic-order helpers -/

section R174W_Cyc

set_option linter.unusedTactic false
set_option linter.unreachableTactic false

theorem r174w_cyc_trans_left {a u v w : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween a v w) :
    cycBetween a u w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

theorem r174w_cyc_trans_right {a u v w : ℝ} (h1 : cycBetween a v w) (h2 : cycBetween v u w) :
    cycBetween a u w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

/-- Two points of the arc `(a, w)` are ordered: `u` before `v` or after. -/
theorem r174w_cyc_split {a u v w : ℝ} (h1 : cycBetween a u w) (h2 : cycBetween a v w) (huv : u ≠ v) :
    cycBetween a u v ∨ cycBetween v u w := by
  rcases lt_or_gt_of_ne huv with h | h
  · unfold cycBetween at *
    rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
      first
      | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | (exfalso; linarith)
  · unfold cycBetween at *
    rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
      first
      | exact Or.inl (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inl (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inl (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
      | exact Or.inr (Or.inr (Or.inl ⟨by linarith, by linarith⟩))
      | exact Or.inr (Or.inr (Or.inr ⟨by linarith, by linarith⟩))
      | (exfalso; linarith)

/-- The arcs `(a, v)` and `(v, a)` are disjoint. -/
theorem r174w_cyc_asymm {a u v : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween v u a) : False := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> linarith

/-- `u ∈ (a, v)`, `v ∈ (a, w)` give `v ∈ (u, w)`. -/
theorem r174w_cyc_mid {a u v w : ℝ} (h1 : cycBetween a u v) (h2 : cycBetween a v w) :
    cycBetween u v w := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

/-- `u ∈ (a, w)`, `v ∈ (u, w)` give `w ∈ (v, u)` (wrapping through `a`). -/
theorem r174w_cyc_wrap {a u v w : ℝ} (h1 : cycBetween a u w) (h2 : cycBetween u v w) :
    cycBetween v w u := by
  unfold cycBetween at *
  rcases h1 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;> rcases h2 with ⟨_, _⟩ | ⟨_, _⟩ | ⟨_, _⟩ <;>
    first
    | exact Or.inl ⟨by linarith, by linarith⟩
    | exact Or.inr (Or.inl ⟨by linarith, by linarith⟩)
    | exact Or.inr (Or.inr ⟨by linarith, by linarith⟩)
    | (exfalso; linarith)

theorem r174w_cyc_ne_left {a u v : ℝ} (h : cycBetween a u v) : a ≠ u := by
  rintro rfl; exact not_cycBetween_self_left _ _ h

theorem r174w_cyc_ne_right {a u v : ℝ} (h : cycBetween a u v) : u ≠ v := by
  rintro rfl; exact not_cycBetween_self_mid _ _ h

end R174W_Cyc

/-! ### C1–C4. The configuration on the two-edge side: supports, owners, child data -/

section R174W_Config

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} {hP : CrossingGeometry P} {hP' : CrossingGeometry P'}
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hP hP' hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

attribute [local instance] Classical.propDecidable
attribute [local instance high] r174w_decEqCrossing

/-- The child data of one insertion, read on the mark keys: the new carrier of `v` is `v` together with
the marks of the old carrier strictly between `twin v` and `v`; the new carrier of `twin v` is `twin v`
with the marks strictly between `v` and `twin v`. -/
theorem r174w_child (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (v : Visit P)
    (hv : v.1 ∉ T) (hc : geoOwner hP T (Sum.inr v) = geoOwner hP T (Sum.inr (visitTwin v))) :
    (∀ z : Mark P, geoOwner hP (insert v.1 T) z = geoOwner hP (insert v.1 T) (Sum.inr v) ↔
      z = Sum.inr v ∨ (cycBetween (geoMarkKey hP (Sum.inr (visitTwin v))) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr v)) ∧ geoOwner hP T z = geoOwner hP T (Sum.inr v))) ∧
    (∀ z : Mark P, geoOwner hP (insert v.1 T) z = geoOwner hP (insert v.1 T) (Sum.inr (visitTwin v)) ↔
      z = Sum.inr (visitTwin v) ∨ (cycBetween (geoMarkKey hP (Sum.inr v)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr (visitTwin v))) ∧ geoOwner hP T z = geoOwner hP T (Sum.inr v))) := by
  obtain ⟨k, A, B, hrot, -, -, -, hL, hR, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI v hv hc
  refine ⟨fun z => ?_, fun z => ?_⟩
  · rw [hL z, List.mem_cons, geoMarkList_filter_right_iff hP T _ k _ _ A B hrot z]
    exact Iff.rfl
  · rw [hR z, List.mem_cons, geoMarkList_filter_left_iff hP T _ k _ _ A B hrot z]
    exact Iff.rfl

include D

theorem r174w_x_not_mem_Q : x ∉ Q := fun h => D.Q_out x h D.xT
theorem r174w_w_not_mem_Q : w ∉ Q := fun h => D.Q_out w h D.wT
theorem r174w_m_not_mem_Q : m ∉ Q := fun h => D.Q_out m h D.mT

theorem r174w_Q_indep : GeoIndependent hP Q := CV.geoIndependent_of_mem_Ind hP D.Q_ind

/-- `Q ∪ {y}` is independent for every triangle crossing `y` (full availability). -/
theorem r174w_insert_indep {y : Crossing P} (hy : y.val ∈ triangleSupports e f g) :
    GeoIndependent hP (insert y Q) := by
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · exact fun h => D.Q_avail b hb a hy (geometricInterlaces_symm hP h)
  · exact D.Q_avail a ha b hy
  · exact r174w_Q_indep D a ha b hb hab

theorem r174w_Sx_indep : GeoIndependent hP (insert x Q) := r174w_insert_indep D D.xT
theorem r174w_Sm_indep : GeoIndependent hP (insert m Q) := r174w_insert_indep D D.mT

theorem r174w_Sxw_indep : GeoIndependent hP (insert w (insert x Q)) := by
  intro a ha b hb hab
  rw [Finset.mem_insert] at ha hb
  rcases ha with rfl | ha <;> rcases hb with rfl | hb
  · exact absurd rfl hab
  · rw [Finset.mem_insert] at hb
    rcases hb with rfl | hb
    · exact fun h => D.hxw (geometricInterlaces_symm hP h)
    · exact fun h => D.Q_avail b hb a D.wT (geometricInterlaces_symm hP h)
  · rw [Finset.mem_insert] at ha
    rcases ha with rfl | ha
    · exact D.hxw
    · exact D.Q_avail a ha b D.wT
  · exact r174w_Sx_indep D a ha b hb hab

theorem r174w_w_not_mem_Sx : w ∉ insert x Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xw h.symm
  · exact r174w_w_not_mem_Q D h

theorem r174w_m_not_mem_Sx : m ∉ insert x Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xm h.symm
  · exact r174w_m_not_mem_Q D h

theorem r174w_m_not_mem_Sxw : m ∉ insert w (insert x Q) := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.wm h.symm
  · exact r174w_m_not_mem_Sx D h

theorem r174w_x_not_mem_Sm' : x ∉ insert m Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.xm h
  · exact r174w_x_not_mem_Q D h

theorem r174w_w_not_mem_Sm' : w ∉ insert m Q := by
  rw [Finset.mem_insert]
  rintro (h | h)
  · exact D.wm h
  · exact r174w_w_not_mem_Q D h

/-! #### Pair owners (both visits of an unselected non-neighbour on one carrier) -/

theorem r174w_ownerQ_m : geoOwner hP Q (Sum.inr D.m₁) = geoOwner hP Q (Sum.inr D.m₃) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sm_indep D) Q (Finset.subset_insert _ _)
    D.m₁ (Finset.mem_insert_self _ _) (r174w_m_not_mem_Q D)
  rwa [D.twin_m₁] at h

theorem r174w_ownerQ_x : geoOwner hP Q (Sum.inr D.x₁) = geoOwner hP Q (Sum.inr D.x₂) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sx_indep D) Q (Finset.subset_insert _ _)
    D.x₁ (Finset.mem_insert_self _ _) (r174w_x_not_mem_Q D)
  rwa [D.twin_x₁] at h

theorem r174w_ownerx_w :
    geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.w₃) := by
  have h := geoIndependent_remaining_pair_owners hP (r174w_Sxw_indep D) (insert x Q)
    (Finset.subset_insert _ _) D.w₂ (Finset.mem_insert_self _ _) (r174w_w_not_mem_Sx D)
  rwa [D.twin_w₂] at h

/-! #### Separations: the two visits of a selected crossing, or of a neighbour, lie on different carriers -/

theorem r174w_sep_m_Sm : geoOwner hP (insert m Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
  have h := geo_selected_visits_separated hP (r174w_Sm_indep D) D.m₁ (Finset.mem_insert_self _ _)
  rwa [D.twin_m₁] at h

theorem r174w_sep_x_Sx : geoOwner hP (insert x Q) (Sum.inr D.x₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
  have h := geo_selected_visits_separated hP (r174w_Sx_indep D) D.x₁ (Finset.mem_insert_self _ _)
  rwa [D.twin_x₁] at h

theorem r174w_sep_x_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) := by
  have h := geo_selected_visits_separated hP (r174w_Sxw_indep D) D.x₁
    (Finset.mem_insert_of_mem (Finset.mem_insert_self _ _))
  rwa [D.twin_x₁] at h

theorem r174w_sep_w_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) := by
  have h := geo_selected_visits_separated hP (r174w_Sxw_indep D) D.w₂ (Finset.mem_insert_self _ _)
  rwa [D.twin_w₂] at h

omit D in
/-- A neighbour of a selected crossing has its two visits on different carriers. -/
theorem r174w_sep_of_neighbor {S : Finset (Crossing P)} (hS : GeoIndependent hP S) {y s : Crossing P}
    (hsS : s ∈ S) (hys : GeometricInterlaces hP y s) (v : Visit P) (hv : v.1 = y) :
    geoOwner hP S (Sum.inr v) ≠ geoOwner hP S (Sum.inr (visitTwin v)) :=
  geo_neighbor_visit_owners_ne hP hS ((mem_geoSupportNeighbors hP S y).mpr ⟨s, hsS, hys⟩) v hv

theorem r174w_sep_x_Sm : geoOwner hP (insert m Q) (Sum.inr D.x₁) ≠ geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
  have h := r174w_sep_of_neighbor (r174w_Sm_indep D) (Finset.mem_insert_self m Q) D.hxm D.x₁ rfl
  rwa [D.twin_x₁] at h

theorem r174w_sep_w_Sm : geoOwner hP (insert m Q) (Sum.inr D.w₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.w₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sm_indep D) (Finset.mem_insert_self m Q) D.hwm D.w₂ rfl
  rwa [D.twin_w₂] at h

theorem r174w_sep_m_Sx : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.m₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sx_indep D) (Finset.mem_insert_self x Q)
    (geometricInterlaces_symm hP D.hxm) D.m₁ rfl
  rwa [D.twin_m₁] at h

theorem r174w_sep_m_Sxw :
    geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) ≠ geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) := by
  have h := r174w_sep_of_neighbor (r174w_Sxw_indep D) (Finset.mem_insert_self w _)
    (geometricInterlaces_symm hP D.hwm) D.m₁ rfl
  rwa [D.twin_m₁] at h

/-! #### Adjacent unselected visits share a carrier -/

theorem r174w_ownerQ_x₁_m₁ : geoOwner hP Q (Sum.inr D.x₁) = geoOwner hP Q (Sum.inr D.m₁) :=
  GT_owner_eq_of_adjacent hP Q D.adj1 rfl (r174w_x_not_mem_Q D) (r174w_m_not_mem_Q D)

theorem r174w_ownerQ_x₂_w₂ : geoOwner hP Q (Sum.inr D.x₂) = geoOwner hP Q (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hP Q D.adj2 rfl (r174w_x_not_mem_Q D) (r174w_w_not_mem_Q D)

theorem r174w_ownerQ_w₃_m₃ : geoOwner hP Q (Sum.inr D.w₃) = geoOwner hP Q (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP Q D.adj3 rfl (r174w_w_not_mem_Q D) (r174w_m_not_mem_Q D)

theorem r174w_ownerx_w₃_m₃ :
    geoOwner hP (insert x Q) (Sum.inr D.w₃) = geoOwner hP (insert x Q) (Sum.inr D.m₃) :=
  GT_owner_eq_of_adjacent hP _ D.adj3 rfl (r174w_w_not_mem_Sx D) (r174w_m_not_mem_Sx D)

theorem r174w_ownerm_x₂_w₂ :
    geoOwner hP (insert m Q) (Sum.inr D.x₂) = geoOwner hP (insert m Q) (Sum.inr D.w₂) :=
  GT_owner_eq_of_adjacent hP _ D.adj2 rfl (r174w_x_not_mem_Sm' D) (r174w_w_not_mem_Sm' D)

/-- All six local visits lie on one carrier `q₀` of `Q`. -/
theorem r174w_ownerQ_w₂ : geoOwner hP Q (Sum.inr D.w₂) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [← r174w_ownerQ_x₂_w₂ D, ← r174w_ownerQ_x D, r174w_ownerQ_x₁_m₁ D]
theorem r174w_ownerQ_x₂' : geoOwner hP Q (Sum.inr D.x₂) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [← r174w_ownerQ_x D, r174w_ownerQ_x₁_m₁ D]
theorem r174w_ownerQ_w₃ : geoOwner hP Q (Sum.inr D.w₃) = geoOwner hP Q (Sum.inr D.m₁) := by
  rw [r174w_ownerQ_w₃_m₃ D, ← r174w_ownerQ_m D]
theorem r174w_ownerQ_m₃' : geoOwner hP Q (Sum.inr D.m₃) = geoOwner hP Q (Sum.inr D.m₁) :=
  (r174w_ownerQ_m D).symm

/-! #### The three splits, in key form -/

/-- Split `m` (`Q → Q ∪ {m}`). -/
theorem r174w_split_m :
    (∀ z : Mark P, geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁) ↔
      z = Sum.inr D.m₁ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.m₁)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) ∧
    (∀ z : Mark P, geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃) ↔
      z = Sum.inr D.m₃ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.m₃)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) := by
  have h := r174w_child (hP := hP) Q (geoIndependent_inheritsMarkOrder hP (r174w_Q_indep D)) D.m₁
    (r174w_m_not_mem_Q D) (by rw [D.twin_m₁]; exact r174w_ownerQ_m D)
  rw [D.twin_m₁] at h
  exact h

/-- Split `x` (`Q → Q ∪ {x}`). -/
theorem r174w_split_x :
    (∀ z : Mark P, geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁) ↔
      z = Sum.inr D.x₁ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.x₁)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) ∧
    (∀ z : Mark P, geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂) ↔
      z = Sum.inr D.x₂ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.x₂)) ∧ geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁))) := by
  have h := r174w_child (hP := hP) Q (geoIndependent_inheritsMarkOrder hP (r174w_Q_indep D)) D.x₁
    (r174w_x_not_mem_Q D) (by rw [D.twin_x₁]; exact r174w_ownerQ_x D)
  rw [D.twin_x₁, r174w_ownerQ_x₁_m₁ D] at h
  exact h

/-- Split `w` (`Q ∪ {x} → Q ∪ {x, w}`). -/
theorem r174w_split_w :
    (∀ z : Mark P, geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ↔
      z = Sum.inr D.w₂ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.w₃)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.w₂)) ∧ geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂))) ∧
    (∀ z : Mark P, geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) ↔
      z = Sum.inr D.w₃ ∨ (cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP z)
        (geoMarkKey hP (Sum.inr D.w₃)) ∧ geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂))) := by
  have h := r174w_child (hP := hP) (insert x Q) (geoIndependent_inheritsMarkOrder hP (r174w_Sx_indep D)) D.w₂
    (r174w_w_not_mem_Sx D) (by rw [D.twin_w₂]; exact r174w_ownerx_w D)
  rw [D.twin_w₂] at h
  exact h

/-- Unaffected carriers of the `w`-split: a carrier of `Q ∪ {x}` not through `w₂` is a carrier of
`Q ∪ {x, w}`. -/
theorem r174w_unaffected_w (z : Mark P)
    (hz : geoOwner hP (insert x Q) z ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂)) (z' : Mark P) :
    geoOwner hP (insert w (insert x Q)) z' = geoOwner hP (insert w (insert x Q)) z ↔
      geoOwner hP (insert x Q) z' = geoOwner hP (insert x Q) z := by
  have h := geoOwner_insert_iff_of_unaffected hP (insert x Q) D.w₂ (r174w_w_not_mem_Sx D)
    (by rw [D.twin_w₂]; exact r174w_ownerx_w D) (geoOwner hP (insert x Q) z) hz z rfl z'
  exact h

/-! #### Partition: every mark of `q₀` lands in one of the two children -/

omit D in
theorem r174w_key_ne {a b : Mark P} (h : a ≠ b) : geoMarkKey hP a ≠ geoMarkKey hP b :=
  fun h' => h (geoMarkKey_injective hP h')

omit [NeZero n] D in
theorem r174w_inr_ne {v u : Visit P} (h : v ≠ u) : (Sum.inr v : Mark P) ≠ Sum.inr u :=
  fun h' => h (Sum.inr.inj h')

theorem r174w_part_m (z : Mark P) (hz : geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁)) :
    geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁) ∨
      geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
  obtain ⟨h1, h3⟩ := r174w_split_m D
  by_cases hz1 : z = Sum.inr D.m₁
  · exact Or.inl ((h1 z).mpr (Or.inl hz1))
  by_cases hz3 : z = Sum.inr D.m₃
  · exact Or.inr ((h3 z).mpr (Or.inl hz3))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz1)) (r174w_key_ne (r174w_inr_ne D.m₁_ne_m₃))
    (r174w_key_ne hz3) with h | h
  · exact Or.inr ((h3 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h1 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

theorem r174w_part_x (z : Mark P) (hz : geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁)) :
    geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁) ∨
      geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
  obtain ⟨h1, h2⟩ := r174w_split_x D
  by_cases hz1 : z = Sum.inr D.x₁
  · exact Or.inl ((h1 z).mpr (Or.inl hz1))
  by_cases hz2 : z = Sum.inr D.x₂
  · exact Or.inr ((h2 z).mpr (Or.inl hz2))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz1)) (r174w_key_ne (r174w_inr_ne D.x₁_ne_x₂))
    (r174w_key_ne hz2) with h | h
  · exact Or.inr ((h2 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h1 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

theorem r174w_part_w (z : Mark P)
    (hz : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.w₂)) :
    geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) ∨
      geoOwner hP (insert w (insert x Q)) z = geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) := by
  obtain ⟨h2, h3⟩ := r174w_split_w D
  by_cases hz2 : z = Sum.inr D.w₂
  · exact Or.inl ((h2 z).mpr (Or.inl hz2))
  by_cases hz3 : z = Sum.inr D.w₃
  · exact Or.inr ((h3 z).mpr (Or.inl hz3))
  rcases GT_cyc_total (r174w_key_ne (Ne.symm hz2)) (r174w_key_ne (r174w_inr_ne D.w₂_ne_w₃))
    (r174w_key_ne hz3) with h | h
  · exact Or.inr ((h3 z).mpr (Or.inr ⟨h, hz⟩))
  · exact Or.inl ((h2 z).mpr (Or.inr ⟨GT_cyc_rotate.mp h, hz⟩))

/-- A mark of a child of `q₀` lies on `q₀`. -/
theorem r174w_onZ_of_m₁ (z : Mark P) (hz : z ≠ Sum.inr D.m₁)
    (h : geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₁)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_m D).1 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_m₃ (z : Mark P) (hz : z ≠ Sum.inr D.m₃)
    (h : geoOwner hP (insert m Q) z = geoOwner hP (insert m Q) (Sum.inr D.m₃)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_m D).2 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_x₁ (z : Mark P) (hz : z ≠ Sum.inr D.x₁)
    (h : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₁)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_x D).1 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

theorem r174w_onZ_of_x₂ (z : Mark P) (hz : z ≠ Sum.inr D.x₂)
    (h : geoOwner hP (insert x Q) z = geoOwner hP (insert x Q) (Sum.inr D.x₂)) :
    geoOwner hP Q z = geoOwner hP Q (Sum.inr D.m₁) := by
  rcases ((r174w_split_x D).2 z).mp h with h' | h'
  · exact absurd h' hz
  · exact h'.2

omit D in
/-- The mark immediately after `a` in the traversal: no mark strictly between. -/
theorem r174w_no_between {a b : Mark P} (h : geoMarkSuccessor hP a = b) (u : Mark P) :
    ¬ cycBetween (geoMarkKey hP a) (geoMarkKey hP u) (geoMarkKey hP b) := by
  have h' : (geoMarkSuccessor hP).symm b = a := (Equiv.symm_apply_eq _).mpr h.symm
  have := geoMarkSuccessor_prev_no_mark_between hP b u
  rw [h'] at this
  exact this

/-! #### C5. The case split -/

omit D in
theorem r174w_owner_eq_of_succ {S : Finset (Crossing P)} {a b : Mark P}
    (h : geoSmoothingSuccessor hP S a = b) : geoOwner hP S b = geoOwner hP S a := by
  rw [← h]; exact geoOwner_successor hP S a

/-- A mark is *nonspecial* if it is none of the six local visits. -/
def r174w_Nonspecial (a : Mark P) : Prop :=
  a ≠ Sum.inr D.x₁ ∧ a ≠ Sum.inr D.x₂ ∧ a ≠ Sum.inr D.w₂ ∧ a ≠ Sum.inr D.w₃ ∧
    a ≠ Sum.inr D.m₁ ∧ a ≠ Sum.inr D.m₃

/-- **The outcome of the orientation case analysis**: the local visit `xA` of `x` and `m₁` lie on one
carrier `A` of `Q ∪ {x, w}`; `wB` (of `w`) and `m₃` on `B`; the other two local visits `xC, wC` on `C'`;
on `Q ∪ {m}`, `mAB` (of `m`) lies with `x₂, w₂` on `AB` and `mC` with `x₁` on `C`; and every
nonspecial mark of `A` or `B` lies on `AB`, every nonspecial mark of `C'` on `C`. -/
structure r174w_Split where
  xA : Visit P
  wB : Visit P
  mAB : Visit P
  hxA : xA.1 = x
  hwB : wB.1 = w
  hmAB : mAB.1 = m
  hcase : (xA = D.x₂ ∧ wB = D.w₃ ∧ mAB = D.m₃) ∨ (xA = D.x₁ ∧ wB = D.w₂ ∧ mAB = D.m₁)
  oA : geoOwner hP (insert w (insert x Q)) (Sum.inr xA) = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁)
  oB : geoOwner hP (insert w (insert x Q)) (Sum.inr wB) = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃)
  oC' : geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) =
    geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin wB))
  oAB : geoOwner hP (insert m Q) (Sum.inr mAB) = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  oC : geoOwner hP (insert m Q) (Sum.inr (visitTwin mAB)) = geoOwner hP (insert m Q) (Sum.inr D.x₁)
  P1 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  P2 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂)
  P3 : ∀ a : Mark P, r174w_Nonspecial D a →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) →
    geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₁)
  onZ_A : ∀ a : Mark P, geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_B : ∀ a : Mark P, geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_C' : ∀ a : Mark P,
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA)) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_AB : ∀ a : Mark P, geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₂) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  onZ_C : ∀ a : Mark P, geoOwner hP (insert m Q) a = geoOwner hP (insert m Q) (Sum.inr D.x₁) →
    geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁)
  triZ : ∀ a : Mark P, geoOwner hP Q a = geoOwner hP Q (Sum.inr D.m₁) →
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) ∨
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) ∨
    geoOwner hP (insert w (insert x Q)) a = geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin xA))

theorem r174w_x₂_ne_m₃ : D.x₂ ≠ D.m₃ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₂_ne_m₁ : D.x₂ ≠ D.m₁ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_m₁ : D.x₁ ≠ D.m₁ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_m₃ : D.x₁ ≠ D.m₃ := fun h => D.xm (congrArg Sigma.fst h)
theorem r174w_x₁_ne_w₂ : D.x₁ ≠ D.w₂ := fun h => D.xw (congrArg Sigma.fst h)
theorem r174w_x₂_ne_w₂ : D.x₂ ≠ D.w₂ := fun h => D.xw (congrArg Sigma.fst h)
theorem r174w_x₂_ne_w₃ : D.x₂ ≠ D.w₃ := fun h => D.xw (congrArg Sigma.fst h)

/-- **Case B** (`x₁` immediately before `m₁` on `ℓ₁`; the printed word `a b A a c B b c C`). -/
def r174w_split_caseB (hB : geoMarkSuccessor hP (Sum.inr D.x₁) = Sum.inr D.m₁) : r174w_Split D := by
  have hxSx : x ∈ insert x Q := Finset.mem_insert_self x Q
  have hxSxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem hxSx
  have hwSxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
  have hmSm : m ∈ insert m Q := Finset.mem_insert_self m Q
  -- (B1) `C = owner_m x₁ ∋ m₁`
  have hB1 : geoOwner hP (insert m Q) (Sum.inr D.m₁) = geoOwner hP (insert m Q) (Sum.inr D.x₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.x₁ (r174w_x_not_mem_Sm' D)]; exact hB)
  -- (B2) in `Q ∪ {x}`: `m₁` on the carrier of `x₂`
  have hB2 : geoOwner hP (insert x Q) (Sum.inr D.m₁) = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₂ hxSx, D.twin_x₂]; exact hB)
  -- (B3) `m₃`, `w₂`, `w₃` on the carrier of `x₁`
  have hB3 : geoOwner hP (insert x Q) (Sum.inr D.m₃) = geoOwner hP (insert x Q) (Sum.inr D.x₁) := by
    rcases r174w_part_x D (Sum.inr D.m₃) (r174w_ownerQ_m₃' D) with h | h
    · exact h
    · exact absurd (hB2.trans h.symm) (r174w_sep_m_Sx D)
  have hB3w : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₁) := by
    rw [r174w_ownerx_w D, r174w_ownerx_w₃_m₃ D, hB3]
  -- (B4) `x₂` immediately before `w₂`
  have hB4 : geoMarkSuccessor hP (Sum.inr D.x₂) = Sum.inr D.w₂ := by
    rcases GT_succ_of_adjacent hP D.adj2 rfl with h | h
    · exact h
    · exfalso
      have h' : geoOwner hP (insert x Q) (Sum.inr D.x₂) = geoOwner hP (insert x Q) (Sum.inr D.w₂) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₂ (r174w_w_not_mem_Sx D)]; exact h)
      exact r174w_sep_x_Sx D (hB3w.symm.trans h'.symm)
  -- (B5) `m₃` immediately before `w₃`
  have hB5 : geoMarkSuccessor hP (Sum.inr D.m₃) = Sum.inr D.w₃ := by
    rcases GT_succ_of_adjacent hP D.adj3 rfl with h | h
    · exfalso
      have h' : geoOwner hP (insert m Q) (Sum.inr D.m₃) = geoOwner hP (insert m Q) (Sum.inr D.w₃) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174w_w_not_mem_Sm' D)]; exact h)
      have hne : geoOwner hP (insert m Q) (Sum.inr D.x₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
        rw [r174w_ownerm_x₂_w₂ D, h']; exact r174w_sep_w_Sm D
      rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h2 | h2
      · exact r174w_sep_x_Sm D (h2.trans hB1).symm
      · exact hne h2
    · exact h
  -- (B6) `AB = owner_m x₂ ∋ m₃`
  have hAB : geoOwner hP (insert m Q) (Sum.inr D.m₃) = geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
    rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h | h
    · exact absurd (h.trans hB1).symm (r174w_sep_x_Sm D)
    · exact h.symm
  have hABw : geoOwner hP (insert m Q) (Sum.inr D.w₂) = geoOwner hP (insert m Q) (Sum.inr D.m₃) := by
    rw [hAB, r174w_ownerm_x₂_w₂ D]
  have hCw : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₁) := by
    rcases r174w_part_m D (Sum.inr D.w₃) (r174w_ownerQ_w₃ D) with h | h
    · exact h
    · exact absurd (hABw.trans h.symm) (r174w_sep_w_Sm D)
  -- (B7) the carriers of `Q ∪ {x, w}`
  have hne_m₁w₂ : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂) := by
    rw [hB2, hB3w]; exact (r174w_sep_x_Sx D).symm
  have hqA : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) :=
    (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ (Sum.inr D.x₂)).mpr hB2.symm
  have hqB : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₃ (r174w_m_not_mem_Sxw D)]; exact hB5)
  have hqC' : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₁ hxSxw, D.twin_x₁]; exact hB4)
  -- (B8) key facts
  have K1 := r174w_no_between (hP := hP) hB
  have K2 := r174w_no_between (hP := hP) hB4
  have K3 := r174w_no_between (hP := hP) hB5
  obtain ⟨Sm1, Sm3⟩ := r174w_split_m D
  obtain ⟨Sx1, Sx2⟩ := r174w_split_x D
  obtain ⟨Sw2, Sw3⟩ := r174w_split_w D
  have c1 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hAB.symm).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₃ D))).1
  have c2 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hABw).resolve_left (r174w_inr_ne D.w₂_ne_m₃)).1
  have c3 : cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₂)) :=
    (((Sx2 _).mp hB2).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₁ D).symm)).1
  have c4 : cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₃)) :=
    (((Sw3 _).mp hqB.symm).resolve_left (r174w_inr_ne D.w₃_ne_m₃.symm)).1
  have c5 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₁)) :=
    (((Sx1 _).mp hB3).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₃ D).symm)).1
  have c8 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hB1.symm).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₁ D))).1
  -- `x₂` before `w₂` inside `(m₁, m₃)`: else `m₃ ∈ (x₂, w₂)`
  have c9 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₃)) := by
    rcases r174w_cyc_split c1 c2 (r174w_key_ne (r174w_inr_ne (r174w_x₂_ne_w₂ D))) with h | h
    · exact r174w_cyc_mid h c2
    · exact absurd (r174w_cyc_wrap c2 h) (K2 _)
  refine ⟨D.x₂, D.w₃, D.m₃, rfl, rfl, rfl, Or.inl ⟨rfl, rfl, rfl⟩, hqA, hqB, ?_, hAB, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.twin_x₂, D.twin_w₃]; exact hqC'.symm
  · rw [D.twin_m₃]; exact hB1
  · -- P1
    intro a ha h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hB2
    obtain ⟨h2, hZ⟩ := ((Sx2 a).mp h1).resolve_left ha.2.1
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.x₂)) := by
      rcases r174w_cyc_split h2 c3 (r174w_key_ne ha.2.2.2.2.1) with h' | h'
      · exact absurd h' (K1 a)
      · exact h'
    rw [← hAB]
    exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_left h3 c1, hZ⟩)
  · -- P2
    intro a ha h
    rw [← hqB] at h
    obtain ⟨h2, hx⟩ := ((Sw3 a).mp h).resolve_left ha.2.2.2.1
    rw [hB3w] at hx
    have hZ := r174w_onZ_of_x₁ D a ha.1 hx
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.m₃)) := by
      rcases r174w_cyc_split h2 c4 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
      · exact h'
      · exact absurd h' (K3 a)
    rw [← hAB]
    exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_right c2 h3, hZ⟩)
  · -- P3
    intro a ha h
    rw [D.twin_x₂, ← hqC'] at h
    obtain ⟨h1, hx⟩ := ((Sw2 a).mp h).resolve_left ha.2.2.1
    rw [hB3w] at hx
    obtain ⟨h2, hZ⟩ := ((Sx1 a).mp hx).resolve_left ha.1
    rcases r174w_cyc_split h2 c5 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
    · exfalso
      rcases r174w_cyc_split h' c9 (r174w_key_ne ha.2.2.1) with h'' | h''
      · exact K2 a h''
      · exact r174w_cyc_asymm (r174w_cyc_trans_left h'' c4) h1
    · rw [← hB1]
      exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_left h' c8, hZ⟩)
  · -- onZ_A
    intro a h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₂) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hB2
    by_cases ha : a = Sum.inr D.x₂
    · rw [ha]; exact r174w_ownerQ_x₂' D
    · exact r174w_onZ_of_x₂ D a ha h1
  · -- onZ_B
    intro a h
    rw [← hqB] at h
    rcases (Sw3 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₃ D
    · rw [hB3w] at hx
      by_cases ha : a = Sum.inr D.x₁
      · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
      · exact r174w_onZ_of_x₁ D a ha hx
  · -- onZ_C'
    intro a h
    rw [D.twin_x₂, ← hqC'] at h
    rcases (Sw2 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₂ D
    · rw [hB3w] at hx
      by_cases ha : a = Sum.inr D.x₁
      · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
      · exact r174w_onZ_of_x₁ D a ha hx
  · -- onZ_AB
    intro a h
    rw [← hAB] at h
    by_cases ha : a = Sum.inr D.m₃
    · rw [ha]; exact r174w_ownerQ_m₃' D
    · exact r174w_onZ_of_m₃ D a ha h
  · -- onZ_C
    intro a h
    rw [← hB1] at h
    by_cases ha : a = Sum.inr D.m₁
    · rw [ha]
    · exact r174w_onZ_of_m₁ D a ha h
  · -- triZ
    intro a hZ
    rcases r174w_part_x D a hZ with h | h
    · rw [← hB3w] at h
      rcases r174w_part_w D a h with h' | h'
      · right; right; rw [D.twin_x₂, ← hqC']; exact h'
      · right; left; rw [← hqB]; exact h'
    · left; exact (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mpr (h.trans hB2.symm)

/-- **Case A** (`m₁` immediately before `x₁` on `ℓ₁`; the reversed traversal). -/
def r174w_split_caseA (hA : geoMarkSuccessor hP (Sum.inr D.m₁) = Sum.inr D.x₁) : r174w_Split D := by
  have hxSx : x ∈ insert x Q := Finset.mem_insert_self x Q
  have hxSxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem hxSx
  have hwSxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
  have hmSm : m ∈ insert m Q := Finset.mem_insert_self m Q
  -- (A1) `C = owner_m x₁ ∋ m₃`
  have hA1 : geoOwner hP (insert m Q) (Sum.inr D.x₁) = geoOwner hP (insert m Q) (Sum.inr D.m₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.m₃ hmSm, D.twin_m₃]; exact hA)
  -- (A2) in `Q ∪ {x}`: `m₁` on the carrier of `x₁`
  have hA2 : geoOwner hP (insert x Q) (Sum.inr D.x₁) = geoOwner hP (insert x Q) (Sum.inr D.m₁) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.m₁ (r174w_m_not_mem_Sx D)]; exact hA)
  -- (A3) `m₃`, `w₂`, `w₃` on the carrier of `x₂`
  have hA3 : geoOwner hP (insert x Q) (Sum.inr D.m₃) = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
    rcases r174w_part_x D (Sum.inr D.m₃) (r174w_ownerQ_m₃' D) with h | h
    · exact absurd (hA2.symm.trans h.symm) (r174w_sep_m_Sx D)
    · exact h
  have hA3w : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₂) := by
    rw [r174w_ownerx_w D, r174w_ownerx_w₃_m₃ D, hA3]
  -- (A4) `w₂` immediately before `x₂`
  have hA4 : geoMarkSuccessor hP (Sum.inr D.w₂) = Sum.inr D.x₂ := by
    rcases GT_succ_of_adjacent hP D.adj2 rfl with h | h
    · exfalso
      have h' : geoOwner hP (insert x Q) (Sum.inr D.w₂) = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_mem hP _ D.x₁ hxSx, D.twin_x₁]; exact h)
      exact r174w_sep_x_Sx D (h'.symm.trans hA3w)
    · exact h
  -- (A5) `w₃` immediately before `m₃`
  have hA5 : geoMarkSuccessor hP (Sum.inr D.w₃) = Sum.inr D.m₃ := by
    rcases GT_succ_of_adjacent hP D.adj3 rfl with h | h
    · exact h
    · exfalso
      have h' : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₁) :=
        r174w_owner_eq_of_succ (by
          rw [geoSmoothingSuccessor_visit_of_mem hP _ D.m₁ hmSm, D.twin_m₁]; exact h)
      have hne : geoOwner hP (insert m Q) (Sum.inr D.x₂) ≠ geoOwner hP (insert m Q) (Sum.inr D.m₁) := by
        rw [r174w_ownerm_x₂_w₂ D, ← h']; exact r174w_sep_w_Sm D
      rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h2 | h2
      · exact hne h2
      · exact r174w_sep_x_Sm D (hA1.trans h2.symm)
  -- (A6) `AB = owner_m x₂ ∋ m₁`
  have hAB : geoOwner hP (insert m Q) (Sum.inr D.m₁) = geoOwner hP (insert m Q) (Sum.inr D.x₂) := by
    rcases r174w_part_m D (Sum.inr D.x₂) (r174w_ownerQ_x₂' D) with h | h
    · exact h.symm
    · exact absurd (hA1.trans h.symm) (r174w_sep_x_Sm D)
  have hABw : geoOwner hP (insert m Q) (Sum.inr D.w₂) = geoOwner hP (insert m Q) (Sum.inr D.m₁) :=
    (r174w_ownerm_x₂_w₂ D).symm.trans hAB.symm
  have hCw : geoOwner hP (insert m Q) (Sum.inr D.w₃) = geoOwner hP (insert m Q) (Sum.inr D.m₃) :=
    (r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_not_mem hP _ D.w₃ (r174w_w_not_mem_Sm' D)]; exact hA5)).symm
  -- (A7) the carriers of `Q ∪ {x, w}`
  have hne_m₁w₂ : geoOwner hP (insert x Q) (Sum.inr D.m₁) ≠ geoOwner hP (insert x Q) (Sum.inr D.w₂) := by
    rw [← hA2, hA3w]; exact r174w_sep_x_Sx D
  have hqA : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₁) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁) :=
    (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ (Sum.inr D.x₁)).mpr hA2
  have hqB : geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃) :=
    (r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.w₂ hwSxw, D.twin_w₂]; exact hA5)).symm
  have hqC' : geoOwner hP (insert w (insert x Q)) (Sum.inr D.x₂) =
      geoOwner hP (insert w (insert x Q)) (Sum.inr D.w₃) :=
    r174w_owner_eq_of_succ (by
      rw [geoSmoothingSuccessor_visit_of_mem hP _ D.w₃ hwSxw, D.twin_w₃]; exact hA4)
  -- (A8) key facts
  have K1 := r174w_no_between (hP := hP) hA
  have K2 := r174w_no_between (hP := hP) hA4
  have K3 := r174w_no_between (hP := hP) hA5
  obtain ⟨Sm1, Sm3⟩ := r174w_split_m D
  obtain ⟨Sx1, Sx2⟩ := r174w_split_x D
  obtain ⟨Sw2, Sw3⟩ := r174w_split_w D
  have c1 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hAB.symm).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₁ D))).1
  have c2 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.m₁)) :=
    (((Sm1 _).mp hABw).resolve_left (r174w_inr_ne D.w₂_ne_m₁)).1
  have c3 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₁)) :=
    (((Sx1 _).mp hA2.symm).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₁ D).symm)).1
  have c4 : cycBetween (geoMarkKey hP (Sum.inr D.w₃)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) :=
    (((Sw2 _).mp hqB.symm).resolve_left (r174w_inr_ne D.w₂_ne_m₃.symm)).1
  have c5 : cycBetween (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.x₂)) :=
    (((Sx2 _).mp hA3).resolve_left (r174w_inr_ne (r174w_x₂_ne_m₃ D).symm)).1
  have c8 : cycBetween (geoMarkKey hP (Sum.inr D.m₁)) (geoMarkKey hP (Sum.inr D.x₁)) (geoMarkKey hP (Sum.inr D.m₃)) :=
    (((Sm3 _).mp hA1).resolve_left (r174w_inr_ne (r174w_x₁_ne_m₃ D))).1
  -- `w₂` before `x₂` inside `(m₃, m₁)`: else `m₁ ∈ (w₂, x₂)`
  have c9 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP (Sum.inr D.w₂)) (geoMarkKey hP (Sum.inr D.x₂)) := by
    rcases r174w_cyc_split c2 c1 (r174w_key_ne (r174w_inr_ne (r174w_x₂_ne_w₂ D).symm)) with h | h
    · exact h
    · exact absurd (r174w_cyc_wrap c1 h) (K2 _)
  refine ⟨D.x₁, D.w₂, D.m₁, rfl, rfl, rfl, Or.inr ⟨rfl, rfl, rfl⟩, hqA, hqB, ?_, hAB, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [D.twin_x₁, D.twin_w₂]; exact hqC'
  · rw [D.twin_m₁]; exact hA1.symm
  · -- P1
    intro a ha h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hA2.symm
    obtain ⟨h2, hZ⟩ := ((Sx1 a).mp h1).resolve_left ha.1
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.x₂)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.m₁)) := by
      rcases r174w_cyc_split h2 c3 (r174w_key_ne ha.2.2.2.2.1) with h' | h'
      · exact h'
      · exact absurd h' (K1 a)
    rw [← hAB]
    exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_right c1 h3, hZ⟩)
  · -- P2
    intro a ha h
    rw [← hqB] at h
    obtain ⟨h2, hx⟩ := ((Sw2 a).mp h).resolve_left ha.2.2.1
    rw [hA3w] at hx
    have hZ := r174w_onZ_of_x₂ D a ha.2.1 hx
    have h3 : cycBetween (geoMarkKey hP (Sum.inr D.m₃)) (geoMarkKey hP a) (geoMarkKey hP (Sum.inr D.w₂)) := by
      rcases r174w_cyc_split h2 c4 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
      · exact absurd h' (K3 a)
      · exact h'
    rw [← hAB]
    exact (Sm1 a).mpr (Or.inr ⟨r174w_cyc_trans_left h3 c2, hZ⟩)
  · -- P3
    intro a ha h
    rw [D.twin_x₁, hqC'] at h
    obtain ⟨h1, hx⟩ := ((Sw3 a).mp h).resolve_left ha.2.2.2.1
    rw [hA3w] at hx
    obtain ⟨h2, hZ⟩ := ((Sx2 a).mp hx).resolve_left ha.2.1
    rcases r174w_cyc_split h2 c5 (r174w_key_ne ha.2.2.2.2.2) with h' | h'
    · rw [hA1]
      exact (Sm3 a).mpr (Or.inr ⟨r174w_cyc_trans_right c8 h', hZ⟩)
    · exfalso
      rcases r174w_cyc_split h' c9 (r174w_key_ne ha.2.2.1) with h'' | h''
      · exact r174w_cyc_asymm h1 (r174w_cyc_trans_right c4 h'')
      · exact K2 a h''
  · -- onZ_A
    intro a h
    have h1 : geoOwner hP (insert x Q) a = geoOwner hP (insert x Q) (Sum.inr D.x₁) :=
      ((r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mp h).trans hA2.symm
    by_cases ha : a = Sum.inr D.x₁
    · rw [ha]; exact r174w_ownerQ_x₁_m₁ D
    · exact r174w_onZ_of_x₁ D a ha h1
  · -- onZ_B
    intro a h
    rw [← hqB] at h
    rcases (Sw2 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₂ D
    · rw [hA3w] at hx
      by_cases ha : a = Sum.inr D.x₂
      · rw [ha]; exact r174w_ownerQ_x₂' D
      · exact r174w_onZ_of_x₂ D a ha hx
  · -- onZ_C'
    intro a h
    rw [D.twin_x₁, hqC'] at h
    rcases (Sw3 a).mp h with rfl | ⟨-, hx⟩
    · exact r174w_ownerQ_w₃ D
    · rw [hA3w] at hx
      by_cases ha : a = Sum.inr D.x₂
      · rw [ha]; exact r174w_ownerQ_x₂' D
      · exact r174w_onZ_of_x₂ D a ha hx
  · -- onZ_AB
    intro a h
    rw [← hAB] at h
    by_cases ha : a = Sum.inr D.m₁
    · rw [ha]
    · exact r174w_onZ_of_m₁ D a ha h
  · -- onZ_C
    intro a h
    rw [hA1] at h
    by_cases ha : a = Sum.inr D.m₃
    · rw [ha]; exact r174w_ownerQ_m₃' D
    · exact r174w_onZ_of_m₃ D a ha h
  · -- triZ
    intro a hZ
    rcases r174w_part_x D a hZ with h | h
    · left; exact (r174w_unaffected_w D (Sum.inr D.m₁) hne_m₁w₂ a).mpr (h.trans hA2)
    · rw [← hA3w] at h
      rcases r174w_part_w D a h with h' | h'
      · right; left; rw [← hqB]; exact h'
      · right; right; rw [D.twin_x₁, hqC']; exact h'

/-- The case analysis: one of the two orientations occurs. -/
theorem r174w_split_exists : Nonempty (r174w_Split D) := by
  rcases GT_succ_of_adjacent hP D.adj1 rfl with h | h
  · exact ⟨r174w_split_caseB D h⟩
  · exact ⟨r174w_split_caseA D h⟩

/-! #### D1. The five carriers and the corner-set decompositions -/

omit [NeZero n] D in
theorem r174w_x_mem_Sxw : x ∈ insert w (insert x Q) := Finset.mem_insert_of_mem (Finset.mem_insert_self x Q)
omit [NeZero n] D in
theorem r174w_w_mem_Sxw : w ∈ insert w (insert x Q) := Finset.mem_insert_self w _
omit [NeZero n] D in
theorem r174w_m_mem_Smi : m ∈ insert m Q := Finset.mem_insert_self m Q

variable (sp : r174w_Split D)

/-- `A`: the carrier of `Q ∪ {x, w}` through `m₁`. -/
abbrev r174w_qA : GeoComponent hP (insert w (insert x Q)) := geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₁)
/-- `B`: the carrier of `Q ∪ {x, w}` through `m₃`. -/
abbrev r174w_qB : GeoComponent hP (insert w (insert x Q)) := geoOwner hP (insert w (insert x Q)) (Sum.inr D.m₃)
/-- `C'`: the carrier of `Q ∪ {x, w}` through the other visit of `x`. -/
abbrev r174w_qCp : GeoComponent hP (insert w (insert x Q)) :=
  geoOwner hP (insert w (insert x Q)) (Sum.inr (visitTwin sp.xA))
/-- `AB`: the carrier of `Q ∪ {m}` through `x₂`. -/
abbrev r174w_qABi : GeoComponent hP (insert m Q) := geoOwner hP (insert m Q) (Sum.inr D.x₂)
/-- `C`: the carrier of `Q ∪ {m}` through `x₁`. -/
abbrev r174w_qCi : GeoComponent hP (insert m Q) := geoOwner hP (insert m Q) (Sum.inr D.x₁)

theorem r174w_qA_ne_qB : r174w_qA D ≠ r174w_qB D := r174w_sep_m_Sxw D

theorem r174w_qA_ne_qCp : r174w_qA D ≠ r174w_qCp D sp := by
  show geoOwner hP _ (Sum.inr D.m₁) ≠ geoOwner hP _ (Sum.inr (visitTwin sp.xA))
  rw [← sp.oA]
  exact geo_selected_visits_separated hP (r174w_Sxw_indep D) sp.xA (by rw [sp.hxA]; exact r174w_x_mem_Sxw)

theorem r174w_qB_ne_qCp : r174w_qB D ≠ r174w_qCp D sp := by
  show geoOwner hP _ (Sum.inr D.m₃) ≠ geoOwner hP _ (Sum.inr (visitTwin sp.xA))
  rw [← sp.oB, sp.oC']
  exact geo_selected_visits_separated hP (r174w_Sxw_indep D) sp.wB (by rw [sp.hwB]; exact r174w_w_mem_Sxw)

theorem r174w_qABi_ne_qCi : r174w_qABi D ≠ r174w_qCi D := (r174w_sep_x_Sm D).symm

theorem r174w_nonspecial_inl (i : ZMod n) : r174w_Nonspecial D (Sum.inl i) :=
  ⟨Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr, Sum.inl_ne_inr⟩

theorem r174w_nonspecial_of_mem_Q (v : Visit P) (hv : v.1 ∈ Q) : r174w_Nonspecial D (Sum.inr v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> obtain rfl := Sum.inr.inj h
  · exact r174w_x_not_mem_Q D hv
  · exact r174w_x_not_mem_Q D hv
  · exact r174w_w_not_mem_Q D hv
  · exact r174w_w_not_mem_Q D hv
  · exact r174w_m_not_mem_Q D hv
  · exact r174w_m_not_mem_Q D hv

/-- For a nonspecial mark, being a corner of `Q ∪ {m}` and of `Q ∪ {x, w}` are the same
(both mean: a vertex, or a visit of a crossing of `Q`). -/
theorem r174w_corner_iff (a : Mark P) (hns : r174w_Nonspecial D a) :
    IsTrueCorner (insert m Q) a ↔ IsTrueCorner (insert w (insert x Q)) a := by
  cases a with
  | inl i => exact iff_of_true trivial trivial
  | inr v =>
    change v.1 ∈ insert m Q ↔ v.1 ∈ insert w (insert x Q)
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert]
    constructor
    · rintro (h | h)
      · exfalso
        rcases D.eq_m₁_or_m₃ h with rfl | rfl
        · exact hns.2.2.2.2.1 rfl
        · exact hns.2.2.2.2.2 rfl
      · exact Or.inr (Or.inr h)
    · rintro (h | h | h)
      · exfalso
        rcases D.eq_w₂_or_w₃ h with rfl | rfl
        · exact hns.2.2.1 rfl
        · exact hns.2.2.2.1 rfl
      · exfalso
        rcases visit_eq_or_twin D.x₁ v h with rfl | h'
        · exact hns.1 rfl
        · rw [D.twin_x₁] at h'
          subst h'
          exact hns.2.1 rfl
      · exact Or.inr h

theorem r174w_not_nonspecial_xA : ¬ r174w_Nonspecial D (Sum.inr sp.xA) := by
  rcases sp.hcase with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> intro hns
  · exact hns.2.1 rfl
  · exact hns.1 rfl
theorem r174w_not_nonspecial_wB : ¬ r174w_Nonspecial D (Sum.inr sp.wB) := by
  rcases sp.hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> intro hns
  · exact hns.2.2.2.1 rfl
  · exact hns.2.2.1 rfl
theorem r174w_not_nonspecial_mAB : ¬ r174w_Nonspecial D (Sum.inr sp.mAB) := by
  rcases sp.hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> intro hns
  · exact hns.2.2.2.2.2 rfl
  · exact hns.2.2.2.2.1 rfl
theorem r174w_not_nonspecial_xC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.xA)) := by
  rcases sp.hcase with ⟨h, -, -⟩ | ⟨h, -, -⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_x₂] at hns; exact hns.1 rfl
  · rw [D.twin_x₁] at hns; exact hns.2.1 rfl
theorem r174w_not_nonspecial_wC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.wB)) := by
  rcases sp.hcase with ⟨-, h, -⟩ | ⟨-, h, -⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_w₃] at hns; exact hns.2.2.1 rfl
  · rw [D.twin_w₂] at hns; exact hns.2.2.2.1 rfl
theorem r174w_not_nonspecial_mC : ¬ r174w_Nonspecial D (Sum.inr (visitTwin sp.mAB)) := by
  rcases sp.hcase with ⟨-, -, h⟩ | ⟨-, -, h⟩ <;> rw [h] <;> intro hns
  · rw [D.twin_m₃] at hns; exact hns.2.2.2.2.1 rfl
  · rw [D.twin_m₁] at hns; exact hns.2.2.2.2.2 rfl

theorem r174w_xC_ne_wC : (Sum.inr (visitTwin sp.xA) : Mark P) ≠ Sum.inr (visitTwin sp.wB) := by
  intro h
  have := congrArg (fun a : Visit P => a.1) (Sum.inr.inj h)
  simp only [visitTwin_crossing, sp.hxA, sp.hwB] at this
  exact D.xw this

theorem r174w_corners_eq_insert_filter {S : Finset (Crossing P)} (q : GeoComponent hP S) (a₀ : Mark P)
    (h₀ : a₀ ∈ r174w_corners hP S q)
    (hothers : ∀ a ∈ r174w_corners hP S q, a ≠ a₀ → r174w_Nonspecial D a) :
    r174w_corners hP S q = insert a₀ ((r174w_corners hP S q).filter (r174w_Nonspecial D)) := by
  ext a
  rw [Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro h
    by_cases ha : a = a₀
    · exact Or.inl ha
    · exact Or.inr ⟨h, hothers a h ha⟩
  · rintro (rfl | ⟨h, -⟩)
    · exact h₀
    · exact h

theorem r174w_corners_eq_insert2_filter {S : Finset (Crossing P)} (q : GeoComponent hP S) (a₀ a₁ : Mark P)
    (h₀ : a₀ ∈ r174w_corners hP S q) (h₁ : a₁ ∈ r174w_corners hP S q)
    (hothers : ∀ a ∈ r174w_corners hP S q, a ≠ a₀ → a ≠ a₁ → r174w_Nonspecial D a) :
    r174w_corners hP S q = insert a₀ (insert a₁ ((r174w_corners hP S q).filter (r174w_Nonspecial D))) := by
  ext a
  rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_filter]
  constructor
  · intro h
    by_cases ha : a = a₀
    · exact Or.inl ha
    by_cases ha' : a = a₁
    · exact Or.inr (Or.inl ha')
    · exact Or.inr (Or.inr ⟨h, hothers a h ha ha'⟩)
  · rintro (rfl | rfl | ⟨h, -⟩)
    · exact h₀
    · exact h₁
    · exact h

/-- The corners of `A`: `xA` and nonspecial corners. -/
theorem r174w_corners_A :
    r174w_corners hP (insert w (insert x Q)) (r174w_qA D) =
      insert (Sum.inr sp.xA) ((r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oA, by change sp.xA.1 ∈ _; rw [sp.hxA]; exact r174w_x_mem_Sxw⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact r174w_qA_ne_qB D (hq.symm.trans sp.oB)
        · exact r174w_qA_ne_qCp D sp (hq.symm.trans sp.oC'.symm)
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qA_ne_qCp D sp hq.symm
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `B`: `wB` and nonspecial corners. -/
theorem r174w_corners_B :
    r174w_corners hP (insert w (insert x Q)) (r174w_qB D) =
      insert (Sum.inr sp.wB) ((r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oB, by change sp.wB.1 ∈ _; rw [sp.hwB]; exact r174w_w_mem_Sxw⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qB_ne_qCp D sp (hq.symm.trans sp.oC'.symm)
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact r174w_qA_ne_qB D (sp.oA.symm.trans hq)
        · exact r174w_qB_ne_qCp D sp hq.symm
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `C'`: the two other local visits and nonspecial corners. -/
theorem r174w_corners_Cp :
    r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp) =
      insert (Sum.inr (visitTwin sp.xA)) (insert (Sum.inr (visitTwin sp.wB))
        ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))) := by
  apply r174w_corners_eq_insert2_filter
  · rw [r174w_mem_corners]
    exact ⟨rfl, by change (visitTwin sp.xA).1 ∈ _; rw [visitTwin_crossing, sp.hxA]; exact r174w_x_mem_Sxw⟩
  · rw [r174w_mem_corners]
    exact ⟨sp.oC'.symm, by change (visitTwin sp.wB).1 ∈ _; rw [visitTwin_crossing, sp.hwB]; exact r174w_w_mem_Sxw⟩
  · intro a ha hne1 hne2
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert w (insert x Q) := hc
      rw [Finset.mem_insert, Finset.mem_insert] at hv
      rcases hv with hv | hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.wB v (hv.trans sp.hwB.symm) with rfl | rfl
        · exact r174w_qB_ne_qCp D sp (sp.oB.symm.trans hq)
        · exact hne2 rfl
      · exfalso
        rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
        · exact r174w_qA_ne_qCp D sp (sp.oA.symm.trans hq)
        · exact hne1 rfl
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `AB`: `mAB` and nonspecial corners. -/
theorem r174w_corners_AB :
    r174w_corners hP (insert m Q) (r174w_qABi D) =
      insert (Sum.inr sp.mAB) ((r174w_corners hP (insert m Q) (r174w_qABi D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oAB, by change sp.mAB.1 ∈ _; rw [sp.hmAB]; exact r174w_m_mem_Smi⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert m Q := hc
      rw [Finset.mem_insert] at hv
      rcases hv with hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.mAB v (hv.trans sp.hmAB.symm) with rfl | rfl
        · exact hne rfl
        · exact r174w_qABi_ne_qCi D (hq.symm.trans sp.oC)
      · exact r174w_nonspecial_of_mem_Q D v hv

/-- The corners of `C`: the other visit of `m` and nonspecial corners. -/
theorem r174w_corners_C :
    r174w_corners hP (insert m Q) (r174w_qCi D) =
      insert (Sum.inr (visitTwin sp.mAB)) ((r174w_corners hP (insert m Q) (r174w_qCi D)).filter (r174w_Nonspecial D)) := by
  apply r174w_corners_eq_insert_filter
  · rw [r174w_mem_corners]
    exact ⟨sp.oC, by change (visitTwin sp.mAB).1 ∈ _; rw [visitTwin_crossing, sp.hmAB]; exact r174w_m_mem_Smi⟩
  · intro a ha hne
    rw [r174w_mem_corners] at ha
    obtain ⟨hq, hc⟩ := ha
    cases a with
    | inl i => exact r174w_nonspecial_inl D i
    | inr v =>
      have hv : v.1 ∈ insert m Q := hc
      rw [Finset.mem_insert] at hv
      rcases hv with hv | hv
      · exfalso
        rcases visit_eq_or_twin sp.mAB v (hv.trans sp.hmAB.symm) with rfl | rfl
        · exact r174w_qABi_ne_qCi D (sp.oAB.symm.trans hq)
        · exact hne rfl
      · exact r174w_nonspecial_of_mem_Q D v hv

include sp in
/-- **The nonspecial corners of `AB` are those of `A` and `B`.** -/
theorem r174w_reg_AB :
    (r174w_corners hP (insert m Q) (r174w_qABi D)).filter (r174w_Nonspecial D) =
      (r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D) ∪
        (r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D) := by
  ext a
  simp only [Finset.mem_union, Finset.mem_filter, r174w_mem_corners]
  constructor
  · rintro ⟨⟨h1, hc⟩, hns⟩
    have hc' := (r174w_corner_iff D a hns).mp hc
    rcases sp.triZ a (sp.onZ_AB a h1) with hA | hB | hC
    · exact Or.inl ⟨⟨hA, hc'⟩, hns⟩
    · exact Or.inr ⟨⟨hB, hc'⟩, hns⟩
    · exact absurd (h1.symm.trans (sp.P3 a hns hC)) (r174w_qABi_ne_qCi D)
  · rintro (⟨⟨hA, hc'⟩, hns⟩ | ⟨⟨hB, hc'⟩, hns⟩)
    · exact ⟨⟨sp.P1 a hns hA, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩
    · exact ⟨⟨sp.P2 a hns hB, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩

theorem r174w_reg_disj :
    Disjoint ((r174w_corners hP (insert w (insert x Q)) (r174w_qA D)).filter (r174w_Nonspecial D))
      ((r174w_corners hP (insert w (insert x Q)) (r174w_qB D)).filter (r174w_Nonspecial D)) := by
  rw [Finset.disjoint_left]
  intro a ha hb
  rw [Finset.mem_filter, r174w_mem_corners] at ha hb
  exact r174w_qA_ne_qB D (ha.1.1.symm.trans hb.1.1)

/-- **The nonspecial corners of `C` are those of `C'`.** -/
theorem r174w_reg_C :
    (r174w_corners hP (insert m Q) (r174w_qCi D)).filter (r174w_Nonspecial D) =
      (r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D) := by
  ext a
  simp only [Finset.mem_filter, r174w_mem_corners]
  constructor
  · rintro ⟨⟨h1, hc⟩, hns⟩
    have hc' := (r174w_corner_iff D a hns).mp hc
    rcases sp.triZ a (sp.onZ_C a h1) with hA | hB | hC
    · exact absurd ((sp.P1 a hns hA).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact absurd ((sp.P2 a hns hB).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact ⟨⟨hC, hc'⟩, hns⟩
  · rintro ⟨⟨hC, hc'⟩, hns⟩
    exact ⟨⟨sp.P3 a hns hC, (r174w_corner_iff D a hns).mpr hc'⟩, hns⟩

theorem r174w_not_mem_filter {C : Finset (Mark P)} {a : Mark P} (h : ¬ r174w_Nonspecial D a) :
    a ∉ C.filter (r174w_Nonspecial D) := fun h' => h (Finset.mem_filter.mp h').2

/-! #### D3. The turn signs and principal turns at the six local corners (the sign condition) -/

/-- The two angle identities of the triangle of directions `u₁, u₂, u₃` under the canonical sign
condition: `∠(u₁,u₂) + ∠(u₂,u₃) = ∠(u₁,u₃)` and `∠(u₂,u₁) + ∠(u₃,u₂) = ∠(u₃,u₁)`. -/
theorem r174w_angle_identities (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    principalAngle (edge P ℓ₁) (edge P ℓ₂) + principalAngle (edge P ℓ₂) (edge P ℓ₃) =
        principalAngle (edge P ℓ₁) (edge P ℓ₃) ∧
    principalAngle (edge P ℓ₂) (edge P ℓ₁) + principalAngle (edge P ℓ₃) (edge P ℓ₂) =
        principalAngle (edge P ℓ₃) (edge P ℓ₁) := by
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  have hne : det (edge P ℓ₁) (edge P ℓ₃) ≠ 0 := crossing_det_ne_zero_of_geometry hP hm
  have h1 := hsgn
  have h2 := D.sgn
  unfold crossingSign at h1 h2
  rcases lt_or_gt_of_ne hne with hneg | hpos
  · have s13 := sign_eq_neg_one_iff.mpr hneg
    have s12 : det (edge P ℓ₁) (edge P ℓ₂) < 0 := sign_eq_neg_one_iff.mp (h1.trans s13)
    have s23 : det (edge P ℓ₂) (edge P ℓ₃) < 0 := sign_eq_neg_one_iff.mp (h2.trans s13)
    refine ⟨r174w_angle_add_of_neg s12 hneg s23, ?_⟩
    have := r174w_angle_add_of_pos (u₁ := edge P ℓ₃) (u₂ := edge P ℓ₂) (u₃ := edge P ℓ₁)
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    rw [add_comm]; exact this
  · have s13 := sign_eq_one_iff.mpr hpos
    have s12 : 0 < det (edge P ℓ₁) (edge P ℓ₂) := sign_eq_one_iff.mp (h1.trans s13)
    have s23 : 0 < det (edge P ℓ₂) (edge P ℓ₃) := sign_eq_one_iff.mp (h2.trans s13)
    refine ⟨r174w_angle_add_of_pos s12 hpos s23, ?_⟩
    have := r174w_angle_add_of_neg (u₁ := edge P ℓ₃) (u₂ := edge P ℓ₂) (u₃ := edge P ℓ₁)
      (by rw [det_swap]; linarith) (by rw [det_swap]; linarith) (by rw [det_swap]; linarith)
    rw [add_comm]; exact this

theorem r174w_sign13_ne_zero : crossingSign P ℓ₁ ℓ₃ ≠ 0 := by
  have hm : IsCrossing P {ℓ₁, ℓ₃} := by rw [← D.mval]; exact m.property
  unfold crossingSign
  exact sign_ne_zero.mpr (crossing_det_ne_zero_of_geometry hP hm)

/-- **The turn data at the six local corners**: the corners of `A`, `B`, `AB` turn the same way `τ`,
the corners of `C'`, `C` turn the opposite way, and the principal turns add. -/
theorem r174w_turn_data (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    r174w_tau P (Sum.inr sp.xA) = r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr sp.wB) = r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.mAB)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.xA)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr (visitTwin sp.wB)) = -r174w_tau P (Sum.inr sp.mAB) ∧
    r174w_tau P (Sum.inr sp.mAB) ≠ 0 ∧
    r174w_theta P (Sum.inr sp.xA) + r174w_theta P (Sum.inr sp.wB) = r174w_theta P (Sum.inr sp.mAB) ∧
    r174w_theta P (Sum.inr (visitTwin sp.xA)) + r174w_theta P (Sum.inr (visitTwin sp.wB)) =
      r174w_theta P (Sum.inr (visitTwin sp.mAB)) := by
  obtain ⟨I1, I2⟩ := r174w_angle_identities D hsgn
  have hs13 := r174w_sign13_ne_zero D
  have h23 := D.sgn
  rcases sp.hcase with ⟨h1, h2, h3⟩ | ⟨h1, h2, h3⟩
  · rw [h1, h2, h3, D.twin_x₂, D.twin_w₃, D.twin_m₃]
    simp only [r174w_tau_visit, r174w_theta_visit]
    rw [D.twin_x₁, D.twin_x₂, D.twin_w₂, D.twin_w₃, D.twin_m₁, D.twin_m₃]
    simp only [D.x₁_edge, D.x₂_edge, D.w₂_edge, D.w₃_edge, D.m₁_edge, D.m₃_edge]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [crossingSign_swap P ℓ₁ ℓ₂, crossingSign_swap P ℓ₁ ℓ₃, hsgn]
    · rw [crossingSign_swap P ℓ₂ ℓ₃, crossingSign_swap P ℓ₁ ℓ₃, h23]
    · rw [crossingSign_swap P ℓ₃ ℓ₁]
    · rw [hsgn, crossingSign_swap P ℓ₃ ℓ₁]
    · rw [h23, crossingSign_swap P ℓ₃ ℓ₁]
    · rw [crossingSign_swap P ℓ₁ ℓ₃]
      revert hs13
      cases crossingSign P ℓ₁ ℓ₃ <;> decide
    · exact I2
    · exact I1
  · rw [h1, h2, h3, D.twin_x₁, D.twin_w₂, D.twin_m₁]
    simp only [r174w_tau_visit, r174w_theta_visit]
    rw [D.twin_x₁, D.twin_x₂, D.twin_w₂, D.twin_w₃, D.twin_m₁, D.twin_m₃]
    simp only [D.x₁_edge, D.x₂_edge, D.w₂_edge, D.w₃_edge, D.m₁_edge, D.m₃_edge]
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact hsgn
    · exact h23
    · rw [crossingSign_swap P ℓ₁ ℓ₃]
    · rw [crossingSign_swap P ℓ₁ ℓ₂, hsgn]
    · rw [crossingSign_swap P ℓ₂ ℓ₃, h23]
    · exact hs13
    · exact I1
    · exact I2

/-! #### D4. The selector and rotation identities on the `insert` supports, exported through a
support equation (so that the ledger's `Q ∪ {m}`, `Q ∪ {x, w}` can be substituted) -/

omit D in
theorem r174w_signType_cast_neg (s : SignType) : ((-s : SignType) : ℤ) = -((s : SignType) : ℤ) := by
  cases s <;> rfl

/-- `wt(A) wt(B) = −τ wt(AB)` with `τ` the common turn of the three smoothing corners. -/
theorem r174w_weight_AB_of_split (hn : 3 ≤ n) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q)) :
    CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr D.m₁)) * CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr D.m₃)) =
      -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) * CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₂)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨hta, htb, -, -, -, hτ, -, -⟩ := r174w_turn_data D sp hsgn
  rw [r174w_weight_eq hn hP (r174w_Sxw_indep D), r174w_weight_eq hn hP (r174w_Sxw_indep D),
    r174w_weight_eq hn hP (r174w_Sm_indep D)]
  rw [r174w_corners_A D sp, r174w_corners_B D sp, r174w_corners_AB D sp, r174w_reg_AB D sp]
  exact r174w_F_split _ _ (r174w_reg_disj D) _ _ _ (r174w_not_mem_filter D (r174w_not_nonspecial_xA D sp))
    (r174w_not_mem_filter D (r174w_not_nonspecial_wB D sp))
    (by rw [← r174w_reg_AB D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mAB D sp))
    _ hτ hta htb rfl

/-- `wt(C') = −τ' wt(C)` with `τ' = −τ` the common turn of the smoothing corners of `C`, `C'`. -/
theorem r174w_weight_C_of_split (hn : 3 ≤ n) (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q)) :
    CV.weight hP Sxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      ((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) * CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨-, -, htc, hta, htb, hτ, -, -⟩ := r174w_turn_data D sp hsgn
  rw [r174w_weight_eq hn hP (r174w_Sxw_indep D), r174w_weight_eq hn hP (r174w_Sm_indep D)]
  rw [r174w_corners_Cp D sp, r174w_corners_C D sp, r174w_reg_C D sp]
  have hτ' : -r174w_tau P (Sum.inr sp.mAB) ≠ 0 := by
    intro h; apply hτ
    have := congrArg (fun t : SignType => -t) h
    simpa using this
  have key := r174w_F_two ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))
    (Sum.inr (visitTwin sp.xA)) (Sum.inr (visitTwin sp.wB)) (Sum.inr (visitTwin sp.mAB))
    (by
      rw [Finset.mem_insert, not_or]
      exact ⟨r174w_xC_ne_wC D sp, r174w_not_mem_filter D (r174w_not_nonspecial_xC D sp)⟩)
    (r174w_not_mem_filter D (r174w_not_nonspecial_wC D sp))
    (by rw [← r174w_reg_C D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mC D sp))
    _ hτ' hta htb htc
  rw [key, r174w_signType_cast_neg, neg_neg]

include sp in
/-- `R(AB) = R(A) + R(B)` under `wt(AB) ≠ 0`. -/
theorem r174w_carrierR_add_of_split (hn : 3 ≤ n) (hG : CV.Generic P)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q))
    (hSm : Sm ∈ CV.Ind hG.crossingGeometry) (hSxw : Sxw ∈ CV.Ind hG.crossingGeometry)
    (hw : CV.weight hP Sm (geoOwner hP Sm (Sum.inr D.x₂)) ≠ 0) :
    CV.carrierR hn hG hSm (geoOwner hP Sm (Sum.inr D.x₂)) =
      CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr D.m₁)) +
        CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr D.m₃)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨hta, htb, -, -, -, -, hθ, -⟩ := r174w_turn_data D sp hsgn
  exact r174w_carrierR_add_of hn hG hSm hSxw _ _ _ _ _ (r174w_reg_disj D) _ _ _
    (r174w_not_mem_filter D (r174w_not_nonspecial_xA D sp))
    (r174w_not_mem_filter D (r174w_not_nonspecial_wB D sp))
    (by rw [← r174w_reg_AB D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mAB D sp))
    (r174w_corners_A D sp) (r174w_corners_B D sp)
    (by rw [r174w_corners_AB D sp, r174w_reg_AB D sp]) hθ hta htb hw

/-- `rot(C') = rot(C)`, hence `R(C') = R(C)`. -/
theorem r174w_carrierR_C_of_split (hn : 3 ≤ n) (hG : CV.Generic P)
    (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) (hSxw_eq : Sxw = insert w (insert x Q))
    (hSm : Sm ∈ CV.Ind hG.crossingGeometry) (hSxw : Sxw ∈ CV.Ind hG.crossingGeometry) :
    CV.carrierR hn hG hSxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      CV.carrierR hn hG hSm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  obtain ⟨-, -, -, -, -, -, -, hθ⟩ := r174w_turn_data D sp hsgn
  unfold CV.carrierR CV.rotAbs
  rw [r174w_rot_eq_two hn hG hSm hSxw _ _
    ((r174w_corners hP (insert w (insert x Q)) (r174w_qCp D sp)).filter (r174w_Nonspecial D))
    (Sum.inr (visitTwin sp.xA)) (Sum.inr (visitTwin sp.wB)) (Sum.inr (visitTwin sp.mAB))
    (by
      rw [Finset.mem_insert, not_or]
      exact ⟨r174w_xC_ne_wC D sp, r174w_not_mem_filter D (r174w_not_nonspecial_xC D sp)⟩)
    (r174w_not_mem_filter D (r174w_not_nonspecial_wC D sp))
    (by rw [← r174w_reg_C D sp]; exact r174w_not_mem_filter D (r174w_not_nonspecial_mC D sp))
    (r174w_corners_Cp D sp) (by rw [r174w_corners_C D sp, r174w_reg_C D sp]) hθ]

/-- The carrier `C'` is the one carrying a visit of `x` and a visit of `w` (uniqueness). -/
theorem r174w_qCp_unique (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q))
    (q' : GeoComponent hP Sxw) (v u : Visit P) (hv : v.1 = x) (hu : u.1 = w)
    (h1 : geoOwner hP Sxw (Sum.inr v) = q') (h2 : geoOwner hP Sxw (Sum.inr u) = q') :
    q' = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq
  rcases visit_eq_or_twin sp.xA v (hv.trans sp.hxA.symm) with rfl | rfl
  · exfalso
    rcases visit_eq_or_twin sp.wB u (hu.trans sp.hwB.symm) with rfl | rfl
    · exact r174w_qA_ne_qB D ((sp.oA.symm.trans h1).trans (h2.symm.trans sp.oB))
    · exact r174w_qA_ne_qCp D sp ((sp.oA.symm.trans h1).trans (h2.symm.trans sp.oC'.symm))
  · exact h1.symm

theorem r174w_qCp_owns (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    ∃ v u : Visit P, v.1 = x ∧ u.1 = w ∧
      geoOwner hP Sxw (Sum.inr v) = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) ∧
      geoOwner hP Sxw (Sum.inr u) = geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq
  exact ⟨visitTwin sp.xA, visitTwin sp.wB, by rw [visitTwin_crossing, sp.hxA], by rw [visitTwin_crossing, sp.hwB],
    rfl, sp.oC'.symm⟩

theorem r174w_qA_ne_qCp_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₁) ≠ geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq; exact r174w_qA_ne_qCp D sp
theorem r174w_qB_ne_qCp_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₃) ≠ geoOwner hP Sxw (Sum.inr (visitTwin sp.xA)) := by
  subst hSxw_eq; exact r174w_qB_ne_qCp D sp
theorem r174w_qA_ne_qB_export (Sxw : Finset (Crossing P)) (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoOwner hP Sxw (Sum.inr D.m₁) ≠ geoOwner hP Sxw (Sum.inr D.m₃) := by
  subst hSxw_eq; exact r174w_qA_ne_qB D
theorem r174w_qAB_ne_qC_export (Sm : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) :
    geoOwner hP Sm (Sum.inr D.x₂) ≠ geoOwner hP Sm (Sum.inr D.x₁) := by
  subst hSm_eq; exact r174w_qABi_ne_qCi D

/-- The visit of `m` carried by `AB`, and the one carried by `C`. -/
theorem r174w_mAB_export (Sm : Finset (Crossing P)) (hSm_eq : Sm = insert m Q) :
    geoOwner hP Sm (Sum.inr sp.mAB) = geoOwner hP Sm (Sum.inr D.x₂) ∧
    geoOwner hP Sm (Sum.inr (visitTwin sp.mAB)) = geoOwner hP Sm (Sum.inr D.x₁) := by
  subst hSm_eq; exact ⟨sp.oAB, sp.oC⟩

/-- The canonical sign as the ledger needs it: `σ = −τ(mAB)`, with `σ = crossingSign ℓ₁ ℓ₂` exactly when
`AB` carries `m₃` (the printed orientation) and `σ = −crossingSign ℓ₁ ℓ₂` when it carries `m₁`. -/
theorem r174w_sigma_cases (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (sp.mAB = D.m₃ ∧ -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) = ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) ∨
    (sp.mAB = D.m₁ ∧ -((r174w_tau P (Sum.inr sp.mAB) : SignType) : ℤ) = -((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) := by
  rcases sp.hcase with ⟨-, -, h3⟩ | ⟨-, -, h3⟩
  · left
    refine ⟨h3, ?_⟩
    rw [h3, r174w_tau_visit, D.twin_m₃, D.m₃_edge, D.m₁_edge, crossingSign_swap P ℓ₁ ℓ₃,
      r174w_signType_cast_neg, neg_neg, hsgn]
  · right
    refine ⟨h3, ?_⟩
    rw [h3, r174w_tau_visit, D.twin_m₁, D.m₁_edge, D.m₃_edge, hsgn]

/-! #### D5. `C` and `C'` retain the same crossings -/

theorem r174w_nonspecial_of_outside (v : Visit P) (hx : v.1 ≠ x) (hw : v.1 ≠ w) (hm : v.1 ≠ m) :
    r174w_Nonspecial D (Sum.inr v) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> intro h <;> obtain rfl := Sum.inr.inj h
  · exact hx rfl
  · exact hx rfl
  · exact hw rfl
  · exact hw rfl
  · exact hm rfl
  · exact hm rfl

/-- For a nonspecial mark: on `C'` iff on `C`. -/
theorem r174w_owner_C_iff (a : Mark P) (hns : r174w_Nonspecial D a) :
    geoOwner hP (insert w (insert x Q)) a = r174w_qCp D sp ↔ geoOwner hP (insert m Q) a = r174w_qCi D := by
  constructor
  · intro h; exact sp.P3 a hns h
  · intro h1
    rcases sp.triZ a (sp.onZ_C a h1) with hA | hB | hC
    · exact absurd ((sp.P1 a hns hA).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact absurd ((sp.P2 a hns hB).symm.trans h1) (r174w_qABi_ne_qCi D)
    · exact hC

/-- **`C` and `C'` have the same retained crossings.** -/
theorem r174w_retained_C_eq :
    geoCarrierCrossings hP (insert w (insert x Q)) (r174w_qCp D sp) =
      geoCarrierCrossings hP (insert m Q) (r174w_qCi D) := by
  ext c
  rw [mem_geoCarrierCrossings, mem_geoCarrierCrossings]
  by_cases hcQ : c ∈ Q
  · exact iff_of_false (fun h => h.1 (Finset.mem_insert_of_mem (Finset.mem_insert_of_mem hcQ)))
      (fun h => h.1 (Finset.mem_insert_of_mem hcQ))
  by_cases hcx : c = x
  · subst hcx
    exact iff_of_false (fun h => h.1 r174w_x_mem_Sxw)
      (fun h => r174w_qABi_ne_qCi D (h.2 D.x₂ rfl))
  by_cases hcw : c = w
  · subst hcw
    refine iff_of_false (fun h => h.1 r174w_w_mem_Sxw) (fun h => r174w_qABi_ne_qCi D ?_)
    have := h.2 D.w₂ rfl
    rw [← r174w_ownerm_x₂_w₂ D] at this
    exact this
  by_cases hcm : c = m
  · subst hcm
    exact iff_of_false (fun h => r174w_qA_ne_qCp D sp (h.2 D.m₁ rfl)) (fun h => h.1 r174w_m_mem_Smi)
  have hcSxw : c ∉ insert w (insert x Q) := by
    rw [Finset.mem_insert, Finset.mem_insert]; tauto
  have hcSm : c ∉ insert m Q := by
    rw [Finset.mem_insert]; tauto
  refine iff_of_eq (congrArg₂ And (propext (iff_of_true hcSxw hcSm)) ?_)
  apply propext
  constructor
  · intro h v hv
    exact (r174w_owner_C_iff D sp (Sum.inr v) (r174w_nonspecial_of_outside D v (hv ▸ hcx) (hv ▸ hcw) (hv ▸ hcm))).mp (h v hv)
  · intro h v hv
    exact (r174w_owner_C_iff D sp (Sum.inr v) (r174w_nonspecial_of_outside D v (hv ▸ hcx) (hv ▸ hcw) (hv ▸ hcm))).mpr (h v hv)

theorem r174w_retained_C_export (Sm Sxw : Finset (Crossing P)) (hSm_eq : Sm = insert m Q)
    (hSxw_eq : Sxw = insert w (insert x Q)) :
    geoCarrierCrossings hP Sxw (geoOwner hP Sxw (Sum.inr (visitTwin sp.xA))) =
      geoCarrierCrossings hP Sm (geoOwner hP Sm (Sum.inr D.x₁)) := by
  subst hSm_eq hSxw_eq
  exact r174w_retained_C_eq D sp

end R174W_Config

/-! ### D6. The ledger fields `weight_C`, `weight_AB`, `carrierR_add` (and `hσ`) on the ledger's own
supports `Q ∪ {m}`, `Q ∪ {x, w}` -/

section R174W_Ledger

variable {n : ℕ} [NeZero n] {P P' : LabelledTuple n} (hn : 3 ≤ n) (hG : CV.Generic P) (hG' : CV.Generic P')
  {hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s} {e f g : ZMod n} {Q : Finset (Crossing P)}
  {x w m : Crossing P} {ℓ₁ ℓ₂ ℓ₃ : ZMod n}
  (D : GT_Endpoint hG.crossingGeometry hG'.crossingGeometry hs e f g Q x w m ℓ₁ ℓ₂ ℓ₃)

/-- A fixed outcome of the orientation case analysis. -/
noncomputable def r174w_sp : r174w_Split D := Classical.choice (r174w_split_exists D)

/-- **The canonical sign `σ` of the ledger**: minus the common turn of the smoothing corners of `A`, `B`,
`AB` (`= crossingSign ℓ₁ ℓ₂` in the printed orientation, its negative in the reversed one). -/
noncomputable def r174w_sigma : ℤ := -((r174w_tau P (Sum.inr (r174w_sp hG hG' D).mAB) : SignType) : ℤ)

/-- The carrier `C'` of the pair row: through the visit of `x` not carried by `A`. -/
noncomputable abbrev r174w_qC' : GeoComponent hG.crossingGeometry (Q ∪ {x, w}) :=
  geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr (visitTwin (r174w_sp hG hG' D).xA))

/-- **`hσ`**: `σ = ±1`. -/
theorem r174w_hsigma (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    r174w_sigma hG hG' D = 1 ∨ r174w_sigma hG hG' D = -1 := by
  obtain ⟨-, -, -, -, -, hτ, -, -⟩ := r174w_turn_data D (r174w_sp hG hG' D) hsgn
  unfold r174w_sigma
  revert hτ
  cases r174w_tau P (Sum.inr (r174w_sp hG hG' D).mAB) <;> decide

include hn in
/-- **`weight_AB` (GSC (5))**: `wt(A) wt(B) = σ wt(AB)` for `qAB` the carrier of `x₂` in the centre row and
`qA, qB` the carriers of `m₁, m₃` in the pair row. -/
theorem r174w_weight_AB (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : qAB = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂))
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hqA : qA = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁))
    (hqB : qB = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃)) :
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) qA * CV.weight hG.crossingGeometry (Q ∪ {x, w}) qB =
      r174w_sigma hG hG' D * CV.weight hG.crossingGeometry (Q ∪ {m}) qAB := by
  subst hqAB hqA hqB
  exact r174w_weight_AB_of_split D (r174w_sp hG hG' D) hn hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

include hn in
/-- **`weight_C` (GSC (5))**: `wt(C') = −σ wt(C)` for `qC` the carrier of `x₁` in the centre row. -/
theorem r174w_weight_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.weight hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) =
      -r174w_sigma hG hG' D * CV.weight hG.crossingGeometry (Q ∪ {m}) qC := by
  subst hqC
  unfold r174w_sigma
  rw [neg_neg]
  exact r174w_weight_C_of_split D (r174w_sp hG hG' D) hn hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- **`carrierR_add` (GSC (8))**: `R(AB) = R(A) + R(B)` under `wt(AB) ≠ 0`. -/
theorem r174w_carrierR_add (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qAB : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqAB : qAB = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂))
    (qA qB : GeoComponent hG.crossingGeometry (Q ∪ {x, w}))
    (hqA : qA = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁))
    (hqB : qB = geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃)) :
    CV.weight hG.crossingGeometry (Q ∪ {m}) qAB ≠ 0 →
      CV.carrierR hn hG hSm qAB = CV.carrierR hn hG hSxw qA + CV.carrierR hn hG hSxw qB := by
  subst hqAB hqA hqB
  exact r174w_carrierR_add_of_split D (r174w_sp hG hG' D) hn hG hsgn (Q ∪ {m}) (Q ∪ {x, w})
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) hSm hSxw

/-- `R(C') = R(C)`. -/
theorem r174w_carrierR_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.carrierR hn hG hSxw (r174w_qC' hG hG' D) = CV.carrierR hn hG hSm qC := by
  subst hqC
  exact r174w_carrierR_C_of_split D (r174w_sp hG hG' D) hn hG hsgn (Q ∪ {m}) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) hSm hSxw

/-- Characterisation of `qC'` for the assembler: it is the carrier of the pair row carrying a visit of `x`
and a visit of `w`, and any such carrier is `qC'`. -/
theorem r174w_qC'_owns :
    ∃ v u : Visit P, v.1 = x ∧ u.1 = w ∧
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = r174w_qC' hG hG' D ∧
      geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr u) = r174w_qC' hG hG' D :=
  r174w_qCp_owns D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

theorem r174w_qC'_unique (q' : GeoComponent hG.crossingGeometry (Q ∪ {x, w})) (v u : Visit P)
    (hv : v.1 = x) (hu : u.1 = w)
    (h1 : geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr v) = q')
    (h2 : geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr u) = q') : q' = r174w_qC' hG hG' D :=
  r174w_qCp_unique D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto) q' v u hv hu h1 h2

theorem r174w_qA_ne_qC' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁) ≠ r174w_qC' hG hG' D :=
  r174w_qA_ne_qCp_export D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qB_ne_qC' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃) ≠ r174w_qC' hG hG' D :=
  r174w_qB_ne_qCp_export D (r174w_sp hG hG' D) (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qA_ne_qB' :
    geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₁) ≠ geoOwner hG.crossingGeometry (Q ∪ {x, w}) (Sum.inr D.m₃) :=
  r174w_qA_ne_qB_export D (Q ∪ {x, w}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
theorem r174w_qAB_ne_qC :
    geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ≠ geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁) :=
  r174w_qAB_ne_qC_export D (Q ∪ {m}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- `σ` against `crossingSign ℓ₁ ℓ₂`: equal in the printed orientation (`AB ∋ m₃`), negated in the other. -/
theorem r174w_sigma_vs_crossingSign (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃) :
    (geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.m₃) = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ∧
        r174w_sigma hG hG' D = ((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) ∨
    (geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.m₁) = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₂) ∧
        r174w_sigma hG hG' D = -((crossingSign P ℓ₁ ℓ₂ : SignType) : ℤ)) := by
  have hm := (r174w_mAB_export D (r174w_sp hG hG' D) (Q ∪ {m}) (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)).1
  rcases r174w_sigma_cases D (r174w_sp hG hG' D) hsgn with ⟨h3, hσ⟩ | ⟨h3, hσ⟩
  · left; rw [h3] at hm; exact ⟨hm, hσ⟩
  · right; rw [h3] at hm; exact ⟨hm, hσ⟩

/-- **`C` and `C'` retain the same crossings** (ledger supports). -/
theorem r174w_retained_C (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) =
      geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC := by
  subst hqC
  exact r174w_retained_C_export D (r174w_sp hG hG' D) (Q ∪ {m}) (Q ∪ {x, w})
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)
    (by ext c; simp only [Finset.mem_union, Finset.mem_singleton, Finset.mem_insert]; tauto)

/-- **The grouped polynomials of `C` and `C'` agree**: same retained crossings on the same polygon, so
the two positive lifts have isomorphic records (`GT_homfly_wall_gen` with the identity on visits). -/
theorem r174w_groupedPoly_C (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry)
    (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.groupedPoly hn hG hSxw (r174w_qC' hG hG' D) = CV.groupedPoly hn hG hSm qC := by
  have hX := r174w_retained_C hG hG' D qC hqC
  have hX' : ∀ v : Visit P, v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC ↔
      v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D) := fun v => by rw [hX]
  -- the identity on visits, with its value equation kept explicit: the kernel must never be asked to
  -- compare `Subtype.val` terms over the two different retained sets by unfolding
  obtain ⟨ψ, hψ'⟩ : ∃ ψ : {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {m}) qC} ≃
      {v : Visit P // v.1 ∈ geoCarrierCrossings hG.crossingGeometry (Q ∪ {x, w}) (r174w_qC' hG hG' D)},
      ∀ z, ψ z = ⟨z.1, (hX' z.1).mp z.2⟩ := ⟨Equiv.subtypeEquivRight hX', fun z => rfl⟩
  have e : ∀ z, (ψ z).1 = z.1 := fun z => (congrArg Subtype.val (hψ' z)).trans (Subtype.coe_mk z.1 _)
  rw [GT_groupedPoly_eq_homfly, GT_groupedPoly_eq_homfly]
  unfold CV.carrierDiagram
  refine GT_homfly_wall_gen hn _ _ _ _ qC (r174w_qC' hG hG' D) ψ ?_ ?_ ?_
  · intro v hv; rw [e, e]
  · intro u v w h; rw [e, e, e]; exact h
  · intro v; rw [e]

/-- **`omega_C`**: `Ω₁(C') = Ω₁(C)` (same retained record, writhe, rotation, slot, read). -/
theorem r174w_omega_C (hsgn : crossingSign P ℓ₁ ℓ₂ = crossingSign P ℓ₁ ℓ₃)
    (hSm : Q ∪ {m} ∈ CV.Ind hG.crossingGeometry) (hSxw : Q ∪ {x, w} ∈ CV.Ind hG.crossingGeometry)
    (qC : GeoComponent hG.crossingGeometry (Q ∪ {m}))
    (hqC : qC = geoOwner hG.crossingGeometry (Q ∪ {m}) (Sum.inr D.x₁)) :
    CV.Omega1 hn hG hSxw (r174w_qC' hG hG' D) = CV.Omega1 hn hG hSm qC := by
  unfold CV.Omega1 CV.slot
  rw [CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSxw, CV.groupedWrithe_eq_card_geoCarrierCrossings hG hSm,
    r174w_retained_C hG hG' D qC hqC, r174w_carrierR_C hn hG hG' D hsgn hSm hSxw qC hqC,
    r174w_groupedPoly_C hn hG hG' D hSm hSxw qC hqC]

end R174W_Ledger

end

end SM.Link
