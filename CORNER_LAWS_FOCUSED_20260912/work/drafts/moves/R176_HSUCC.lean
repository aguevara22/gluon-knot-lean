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


/-! # Site_176 — row 176 (R:extreme_transport), the `j`-corner bigon site of `carrierDiagram q₀'` switched at `y`

APPENDED by the I-176 prover, 2026-09-15, to `Skeleton_W1.lean` (byte-identical above this line except the
added `import RProof.RALedgers`).  Companion report: `Site_176_REPORT.md`.  All names carry the prefix
`s176_`; nothing above is modified; the frozen leaves (`exists_bigonData_of_triangle`, …) are used as black
boxes.  Sections: §A the abstract `j`-corner site on a positive diagram and its `BigonData` through the frozen
leaf (`same_over` PROVED from the corner identity, `hk` from genericity); §B the row-176 ledger re-based on the
weak port (F-176-1: `s176_PortDataWeak`, `s176_est_omega1_eq_of_port_weak`, `s176_est_port_relation_weak`,
`s176_est_ledger_weak`); §C the carrier-level realisation of the site (`s176_cornerSite_of_carrier`, PROVED:
the corner structure `s176_corner_case1`, the cyclicity `s176_cyclic`, the closed-triangle clearance
`s176_clear_case1`); §D the event-level site in the binders of `est_port_relation` (`s176_site_of_event`,
PROVED); §E the record identification `hrec` (`s176_hrec_of_site`, STATED) and the compositions
(`s176_port_weak_of_event`, `s176_est_port_relation_weak_of`); §F the switch drops out of `hrec`
(`s176_switchRestrictIso`, PROVED); §G the wall occurrence bijection `s176_wallΦ` and the `RecordIso` modulo the
successor clause (`s176_hrec_unswitched_of_succ`, PROVED); §H the event-level wall data and the closure of the
chain: `s176_hrec_wall_of_succ`, `s176_site_of_event'`, `s176_port_weak_of_event'`,
`s176_est_port_relation_weak_of'` — the ONE remaining obligation of the move is the successor clause `hsucc`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

/-! ## §A. The abstract `j`-corner site (row 176, PLAN_FINAL §4.3) -/

/-- **The `j`-corner site on a diagram `D`** (positive at the two crossings): the corner vertex
`M₁ = P (a+1)` of component `i`, its two incident edges `e_in = ⟨i, a⟩`, `e_out = ⟨i, a+1⟩`, one
straight remote strand `s` crossing both (`y₁` on `e_in`, `y₂` on `e_out`), and the printed
emptiness of the closed contact triangle.  For row 176: `D = carrierDiagram q₀'`, `M₁` = the
`j`-corner, `{y₁, y₂}` = the lifts of `u', v'`, `s` = the third triangle strand. -/
structure s176_CornerSite (D : Diagram) where
  i : Fin D.Γ.c
  a : ZMod (D.Γ.comp i).k
  hk : 4 ≤ (D.Γ.comp i).k
  s : D.Γ.Strand
  y₁ : D.Γ.Crossing
  y₂ : D.Γ.Crossing
  hy₁ : y₁.val = {⟨i, a⟩, s}
  hy₂ : y₂.val = {⟨i, a + 1⟩, s}
  pos₁ : D.IsPositive y₁
  pos₂ : D.IsPositive y₂
  clear : ∀ u : D.Γ.Strand, u ≠ ⟨i, a⟩ → u ≠ ⟨i, a + 1⟩ → u ≠ s →
    Disjoint (D.Γ.seg u)
      (convexHull ℝ {D.Γ.crossingPoint y₁, (D.Γ.comp i).P (a + 1), D.Γ.crossingPoint y₂})

namespace s176_CornerSite

variable {D : Diagram} (T : s176_CornerSite D)

/-- the entering edge `e_in = (M₀, M₁)` -/
def eIn : D.Γ.Strand := ⟨T.i, T.a⟩
/-- the exiting edge `e_out = (M₁, M₂)` -/
def eOut : D.Γ.Strand := ⟨T.i, T.a + 1⟩

theorem eIn_mem : T.eIn ∈ T.y₁.val := by
  rw [T.hy₁]; exact Finset.mem_insert_self _ _
theorem s_mem₁ : T.s ∈ T.y₁.val := by
  rw [T.hy₁]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
theorem eOut_mem : T.eOut ∈ T.y₂.val := by
  rw [T.hy₂]; exact Finset.mem_insert_self _ _
theorem s_mem₂ : T.s ∈ T.y₂.val := by
  rw [T.hy₂]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

theorem eIn_ne_s : T.eIn ≠ T.s := by
  intro h
  have h2 := D.Γ.crossing_card_two T.y₁
  rw [T.hy₁, show (⟨T.i, T.a⟩ : D.Γ.Strand) = T.eIn from rfl, h,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
  exact absurd h2 (by norm_num)

theorem eOut_ne_s : T.eOut ≠ T.s := by
  intro h
  have h2 := D.Γ.crossing_card_two T.y₂
  rw [T.hy₂, show (⟨T.i, T.a + 1⟩ : D.Γ.Strand) = T.eOut from rfl, h,
    Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
  exact absurd h2 (by norm_num)

theorem one_ne_zero_k : (1 : ZMod (D.Γ.comp T.i).k) ≠ 0 := by
  intro h
  have h' : (D.Γ.comp T.i).k ∣ 1 :=
    (ZMod.natCast_eq_zero_iff 1 (D.Γ.comp T.i).k).mp (by rw [Nat.cast_one]; exact h)
  have := Nat.le_of_dvd one_pos h'
  have := T.hk
  omega

theorem eIn_ne_eOut : T.eIn ≠ T.eOut := by
  intro h
  have h'' : T.a = T.a + 1 := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  exact T.one_ne_zero_k (by linear_combination -h'')

theorem y₁_ne_y₂ : T.y₁ ≠ T.y₂ := by
  intro h
  have hmem : T.eIn ∈ T.y₂.val := h ▸ T.eIn_mem
  rw [T.hy₂, Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h1 | h1
  · exact T.eIn_ne_eOut h1
  · exact T.eIn_ne_s h1

/-- transversality of `e_in` and `s` -/
theorem det_in_ne_zero : det (D.Γ.dir T.eIn) (D.Γ.dir T.s) ≠ 0 :=
  D.generic.transverse _ _ (D.Γ.crossing_pair_spec T.y₁ T.eIn_mem T.s_mem₁ T.eIn_ne_s).1
    (D.Γ.crossing_pair_spec T.y₁ T.eIn_mem T.s_mem₁ T.eIn_ne_s).2

/-- transversality of `e_out` and `s` -/
theorem det_out_ne_zero : det (D.Γ.dir T.eOut) (D.Γ.dir T.s) ≠ 0 :=
  D.generic.transverse _ _ (D.Γ.crossing_pair_spec T.y₂ T.eOut_mem T.s_mem₂ T.eOut_ne_s).1
    (D.Γ.crossing_pair_spec T.y₂ T.eOut_mem T.s_mem₂ T.eOut_ne_s).2

/-- **The corner identity**: the straight strand `s` through `y₁ ∈ e_in` and `y₂ ∈ e_out` crosses the
two edges of the corner `M₁` with OPPOSITE orientations — `(1 − t₁) det(e_in, s) + t₂ det(e_out, s) = 0`
with `t₁ < 1`, `0 < t₂`, so the two determinants have opposite signs.  This is the whole geometric
content of `same_over` (sm-4:614-618's sign table). -/
theorem det_mul_det_neg :
    det (D.Γ.dir T.eIn) (D.Γ.dir T.s) * det (D.Γ.dir T.eOut) (D.Γ.dir T.s) < 0 := by
  -- the four parametrisations of the two crossing points
  obtain ⟨-, -, h₁⟩ := D.crossingParam_spec T.y₁ T.eIn_mem
  obtain ⟨-, -, h₁'⟩ := D.crossingParam_spec T.y₁ T.s_mem₁
  obtain ⟨-, -, h₂⟩ := D.crossingParam_spec T.y₂ T.eOut_mem
  obtain ⟨-, -, h₂'⟩ := D.crossingParam_spec T.y₂ T.s_mem₂
  have ht₁ : D.crossingParam T.y₁ T.eIn_mem < 1 := D.crossingParam_lt_one T.y₁ T.eIn_mem
  have ht₂ : 0 < D.crossingParam T.y₂ T.eOut_mem := D.crossingParam_pos T.y₂ T.eOut_mem
  set t₁ := D.crossingParam T.y₁ T.eIn_mem
  set u₁ := D.crossingParam T.y₁ T.s_mem₁
  set t₂ := D.crossingParam T.y₂ T.eOut_mem
  set u₂ := D.crossingParam T.y₂ T.s_mem₂
  set A := D.Γ.dir T.eIn with hA
  set B := D.Γ.dir T.eOut with hB
  set S := D.Γ.dir T.s with hS
  set O := D.Γ.tail T.s with hO
  set Pa := (D.Γ.comp T.i).P T.a with hPa
  have e₁ : Pa + t₁ • A = O + u₁ • S := by
    have := h₁.symm.trans h₁'
    exact this
  have e₂ : (Pa + A) + t₂ • B = O + u₂ • S := by
    have := h₂.symm.trans h₂'
    have hPa1 : (D.Γ.comp T.i).P (T.a + 1) = Pa + A := by
      show _ = _ + edge (D.Γ.comp T.i).P T.a
      unfold edge; abel
    rw [show edgePoint (D.Γ.comp T.eOut.1).P T.eOut.2 t₂ = (D.Γ.comp T.i).P (T.a + 1) + t₂ • B from rfl,
      hPa1] at this
    exact this
  -- the linear relation `(1 − t₁) det(A, S) + t₂ det(B, S) = 0`
  have hlin : (1 - t₁) * det A S + t₂ * det B S = 0 := by
    have c1 := congrArg Prod.fst e₁
    have c2 := congrArg Prod.snd e₁
    have c3 := congrArg Prod.fst e₂
    have c4 := congrArg Prod.snd e₂
    simp only [Prod.fst_add, Prod.snd_add, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at c1 c2 c3 c4
    unfold det
    linear_combination S.2 * (c3 - c1) - S.1 * (c4 - c2)
  have hA0 : det A S ≠ 0 := T.det_in_ne_zero
  have hB0 : det B S ≠ 0 := T.det_out_ne_zero
  have hB2 : 0 < det B S * det B S := mul_self_pos.mpr hB0
  have h1t : 0 < 1 - t₁ := by linarith
  have key : (1 - t₁) * (det A S * det B S) = -(t₂ * (det B S * det B S)) := by
    linear_combination det B S * hlin
  by_contra hcon
  have hcon' : 0 ≤ det A S * det B S := not_lt.mp hcon
  nlinarith [mul_nonneg h1t.le hcon', mul_pos ht₂ hB2]

/-- On the positive diagram, `s` is over at `y₁` iff `det(e_in, s) < 0`. -/
theorem over₁_eq_s_iff : D.overStrand T.y₁ = T.s ↔ det (D.Γ.dir T.eIn) (D.Γ.dir T.s) < 0 := by
  have hpos := T.pos₁
  unfold Diagram.IsPositive at hpos
  constructor
  · intro h
    have hu : T.eIn = D.underStrand T.y₁ :=
      D.eq_under_of_mem_of_ne T.y₁ T.eIn_mem (by rw [h]; exact T.eIn_ne_s)
    rw [h, ← hu, det_swap] at hpos
    linarith
  · intro hlt
    by_contra h
    have ho : T.eIn = D.overStrand T.y₁ := by
      have hs : T.s = D.underStrand T.y₁ := D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)
      exact D.eq_over_of_mem_of_ne T.y₁ T.eIn_mem (by rw [← hs]; exact T.eIn_ne_s)
    have hs : T.s = D.underStrand T.y₁ := D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)
    rw [← ho, ← hs] at hpos
    linarith

/-- On the positive diagram, `s` is over at `y₂` iff `det(e_out, s) < 0`. -/
theorem over₂_eq_s_iff : D.overStrand T.y₂ = T.s ↔ det (D.Γ.dir T.eOut) (D.Γ.dir T.s) < 0 := by
  have hpos := T.pos₂
  unfold Diagram.IsPositive at hpos
  constructor
  · intro h
    have hu : T.eOut = D.underStrand T.y₂ :=
      D.eq_under_of_mem_of_ne T.y₂ T.eOut_mem (by rw [h]; exact T.eOut_ne_s)
    rw [h, ← hu, det_swap] at hpos
    linarith
  · intro hlt
    by_contra h
    have hs : T.s = D.underStrand T.y₂ := D.eq_under_of_mem_of_ne T.y₂ T.s_mem₂ (Ne.symm h)
    have ho : T.eOut = D.overStrand T.y₂ :=
      D.eq_over_of_mem_of_ne T.y₂ T.eOut_mem (by rw [← hs]; exact T.eOut_ne_s)
    rw [← ho, ← hs] at hpos
    linarith

/-- On the positive diagram exactly one of the two crossings has `s` over (the printed sign table). -/
theorem over₁_iff_not_over₂ : D.overStrand T.y₁ = T.s ↔ D.overStrand T.y₂ ≠ T.s := by
  rw [T.over₁_eq_s_iff, ne_eq, T.over₂_eq_s_iff]
  have h := T.det_mul_det_neg
  have hA := T.det_in_ne_zero
  have hB := T.det_out_ne_zero
  constructor
  · intro h1 h2
    nlinarith
  · intro h2
    have h2' : 0 < det (D.Γ.dir T.eOut) (D.Γ.dir T.s) := lt_of_le_of_ne (not_lt.mp h2) (Ne.symm hB)
    by_contra h1
    have h1' : 0 < det (D.Γ.dir T.eIn) (D.Γ.dir T.s) := lt_of_le_of_ne (not_lt.mp h1) (Ne.symm hA)
    nlinarith

/-- the under strand at `y₁` is `s` iff the over strand is not -/
theorem under₁_eq_s_iff : D.underStrand T.y₁ = T.s ↔ D.overStrand T.y₁ ≠ T.s := by
  constructor
  · intro h h'
    exact D.under_ne_over T.y₁ (h.trans h'.symm)
  · intro h
    exact (D.eq_under_of_mem_of_ne T.y₁ T.s_mem₁ (Ne.symm h)).symm

theorem under₂_eq_s_iff : D.underStrand T.y₂ = T.s ↔ D.overStrand T.y₂ ≠ T.s := by
  constructor
  · intro h h'
    exact D.under_ne_over T.y₂ (h.trans h'.symm)
  · intro h
    exact (D.eq_under_of_mem_of_ne T.y₂ T.s_mem₂ (Ne.symm h)).symm

/-- **`same_over` after switching `y₁`** (the frozen field of `BigonData`, verbatim on `D.switch y₁`). -/
theorem same_over_switch₁ :
    ((D.switch T.y₁).overStrand T.y₁ = T.s ∧ (D.switch T.y₁).overStrand T.y₂ = T.s) ∨
      ((D.switch T.y₁).overStrand T.y₁ ≠ T.s ∧ (D.switch T.y₁).overStrand T.y₂ ≠ T.s) := by
  have h1 : (D.switch T.y₁).overStrand T.y₁ = D.underStrand T.y₁ := D.switch_overStrand_self T.y₁
  have h2 : (D.switch T.y₁).overStrand T.y₂ = D.overStrand T.y₂ :=
    D.switch_overStrand_of_ne T.y₁_ne_y₂.symm
  by_cases h : D.overStrand T.y₂ = T.s
  · exact Or.inl ⟨h1.trans (T.under₁_eq_s_iff.mpr fun h' => (T.over₁_iff_not_over₂.mp h') h),
      h2.trans h⟩
  · exact Or.inr ⟨fun h' => (T.under₁_eq_s_iff.mp (h1.symm.trans h')) (T.over₁_iff_not_over₂.mpr h),
      fun h' => h (h2.symm.trans h')⟩

/-- **`same_over` after switching `y₂`.** -/
theorem same_over_switch₂ :
    ((D.switch T.y₂).overStrand T.y₁ = T.s ∧ (D.switch T.y₂).overStrand T.y₂ = T.s) ∨
      ((D.switch T.y₂).overStrand T.y₁ ≠ T.s ∧ (D.switch T.y₂).overStrand T.y₂ ≠ T.s) := by
  have h1 : (D.switch T.y₂).overStrand T.y₁ = D.overStrand T.y₁ :=
    D.switch_overStrand_of_ne T.y₁_ne_y₂
  have h2 : (D.switch T.y₂).overStrand T.y₂ = D.underStrand T.y₂ := D.switch_overStrand_self T.y₂
  by_cases h : D.overStrand T.y₁ = T.s
  · exact Or.inl ⟨h1.trans h, h2.trans (T.under₂_eq_s_iff.mpr (T.over₁_iff_not_over₂.mp h))⟩
  · exact Or.inr ⟨fun h' => h (h1.symm.trans h'),
      fun h' => (T.under₂_eq_s_iff.mp (h2.symm.trans h'))
        (not_not.mp fun hne => h (T.over₁_iff_not_over₂.mpr hne))⟩

/-- **The site theorem, switched at `y₁`**: a `BigonData` on `D.switch y₁` with the frozen fields,
through the frozen leaf `exists_bigonData_of_triangle` (the closed contact triangle `K`). -/
theorem exists_bigon_switch₁ :
    ∃ B : BigonData (D.switch T.y₁), B.i = T.i ∧ B.y = T.y₁ ∧ B.z = T.y₂ :=
  exists_bigonData_of_triangle (D.switch T.y₁) T.i T.a T.hk T.s T.y₁ T.y₂ T.hy₁ T.hy₂
    T.same_over_switch₁ T.clear

/-- **The site theorem, switched at `y₂`.** -/
theorem exists_bigon_switch₂ :
    ∃ B : BigonData (D.switch T.y₂), B.i = T.i ∧ B.y = T.y₁ ∧ B.z = T.y₂ :=
  exists_bigonData_of_triangle (D.switch T.y₂) T.i T.a T.hk T.s T.y₁ T.y₂ T.hy₁ T.hy₂
    T.same_over_switch₂ T.clear

/-- **The site theorem for the switched crossing `y₀ ∈ {y₁, y₂}`** (row 176's `y` is the lift of the
retained unselected crossing `u'`, which is `y₁` or `y₂` according to the orientation of the corner). -/
theorem exists_bigon_switch (y₀ : D.Γ.Crossing) (h : y₀ = T.y₁ ∨ y₀ = T.y₂) :
    ∃ B : BigonData (D.switch y₀), B.i = T.i ∧ (B.y = y₀ ∨ B.z = y₀) := by
  rcases h with rfl | rfl
  · obtain ⟨B, hi, hy, -⟩ := T.exists_bigon_switch₁
    exact ⟨B, hi, Or.inl hy⟩
  · obtain ⟨B, hi, -, hz⟩ := T.exists_bigon_switch₂
    exact ⟨B, hi, Or.inr hz⟩

end s176_CornerSite

/-- **`hk` for a one-component site**: if the remote strand lies on the same component as the corner
(row 176: the carrier diagram has one component) then `k ≥ 4` — a crossing pairs NON-adjacent strands,
and on `ZMod 3` every pair of labels is adjacent. -/
theorem s176_four_le_of_crossing (D : Diagram) (i : Fin D.Γ.c) (a b : ZMod (D.Γ.comp i).k)
    (x : D.Γ.Crossing) (hx : x.val = {⟨i, a⟩, ⟨i, b⟩}) : 4 ≤ (D.Γ.comp i).k := by
  have hne : (⟨i, a⟩ : D.Γ.Strand) ≠ ⟨i, b⟩ := by
    intro h
    have h2 := D.Γ.crossing_card_two x
    rw [hx, h, Finset.insert_eq_of_mem (Finset.mem_singleton_self _), Finset.card_singleton] at h2
    exact absurd h2 (by norm_num)
  have hna := (D.Γ.crossing_pair_spec x (by rw [hx]; exact Finset.mem_insert_self _ _)
    (by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)) hne).1
  rw [D.Γ.adjacent_mk_iff] at hna
  have h3 := (D.Γ.comp i).hk
  by_contra hlt
  have hk3 : (D.Γ.comp i).k = 3 := by omega
  apply hna
  have key : ∀ (m : ℕ), m = 3 → ∀ c d : ZMod m, adjacent c d := by
    rintro m rfl c d
    unfold adjacent
    revert c d
    decide
  exact key _ hk3 a b

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §B. Row 176 re-based on the weak port (F-176-1): the port data, the ledger, the row shape -/

/-- **`est_PortData` with the `port` field in the deliverable (weak) form** (PLAN_FINAL §3 F-176-1): every
other field is byte-identical to `RProof.est_PortData` (RALedgers.lean:872); `port` becomes
`est_port_weak D₊ D₀ y = ∃ D₀', ReflTransGen RII (D₊.switch y) D₀' ∧ homfly D₀' = homfly D₀`. -/
structure s176_PortDataWeak (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  /-- (T2) the RII port relation in the weak form (the only changed field) -/
  port : est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

/-- **The non-move part of the port data** (U_R176_REPORT §5 items 2–5: the oriented smoothing `D_A`,
the exact owner map (9)/(9a), the linking number, the writhe/rotation/sign ledgers): `est_PortData`
minus `port`.  This is what row 176 still owes beyond the site and `hrec`. -/
structure s176_PortDataRest (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
    {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
    (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
    (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing) where
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  Sf : Finset (Crossing P')
  hSf : Sf ∈ CV.Ind hG'.crossingGeometry
  Λ₁ : GeoComponent hG'.crossingGeometry Sf
  Λ₂ : GeoComponent hG'.crossingGeometry Sf
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  ℓ : ℤ
  link : CV.IsLinkingNumber DA i j ℓ
  writhe : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ + 2 * ℓ
  rot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1
  alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁)
  alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)

section S176PortData

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
  {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
  (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
  (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
  (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)

/-- The weak port data = the weak port + the rest. -/
def s176_PortDataWeak.mk' (port : est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y)
    (R : s176_PortDataRest hn hG hG' hS hS' q q' y) : s176_PortDataWeak hn hG hG' hS hS' q q' y :=
  ⟨port, R.DA, R.smooth, R.two, R.i, R.j, R.ij, R.Sf, R.hSf, R.Λ₁, R.Λ₂, R.poly₁, R.poly₂, R.ℓ, R.link,
    R.writhe, R.rot, R.alt₁, R.alt₂⟩

/-- The literal port data gives the weak one (`D₀' := D₀`). -/
def s176_PortDataWeak.ofPortData (D : est_PortData hn hG hG' hS hS' q q' y) :
    s176_PortDataWeak hn hG hG' hS hS' q q' y :=
  ⟨⟨_, D.port, rfl⟩, D.DA, D.smooth, D.two, D.i, D.j, D.ij, D.Sf, D.hSf, D.Λ₁, D.Λ₂, D.poly₁, D.poly₂,
    D.ℓ, D.link, D.writhe, D.rot, D.alt₁, D.alt₂⟩

/-- **The weak port from the bigon site and the record identification** (the composition (a)+(b) →
`est_port_weak_of_bigon`): `Dp = carrierDiagram q₀'`, `D₀ = carrierDiagram q₀`, both one-component
(`geoPositiveLift_componentCount`, `rfl`). -/
theorem s176_port_weak_of_bigon (B : BigonData ((CV.carrierDiagram hn hG' hS' q').switch y))
    (hrec : Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hS q).record)) :
    est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y :=
  est_port_weak_of_bigon _ _ y rfl rfl B hrec

/-- The weak port from an abstract corner site on `carrierDiagram q₀'` whose switched crossing is one
of the two site crossings, plus the record identification of the reduced record for THAT bigon. -/
theorem s176_port_weak_of_cornerSite (T : s176_CornerSite (CV.carrierDiagram hn hG' hS' q'))
    (hy : y = T.y₁ ∨ y = T.y₂)
    (hrec : ∀ B : BigonData ((CV.carrierDiagram hn hG' hS' q').switch y), B.i = T.i →
      (B.y = y ∨ B.z = y) → Nonempty (RecordIso B.reducedRecord (CV.carrierDiagram hn hG hS q).record)) :
    est_port_weak (CV.carrierDiagram hn hG' hS' q') (CV.carrierDiagram hn hG hS q) y := by
  obtain ⟨B, hi, hyz⟩ := T.exists_bigon_switch y hy
  exact s176_port_weak_of_bigon hn hG hG' hS hS' q q' y B (hrec B hi hyz)

/-- **(16) `Ω_+ = Ω_0` from the WEAK port data** — `est_omega1_eq_of_port` (RALedgers.lean:915) replayed
verbatim with the ONE call `CV.fulltwist_coefficient … D.port …` replaced by
`fulltwist_coefficient_of_port_weak … D.port …` (F-176-1: 1 line changed, the rest byte-identical). -/
theorem s176_est_omega1_eq_of_port_weak (hF : CV.CarrierSlotFloor)
    (D : s176_PortDataWeak hn hG hG' hS hS' q q' y)
    (hw : CV.groupedWrithe hG' q' = CV.groupedWrithe hG q + 2)
    (hR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q) :
    CV.Omega1 hn hG' hS' q' = CV.Omega1 hn hG hS q := by
  have hpos : (CV.carrierDiagram hn hG' hS' q').IsPositive y := geoPositiveLift_isPositive hn _ _ q' y
  -- (7) `d_+ = d_0 − 2`
  have hd : CV.d (CV.carrierDiagram hn hG' hS' q') rfl = CV.d (CV.carrierDiagram hn hG hS q) rfl - 2 := by
    rw [est_carrierDiagram_d, est_carrierDiagram_d]
    unfold CV.slot
    rw [hw, hR]; ring
  -- (8) lem:fulltwist, re-based on the weak port (the ONE changed call)
  have hft := fulltwist_coefficient_of_port_weak (CV.carrierDiagram hn hG' hS' q')
    (CV.carrierDiagram hn hG hS q) D.DA y hpos D.smooth D.port rfl rfl hd
  rw [est_carrierDiagram_Omega, est_carrierDiagram_Omega, est_carrierDiagram_d] at hft
  -- (11) lem:homflyrows (ii)
  have hrow := CV.homflyrows.two_component_row D.DA D.i D.j D.two D.ij D.ℓ D.link
  rw [D.poly₁, D.poly₂] at hrow
  have hcoef := est_coeffAt_of_zRow _ _ (CV.slot hn hG hS q) D.ℓ hrow
  -- the floor at the two clean outer carriers
  have hne₁ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₁
  have hne₂ := CV.cvt_groupedPoly_ne_zero hn hG' D.hSf D.Λ₂
  have h₁ := hF hn hG' D.hSf D.Λ₁ D.alt₁
  have h₂ := hF hn hG' D.hSf D.Λ₂ D.alt₂
  -- (15) `D = d_0 + 2 + 2ℓ`
  have hsum : CV.slot hn hG' D.hSf D.Λ₁ + CV.slot hn hG' D.hSf D.Λ₂ =
      CV.slot hn hG hS q + 2 + 2 * D.ℓ := by
    unfold CV.slot
    have := D.writhe
    have := D.rot
    omega
  -- (16)
  have hz₁ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q - 2 + 2 * D.ℓ) h₁ h₂ (by omega)
  have hz₂ := est_coeffAt_mul_eq_zero _ _ hne₁ hne₂ _ _ (CV.slot hn hG hS q + 2 * D.ℓ) h₁ h₂ (by omega)
  rw [hcoef, hz₁, hz₂, sub_zero] at hft
  linarith

end S176PortData

/-- **The RII port relation of row 176 in the weak form** — `RProof.est_port_relation` (RALedgers.lean:1453)
with `est_PortData` replaced by `s176_PortDataWeak`; otherwise byte-identical. -/
def s176_est_port_relation_weak : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataWeak hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

/-- The literal interface implies the weak one. -/
theorem s176_est_port_relation_weak_of_strong (h : est_port_relation) : s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu', ⟨D⟩⟩ := h n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg'
    hcomp Q hQ hfull j hj q hex
  exact ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.ofPortData _ _ _ _ _ _ _ _ D⟩⟩

section S176Ledger

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- `est_row_H` (RALedgers.lean:1514) replayed with the weak interface: the only change is the call
`est_omega1_eq_of_port` ↦ `s176_est_omega1_eq_of_port_weak`. -/
theorem s176_est_row_H_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
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
      hcomp Q hQ hfull j hj q ⟨u, hu, hju.symm, hu'⟩
    exact s176_est_omega1_eq_of_port_weak hn _ _ hS hS' q _ _ hF D
      (est_groupedWrithe_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq)
      (GT_carrierR_eq hn (genericAt E t ht.1) (genericAt E t' ht'.1) W hS hS' q)
  · exact est_omega1_eq_of_ne hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- `est_row` (RALedgers.lean:1548) replayed with the weak interface (byte-identical body). -/
theorem s176_est_row_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) (hn : 3 ≤ n)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    {t t' : E.Parameter} (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hext : ExtremeLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) :
    rowTerm hn (genericAt E t ht.1) (Q ∪ {j}) =
      rowTerm hn (genericAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) := by
  rcases hext with hcomp | hemp
  · exact s176_est_row_H_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj
  · have hs' : ∀ s, IsCrossing (E.curve t') s ↔ IsCrossing (E.curve t) s := fun s => (hs s).symm
    have hop' : OppositeSides E t' t := by
      unfold OppositeSides at hop ⊢; linarith [mul_comm t.val t'.val]
    obtain ⟨hef'', heg'', hfg''⟩ := hL.triangle_crossings t' ht'
    have hcomp' : CompleteLocal (geomAt E t' ht'.1) hef'' heg'' hfg'' :=
      (PRE_176_graphs_complementary hL t' t ht' ht hop' hef'' heg'' hfg'' hef' heg' hfg').mpr hemp
    have hQ' := GT_outsideSupports_transport hL ht ht' hop hs hQ
    have hfull' := GT_fullAvail_transport hL ht ht' hop hs hQ hfull
    have hj' : (crossingTransport hs j).val ∈ triangleSupports e f g := hj
    have h := s176_est_row_H_weak hF hport hn hL hR hef heg hfg ht' ht hop' hs' hcomp' hQ' hfull' hj'
    rw [← GT_transportSupport_S hs Q j, EXT_transportSupport_symm hs (Q ∪ {j})] at h
    exact h.symm

/-- `est_extremeTransportData` (RALedgers.lean:1576) replayed with the weak interface. -/
theorem s176_est_extremeTransportData_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak)
    (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hGT : GenericTableData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) : ExtremeTransportData hn E e f g δ where
  singleton_rows_present := PRE_176_singleton_rows_present E e f g δ
  graphs_complementary := PRE_176_graphs_complementary hL
  sign_branch := PRE_176_sign_branch hGT
  transport_x := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inl rfl))
  transport_y := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inl rfl)))
  transport_z := fun _ _ ht ht' hop hs _ _ _ hext _ hQ hfull =>
    s176_est_row_weak hF hport hn hL hR hef heg hfg ht ht' hop hs hext hQ hfull
      ((P1.mem_triangleSupports _).mpr (Or.inr (Or.inr rfl)))

end S176Ledger

/-- **The RA ledger of row 176 re-based on the weak port** — `est_ledger` (RALedgers.lean:1598) with
`est_port_relation` replaced by `s176_est_port_relation_weak`; the body is byte-identical. -/
theorem s176_est_ledger_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak) :
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
  exact s176_est_extremeTransportData_weak hF hport hn hL' hGT' hR' hef heg hfg

/-- The row statement from the weak ledger (`est_extreme_transport_of` re-based). -/
theorem s176_est_extreme_transport_of_weak (hF : CV.CarrierSlotFloor) (hport : s176_est_port_relation_weak)
    (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n)
    (h3 : remote e f ∧ remote f g ∧ remote e g ∧ CV.rep e < CV.rep f ∧ CV.rep f < CV.rep g)
    (h4e : remote e f ∧ remote e g ∧ f ≠ g ∧ CV.rep f < CV.rep g)
    (h4f : remote f e ∧ remote f g ∧ e ≠ g ∧ CV.rep e < CV.rep g)
    (h4g : remote g e ∧ remote g f ∧ e ≠ f ∧ CV.rep e < CV.rep f)
    (hE : E.IsSimpleRIII e f g h3 h4e h4f h4g) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ E.radius ∧ ExtremeTransportData hn E e f g δ :=
  s176_est_ledger_weak hF hport n hn E e f g h3 h4e h4f h4g hE

/-- Sanity: the weak ledger recovers the accepted one from the literal interface. -/
theorem s176_est_ledger_of_strong (hF : CV.CarrierSlotFloor) (hport : est_port_relation) :
    RowShape @ExtremeTransportData :=
  s176_est_ledger_weak hF (s176_est_port_relation_weak_of_strong hport)

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §C. The carrier-level realisation of the corner site — general lemmas on a carrier `q` of an
independent support `T` on a `CarrierGeometry` polygon `P` (the L side of row 176), with the other
side `P'` entering only through `ExactTriangleVisitOrders` (R-LOC (2)–(3) at the Gauss-word level). -/

section S176Carrier

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

omit [NeZero n] in
theorem s176_union_supports {x y : Crossing P} {ℓ m m' : ZMod n} (hx : x.val = {ℓ, m})
    (hy : y.val = {ℓ, m'}) : x.val ∪ y.val = {ℓ, m, m'} := by
  rw [hx, hy]
  ext z
  simp only [Finset.mem_union, Finset.mem_insert, Finset.mem_singleton]
  tauto

omit [NeZero n] in
/-- a visit on `ℓ` whose crossing contains the label `m'` and `ℓ` is THE visit of the crossing `{ℓ, m'}` -/
theorem s176_visit_eq_of_mem {y : Crossing P} {ℓ m' : ZMod n} (hy : y.val = {ℓ, m'}) (hℓm' : ℓ ≠ m')
    (w : Visit P) (hw : w.2.val = ℓ) (hm' : m' ∈ w.1.val) :
    w = visitOn y ℓ (by rw [hy]; exact Finset.mem_insert_self _ _) := by
  obtain ⟨c, ⟨i, hi⟩⟩ := w
  change i = ℓ at hw
  subst hw
  change m' ∈ c.val at hm'
  have hsub : ({i, m'} : Finset (ZMod n)) ⊆ c.val := by
    intro z hz
    rcases Finset.mem_insert.mp hz with rfl | hz
    · exact hi
    · rw [Finset.mem_singleton.mp hz]; exact hm'
  have hval : ({i, m'} : Finset (ZMod n)) = c.val :=
    Finset.eq_of_subset_of_card_le hsub (by rw [crossing_card_two c, Finset.card_pair hℓm'])
  have hc : c = y := Subtype.ext (hval.symm.trans hy.symm)
  subst hc
  rfl

omit [NeZero n] in
/-- **No visit between two adjacent triangle visits on their shared edge** (the labelled form of
`G11_no_visit_between`, for the crossings `x = {ℓ, m}`, `y = {ℓ, m'}` and the triple `{ℓ, m, m'}`). -/
theorem s176_no_visit_between {ℓ m m' : ZMod n} (hℓm : ℓ ≠ m) (hℓm' : ℓ ≠ m') (hmm' : m ≠ m')
    (hX : ExactTriangleVisitOrders P P' ℓ m m' hs) {x y : Crossing P}
    (hx : x.val = {ℓ, m}) (hy : y.val = {ℓ, m'}) (hℓx : ℓ ∈ x.val) (hℓy : ℓ ∈ y.val)
    (w : Visit P) (hw : w.2.val = ℓ) :
    ¬ (visitParameter (visitOn x ℓ hℓx) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn y ℓ hℓy)) ∧
    ¬ (visitParameter (visitOn y ℓ hℓy) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn x ℓ hℓx)) := by
  set vx := visitOn x ℓ hℓx with hvx
  set vy := visitOn y ℓ hℓy with hvy
  have hunion : x.val ∪ y.val = {ℓ, m, m'} := s176_union_supports hx hy
  have hunion' : y.val ∪ x.val = {ℓ, m, m'} := by rw [Finset.union_comm]; exact hunion
  have hnA : ∀ w : Visit P, w.2.val = ℓ → w ≠ vy → x.val ∪ w.1.val ≠ {ℓ, m, m'} := by
    intro w hw hwy hu
    apply hwy
    apply s176_visit_eq_of_mem hy hℓm' w hw
    have hm' : m' ∈ x.val ∪ w.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hm' with h | h
    · exfalso
      rw [hx, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hℓm' h.symm
      · exact hmm' h.symm
    · exact h
  have hnB : ∀ w : Visit P, w.2.val = ℓ → w ≠ vx → y.val ∪ w.1.val ≠ {ℓ, m, m'} := by
    intro w hw hwx hu
    apply hwx
    apply s176_visit_eq_of_mem hx hℓm w hw
    have hm : m ∈ y.val ∪ w.1.val := by rw [hu]; simp
    rcases Finset.mem_union.mp hm with h | h
    · exfalso
      rw [hy, Finset.mem_insert, Finset.mem_singleton] at h
      rcases h with h | h
      · exact hℓm h.symm
      · exact hmm' h
    · exact h
  constructor
  · rintro ⟨h1, h2⟩
    have hwx : w ≠ vx := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have hwy : w ≠ vy := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have h1' := ((hX vx w hw.symm).2 (hnA w hw hwy)).mp h1
    have h2' := ((hX w vy hw).2 (by rw [Finset.union_comm]; exact hnB w hw hwx)).mp h2
    have h3 := ((hX vx vy rfl).1 hunion).mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)
  · rintro ⟨h1, h2⟩
    have hwx : w ≠ vx := fun h => by rw [h] at h2; exact lt_irrefl _ h2
    have hwy : w ≠ vy := fun h => by rw [h] at h1; exact lt_irrefl _ h1
    have h1' := ((hX vy w hw.symm).2 (hnB w hw hwx)).mp h1
    have h2' := ((hX w vx hw).2 (by rw [Finset.union_comm]; exact hnA w hw hwy)).mp h2
    have h3 := ((hX vy vx rfl).1 hunion').mp (h1.trans h2)
    exact lt_irrefl _ ((h1'.trans h2').trans h3)

include hn in
/-- the `ρ_T`-successor of an unselected visit is the next visit on its edge when no visit lies between -/
theorem s176_succ_of_lt {x y : Crossing P} {ℓ : ZMod n} (hℓx : ℓ ∈ x.val) (hℓy : ℓ ∈ y.val)
    (hxT : x ∉ T)
    (hlt : visitParameter (visitOn x ℓ hℓx) < visitParameter (visitOn y ℓ hℓy))
    (hnb : ∀ w : Visit P, w.2.val = ℓ →
      ¬ (visitParameter (visitOn x ℓ hℓx) < visitParameter w ∧
          visitParameter w < visitParameter (visitOn y ℓ hℓy))) :
    geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn x ℓ hℓx)) = Sum.inr (visitOn y ℓ hℓy) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hG.cg T _ hxT]
  exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt hnb

include hn hT in
/-- **Distinct corners of a carrier sit at distinct points** (`tail_off` + nonzero edges). -/
theorem s176_cornerPolygon_inj {i j : ZMod (geoCornerCount hG.cg T q)}
    (h : geoCornerPolygon hG.cg T q i = geoCornerPolygon hG.cg T q j) : i = j := by
  by_contra hij
  have hmem : geoCornerPolygon hG.cg T q i ∈ edgeSegment (geoCornerPolygon hG.cg T q) j :=
    ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]; exact h⟩
  by_cases hinc : incident i j
  · rcases hinc with hj | hj
    · apply geoCornerPolygon_edge_ne_zero_of_independent hn hG.cg hT q j
      have h' : geoCornerPolygon hG.cg T q (j + 1) = geoCornerPolygon hG.cg T q j := by
        rw [hj, sub_add_cancel, ← hj]; exact h
      show geoCornerPolygon hG.cg T q (j + 1) - geoCornerPolygon hG.cg T q j = 0
      rw [h', sub_self]
    · exact hij hj.symm
  · exact geoCornerPolygon_tail_off hn hG hT q i j hinc hmem

/-- **The strands of the lift of a retained crossing** are the carrier edges of its two visits
(`G11_carrierEdge_isCrossing`, `G11_carrierEdge_crossingPoint`, injectivity of crossing points). -/
theorem s176_lift_val (w : Visit P) (hw : w.1 ∈ geoCarrierCrossings hG.cg T q) :
    ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩).val =
      {(⟨0, G11_carrierEdge hn hG hT q w hw⟩ : (geoCarrierShadow hn hG hT q).Strand),
       ⟨0, G11_carrierEdge hn hG hT q (visitTwin w) (by rw [visitTwin_crossing]; exact hw)⟩} := by
  have hc := G11_carrierEdge_isCrossing hn hG hT q w hw
  have hgen := geoCarrierShadow_generic hn hG hT q
  set x' : (geoCarrierShadow hn hG hT q).Crossing :=
    (Shadow.singleCrossingEquiv (geoCarrierPolyComp hn hG hT q)).symm (xPair hc) with hx'
  have h1 : (geoCarrierShadow hn hG hT q).crossingPoint
      ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩) = crossingPoint w.1 := by
    rw [← crossingPoint_geoCarrierCrossingEquiv, Equiv.apply_symm_apply]
  have h2 : (geoCarrierShadow hn hG hT q).crossingPoint x' = crossingPoint w.1 := by
    rw [Shadow.single_crossingPoint _ hgen, hx', Equiv.apply_symm_apply]
    exact G11_carrierEdge_crossingPoint hn hG hT q w hw hc
  have heq : (geoCarrierCrossingEquiv hn hG hT q).symm ⟨w.1, hw⟩ = x' :=
    hgen.crossingPoint_injective (h1.trans h2.symm)
  rw [heq, hx']
  show ((xPair hc).val.map (Shadow.singleStrandEquiv (geoCarrierPolyComp hn hG hT q)).symm.toEmbedding) = _
  rw [show (xPair hc).val = {G11_carrierEdge hn hG hT q w hw,
      G11_carrierEdge hn hG hT q (visitTwin w) (by rw [visitTwin_crossing]; exact hw)} from rfl,
    Finset.map_insert, Finset.map_singleton]
  rfl

include hn hT in
/-- **The next corner after a block mark**: if `ρ^r c_k` is an (unselected) block mark of the edge `k`
and its `ρ`-successor is a true corner, that corner is `c_{k+1}` (`geoCornerPolygon_block`). -/
theorem s176_next_corner {k : ZMod (geoCornerCount hG.cg T q)} {r : ℕ} {w : Visit P}
    (hρ : (geoSmoothingSuccessor hG.cg T ^ r) (geoCornerMark hG.cg T q k) = Sum.inr w)
    (hb : GeoBlockInterior hG.cg T q k r) {m : Mark P} (hm : IsTrueCorner T m)
    (hsucc : geoSmoothingSuccessor hG.cg T (Sum.inr w) = m) :
    geoCornerMark hG.cg T q (k + 1) = m := by
  have hblock := geoCornerPolygon_block hn hG.cg hT q k
  obtain ⟨mk, hmk1, hchain, hmid, -, -, -, -, -⟩ := hblock
  have hρ1 : (geoSmoothingSuccessor hG.cg T ^ (r + 1)) (geoCornerMark hG.cg T q k) = m := by
    rw [pow_succ', Equiv.Perm.mul_apply, hρ, hsucc]
  rcases lt_trichotomy (r + 1) mk with hlt | heq | hgt
  · exfalso
    obtain ⟨v, hv, hvT, -⟩ := hmid (r + 1) (by omega) hlt
    rw [hρ1] at hv
    rw [hv] at hm
    exact hvT hm
  · rw [← hchain, ← heq, hρ1]
  · exfalso
    obtain ⟨v, hv, hvT, -⟩ := hb mk hmk1 (by omega)
    rw [hchain] at hv
    have := isTrueCorner_geoCornerMark hG.cg T q (k + 1)
    rw [hv] at this
    exact hvT this

/-- **The carrier edge of the first block mark after a corner**: if `ρ c_k` is a retained visit on the
outgoing edge of `c_k`, its carrier edge is `k` (`geo_block_mark_eq`). -/
theorem s176_carrierEdge_of_succ {k : ZMod (geoCornerCount hG.cg T q)} {w : Visit P}
    (hw : w.1 ∈ geoCarrierCrossings hG.cg T q)
    (hsucc : geoSmoothingSuccessor hG.cg T (geoCornerMark hG.cg T q k) = Sum.inr w)
    (hedge : w.2.val = (geoOutSlot hG.cg T (geoCornerMark hG.cg T q k)).1) :
    G11_carrierEdge hn hG hT q w hw = k := by
  obtain ⟨r', -, hρ', hb', -, -⟩ := gu1_carrierEdge_block hn hG hT q w hw
  have hwT : w.1 ∉ T := ((mem_geoCarrierCrossings hG.cg T q w.1).mp hw).1
  have hb1 : GeoBlockInterior hG.cg T q k 1 := by
    intro i h1 hi
    have hi1 : i = 1 := by omega
    subst hi1
    exact ⟨w, by rw [pow_one]; exact hsucc, hwT, hedge⟩
  exact (geo_block_mark_eq hG.cg T q hb' hb1 (hρ'.trans (by rw [pow_one]; exact hsucc.symm))).1

/-- the owner of a retained visit is `q` -/
theorem s176_owner_of_retained {x : Crossing P} (hx : x ∈ geoCarrierCrossings hG.cg T q) (w : Visit P)
    (hw : w.1 = x) : geoOwner hG.cg T (Sum.inr w) = q :=
  ((mem_geoCarrierCrossings hG.cg T q x).mp hx).2 w hw

/-- **From the index form of clearance to the strand form of `s176_CornerSite.clear`** on the
one-component carrier shadow. -/
theorem s176_clear_of_indices (kA kB kC : ZMod (geoCornerCount hG.cg T q)) (K : Set Plane)
    (hcl : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ kA → h ≠ kB → h ≠ kC →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h, x ∉ K) :
    ∀ w : (geoCarrierShadow hn hG hT q).Strand,
      w ≠ ⟨(0 : Fin 1), kA⟩ → w ≠ ⟨(0 : Fin 1), kB⟩ → w ≠ ⟨(0 : Fin 1), kC⟩ →
      Disjoint ((geoCarrierShadow hn hG hT q).seg w) K := by
  intro w hA hB hC
  rw [← Shadow.single_strand_eta _ w] at hA hB hC ⊢
  have hA' : w.2 ≠ kA := fun e => hA (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  have hB' : w.2 ≠ kB := fun e => hB (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  have hC' : w.2 ≠ kC := fun e => hC (congrArg (fun k : ZMod (geoCornerCount hG.cg T q) =>
    (⟨(0 : Fin 1), k⟩ : (geoCarrierShadow hn hG hT q).Strand)) e)
  show Disjoint (edgeSegment (geoCornerPolygon hG.cg T q) w.2) K
  exact Set.disjoint_left.mpr fun x hx hxK => hcl w.2 hA' hB' hC' x hx hxK

end S176Carrier

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section S176Corner

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

omit [NeZero n] in
/-- the twin of the visit of `x = {ℓ, m}` on `ℓ` is its visit on `m` -/
theorem s176_visitTwin_eq {x : Crossing P} {ℓ m : ZMod n} (_hx : x.val = {ℓ, m}) (hℓm : ℓ ≠ m)
    (hℓx : ℓ ∈ x.val) (hmx : m ∈ x.val) : visitTwin (visitOn x ℓ hℓx) = visitOn x m hmx := by
  rcases visit_eq_or_twin (visitOn x ℓ hℓx) (visitOn x m hmx) rfl with h | h
  · exfalso
    have := congrArg (fun w : Visit P => w.2.val) h
    exact hℓm (this.symm)
  · exact h.symm

omit [NeZero n] in
theorem s176_mem_left {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : ℓ ∈ x.val := by
  rw [hx]; exact Finset.mem_insert_self _ _

omit [NeZero n] in
theorem s176_mem_right {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : m ∈ x.val := by
  rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)

omit [NeZero n] in
theorem s176_pair_comm' {x : Crossing P} {ℓ m : ZMod n} (hx : x.val = {ℓ, m}) : x.val = {m, ℓ} := by
  rw [hx, Finset.pair_comm]

omit [NeZero n] in
/-- two crossings with a common label and different second labels are distinct -/
theorem s176_ne_of_supports {x y : Crossing P} {ℓ m m' : ZMod n} (hx : x.val = {ℓ, m})
    (hy : y.val = {ℓ, m'}) (hℓm' : ℓ ≠ m') (hmm' : m ≠ m') : x ≠ y := by
  intro h
  have : m' ∈ x.val := by rw [h, hy]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
  rw [hx, Finset.mem_insert, Finset.mem_singleton] at this
  rcases this with h1 | h1
  · exact hℓm' h1.symm
  · exact hmm' h1.symm

/-- a corner mark of `q` is owned by `q` -/
theorem s176_owner_cornerMark (k : ZMod (geoCornerCount hG.cg T q)) :
    geoOwner hG.cg T (geoCornerMark hG.cg T q k) = q :=
  (geoCornerMark_mem hG.cg T q k).1

include hn hT in
/-- **No carrier has two corners at one crossing point**: the two visits of a selected crossing `j`
cannot both be corner marks of `q` (distinct corners sit at distinct points, `s176_cornerPolygon_inj`). -/
theorem s176_no_two_corners {j : Crossing P} (hjT : j ∈ T) {a b : ZMod n} (hab : a ≠ b)
    (haj : a ∈ j.val) (hbj : b ∈ j.val)
    (h1 : geoOwner hG.cg T (Sum.inr (visitOn j a haj)) = q)
    (h2 : geoOwner hG.cg T (Sum.inr (visitOn j b hbj)) = q) : False := by
  obtain ⟨k₁, hk₁⟩ := geoCornerMark_exists_of_owner hG.cg T q _ h1 (by exact hjT)
  obtain ⟨k₂, hk₂⟩ := geoCornerMark_exists_of_owner hG.cg T q _ h2 (by exact hjT)
  have hpt : geoCornerPolygon hG.cg T q k₁ = geoCornerPolygon hG.cg T q k₂ := by
    rw [geoCornerPolygon_apply, geoCornerPolygon_apply, hk₁, hk₂,
      geoMarkPosition_evaluation_visit, geoMarkPosition_evaluation_visit]
    rfl
  have hk : k₁ = k₂ := s176_cornerPolygon_inj hn hG hT q hpt
  rw [hk, hk₂] at hk₁
  have hvis : visitOn j b hbj = visitOn j a haj := Sum.inr_injective hk₁
  exact hab (congrArg (fun w : Visit P => w.2.val) hvis).symm

/-! ### The labelled corner: `j = {a, b} ∈ T` the corner, `u = {a, c}`, `v = {b, c}` retained -/

variable {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hX : ExactTriangleVisitOrders P P' a b c hs)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)

include hab hac hbc hX hj hu in
/-- no visit between `u` and `j` on `a` (both orders) -/
theorem s176_nb_a (w : Visit P) (hw : w.2.val = a) :
    ¬ (visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn j a (s176_mem_left hj))) ∧
    ¬ (visitParameter (visitOn j a (s176_mem_left hj)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn u a (s176_mem_left hu))) :=
  s176_no_visit_between hs hac hab hbc.symm
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    hu hj _ _ w hw

include hab hac hbc hX hj hv in
/-- no visit between `j` and `v` on `b` (both orders) -/
theorem s176_nb_b (w : Visit P) (hw : w.2.val = b) :
    ¬ (visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn v b (s176_mem_left hv))) ∧
    ¬ (visitParameter (visitOn v b (s176_mem_left hv)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn j b (s176_mem_right hj))) :=
  s176_no_visit_between hs hab.symm hbc hac
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    (s176_pair_comm' hj) hv _ _ w hw

include hab hac hbc hX hu hv in
/-- no visit between `u` and `v` on `c` (both orders) -/
theorem s176_nb_c (w : Visit P) (hw : w.2.val = c) :
    ¬ (visitParameter (visitOn u c (s176_mem_right hu)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧
        visitParameter w < visitParameter (visitOn u c (s176_mem_right hu))) :=
  s176_no_visit_between hs hac.symm hbc.symm hab
    (gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX)
    (s176_pair_comm' hu) (s176_pair_comm' hv) _ _ w hw

include hG in
/-- distinct crossings on one edge have distinct visit parameters -/
theorem s176_param_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ : ZMod n} (hx : ℓ ∈ x.val) (hy : ℓ ∈ y.val) :
    visitParameter (visitOn x ℓ hx) ≠ visitParameter (visitOn y ℓ hy) :=
  gu2_param_ne_of_xPair_ne hG hxy hx hy

include hn hT hab hac hbc hX hj hu hv hjT huq hvq in
/-- **Cyclicity of the corner from retention**: `u` before `j` on `a` iff `j` before `v` on `b` —
otherwise both visits of `j` would be corners of `q` at one point (`s176_no_two_corners`). -/
theorem s176_cyclic :
    visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj)) ↔
      visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)) := by
  have huT : u ∉ T := ((mem_geoCarrierCrossings hG.cg T q u).mp huq).1
  have hvT : v ∉ T := ((mem_geoCarrierCrossings hG.cg T q v).mp hvq).1
  have hju : j ≠ u := s176_ne_of_supports hj hu hac hbc
  have hjv : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
  have hqu : geoOwner hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) = q :=
    s176_owner_of_retained hG q huq _ rfl
  have hqv : geoOwner hG.cg T (Sum.inr (visitOn v b (s176_mem_left hv))) = q :=
    s176_owner_of_retained hG q hvq _ rfl
  have htwin_a : visitTwin (visitOn j a (s176_mem_left hj)) = visitOn j b (s176_mem_right hj) :=
    s176_visitTwin_eq hj hab _ _
  have htwin_b : visitTwin (visitOn j b (s176_mem_right hj)) = visitOn j a (s176_mem_left hj) :=
    s176_visitTwin_eq (s176_pair_comm' hj) hab.symm _ _
  constructor
  · intro hlt_a
    by_contra hnot
    have hlt_b : visitParameter (visitOn v b (s176_mem_left hv)) <
        visitParameter (visitOn j b (s176_mem_right hj)) :=
      lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hjv.symm _ _)
    -- `ρ (u, a) = (j, a)` and `ρ (v, b) = (j, b)`: both corners owned by `q`
    have h1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) =
        Sum.inr (visitOn j a (s176_mem_left hj)) :=
      s176_succ_of_lt hn hG _ _ huT hlt_a (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).1)
    have h2 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn v b (s176_mem_left hv))) =
        Sum.inr (visitOn j b (s176_mem_right hj)) :=
      s176_succ_of_lt hn hG _ _ hvT hlt_b (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).2)
    exact s176_no_two_corners hn hG hT q hjT hab _ _
      (by rw [← h1, geoOwner_successor]; exact hqu)
      (by rw [← h2, geoOwner_successor]; exact hqv)
  · intro hlt_b
    by_contra hnot
    have hlt_a : visitParameter (visitOn j a (s176_mem_left hj)) <
        visitParameter (visitOn u a (s176_mem_left hu)) :=
      lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hju _ _)
    -- `ρ (j, a) = (v, b)` and `ρ (j, b) = (u, a)`: both corners owned by `q`
    have h1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn j a (s176_mem_left hj))) =
        Sum.inr (visitOn v b (s176_mem_left hv)) := by
      rw [geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_a]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_b
        (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).1)
    have h2 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn j b (s176_mem_right hj))) =
        Sum.inr (visitOn u a (s176_mem_left hu)) := by
      rw [geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_b]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_a
        (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).2)
    exact s176_no_two_corners hn hG hT q hjT hab _ _
      (by rw [← geoOwner_successor, h1]; exact hqv)
      (by rw [← geoOwner_successor, h2]; exact hqu)

include hn hab hac hbc hX hj hu hv hjT huq hvq in
/-- **The corner, case 1 (`u` before `j` on `a`)**: the corner after the carrier edge `kA` of `(u, a)` is
the visit `(j, a)`; the next edge `kA + 1` carries `(v, b)`; the two `c`-visits share one carrier edge. -/
theorem s176_corner_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    geoCornerMark hG.cg T q (G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1) =
        Sum.inr (visitOn j a (s176_mem_left hj)) ∧
    geoCornerPolygon hG.cg T q (G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1) =
        crossingPoint j ∧
    G11_carrierEdge hn hG hT q (visitOn v b (s176_mem_left hv)) hvq =
        G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1 ∧
    G11_carrierEdge hn hG hT q (visitOn v c (s176_mem_right hv)) hvq =
        G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq := by
  have huT : u ∉ T := ((mem_geoCarrierCrossings hG.cg T q u).mp huq).1
  have hlt_b := (s176_cyclic hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq).mp hlt_a
  have htwin_a : visitTwin (visitOn j a (s176_mem_left hj)) = visitOn j b (s176_mem_right hj) :=
    s176_visitTwin_eq hj hab _ _
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  -- `ρ (u, a) = (j, a)`
  have hsucc1 : geoSmoothingSuccessor hG.cg T (Sum.inr (visitOn u a (s176_mem_left hu))) =
      Sum.inr (visitOn j a (s176_mem_left hj)) :=
    s176_succ_of_lt hn hG _ _ huT hlt_a (fun w hw => (s176_nb_a hs hab hac hbc hX hj hu w hw).1)
  -- the corner `c_{kA+1} = (j, a)`
  obtain ⟨r, -, hρ, hb, -, -⟩ := gu1_carrierEdge_block hn hG hT q (visitOn u a (s176_mem_left hu)) huq
  have hcorner : geoCornerMark hG.cg T q (kA + 1) = Sum.inr (visitOn j a (s176_mem_left hj)) :=
    s176_next_corner hn hG hT q hρ hb (by exact hjT) hsucc1
  refine ⟨hcorner, ?_, ?_, ?_⟩
  · rw [geoCornerPolygon_apply, hcorner, geoMarkPosition_evaluation_visit]
    rfl
  · -- `ρ (j, a) = (v, b)`, on the outgoing edge `b` of the corner
    have hsucc2 : geoSmoothingSuccessor hG.cg T (geoCornerMark hG.cg T q (kA + 1)) =
        Sum.inr (visitOn v b (s176_mem_left hv)) := by
      rw [hcorner, geoSmoothingSuccessor_visit_of_mem hG.cg T _ hjT, htwin_a]
      exact gu1_markSuccessor_eq_of_adjacent hn hG.cg rfl hlt_b
        (fun w hw => (s176_nb_b hs hab hac hbc hX hj hv w hw).1)
    have hedge : (visitOn v b (s176_mem_left hv)).2.val =
        (geoOutSlot hG.cg T (geoCornerMark hG.cg T q (kA + 1))).1 := by
      rw [hcorner, geoOutSlot_selected hG.cg T _ hjT, htwin_a]
      rfl
    exact s176_carrierEdge_of_succ hn hG hT q hvq hsucc2 hedge
  · exact G11_carrierEdge_eq_of_adjacent hn hG hT q hvq huq rfl
      (fun w hw => ⟨(s176_nb_c hs hab hac hbc hX hu hv w hw).2, (s176_nb_c hs hab hac hbc hX hu hv w hw).1⟩)

end S176Corner

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

section S176Clear

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P)
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T)

/-- the crossing point of the lift of a retained crossing is its crossing point -/
theorem s176_liftPoint {x : Crossing P} (hx : x ∈ geoCarrierCrossings hG.cg T q) :
    (geoCarrierShadow hn hG hT q).crossingPoint ((geoCarrierCrossingEquiv hn hG hT q).symm ⟨x, hx⟩) =
      crossingPoint x := by
  rw [← crossingPoint_geoCarrierCrossingEquiv, Equiv.apply_symm_apply]

variable {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  (hX : ExactTriangleVisitOrders P P' a b c hs)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hG.cg T q) (hvq : v ∈ geoCarrierCrossings hG.cg T q)
  (hQT : ∀ x ∈ T, x ≠ j → ∃ ℓ ∈ x.val, ℓ ≠ a ∧ ℓ ≠ b ∧ ℓ ≠ c)

omit [NeZero n] in
include hj in
theorem s176_hcab : IsCrossing P {a, b} := by rw [← hj]; exact j.2
omit [NeZero n] in
include hu in
theorem s176_hcac : IsCrossing P {a, c} := by rw [← hu]; exact u.2
omit [NeZero n] in
include hv in
theorem s176_hcbc : IsCrossing P {b, c} := by rw [← hv]; exact v.2

omit [NeZero n] in
include hj in
theorem s176_xPair_j : xPair (s176_hcab hj) = j := Subtype.ext hj.symm
omit [NeZero n] in
include hu in
theorem s176_xPair_u : xPair (s176_hcac hu) = u := Subtype.ext hu.symm
omit [NeZero n] in
include hv in
theorem s176_xPair_v : xPair (s176_hcbc hv) = v := Subtype.ext hv.symm

include hn hT hab hac hbc hX hj hu hv hjT hQT in
/-- **The only corner of the carrier inside the closed triangle is the `j`-corner** (case 1 data:
`c_{kA+1} = (j, a)`): a corner is a vertex of `P` (off the triangle, `gu2_clear`), or a `T`-visit — of `j`
(then it is `(j, a)`, or `(j, b)` and two corners would sit at one point), or of a foreign crossing whose
foreign edge misses the closed triangle (`gu2_clear_closed`). -/
theorem s176_corner_mem_K {kA : ZMod (geoCornerCount hG.cg T q)}
    (hcorner : geoCornerMark hG.cg T q (kA + 1) = Sum.inr (visitOn j a (s176_mem_left hj)))
    (i : ZMod (geoCornerCount hG.cg T q))
    (hi : geoCornerPolygon hG.cg T q i ∈
      convexHull ℝ {crossingPoint j, crossingPoint u, crossingPoint v}) : i = kA + 1 := by
  have hcl := gu2_clear hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  have hclosed := gu2_clear_closed hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv] at hcl hclosed
  rw [geoCornerPolygon_apply] at hi
  have hcorn := isTrueCorner_geoCornerMark hG.cg T q i
  rcases hmark : geoCornerMark hG.cg T q i with vtx | w
  · rw [hmark, geoMarkPosition_evaluation_vertex] at hi
    exact (hcl.2 vtx hi).elim
  · rw [hmark, geoMarkPosition_evaluation_visit] at hi
    rw [hmark, isTrueCorner_visit] at hcorn
    by_cases hwj : w.1 = j
    · rcases visit_eq_or_twin (visitOn j a (s176_mem_left hj)) w hwj with hw | hw
      · apply geoCornerMark_injective hG.cg T q
        rw [hmark, hw, hcorner]
      · exfalso
        rw [s176_visitTwin_eq hj hab _ (s176_mem_right hj)] at hw
        have h1 : geoOwner hG.cg T (Sum.inr (visitOn j a (s176_mem_left hj))) = q := by
          rw [← hcorner]; exact s176_owner_cornerMark hG q (kA + 1)
        have h2 : geoOwner hG.cg T (Sum.inr (visitOn j b (s176_mem_right hj))) = q := by
          rw [← hw, ← hmark]; exact s176_owner_cornerMark hG q i
        exact s176_no_two_corners hn hG hT q hjT hab _ _ h1 h2
    · obtain ⟨ℓ, hℓw, hℓa, hℓb, hℓc⟩ := hQT w.1 hcorn hwj
      exact (hclosed ℓ hℓa hℓb hℓc _ (crossingPoint_mem w.1 ℓ hℓw) hi).elim

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **Clearance of the closed contact triangle (case 1)**: every edge of the corner polygon other than
`e_in = kA`, `e_out = kA + 1` and `s = kC` misses the closed triangle `conv{pt j, pt u, pt v}`.  A carrier
edge inside `a` (resp. `b`, `c`) meeting the triangle meets it on the side `[pt j, pt u] ⊆ e_in` (resp.
`[pt j, pt v] ⊆ e_out`, `[pt u, pt v] ⊆ s`); two parallel carrier edges meeting share a corner
(`gu2_parallel_meet_vertex`), which is the `j`-corner (`s176_corner_mem_K`), and an edge through the
`j`-corner is incident to it (`geoCornerPolygon_tail_off`) — i.e. it is `e_in` or `e_out`.  Foreign carrier
edges lie inside foreign edges of `P` (`gu2_clear_closed`). -/
theorem s176_clear_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    ∀ h : ZMod (geoCornerCount hG.cg T q),
      h ≠ G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq →
      h ≠ G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq + 1 →
      h ≠ G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h,
        x ∉ convexHull ℝ {crossingPoint j, crossingPoint u, crossingPoint v} := by
  obtain ⟨hcorner, hpt, hkB, hkC⟩ := s176_corner_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hlt_a
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  set kC := G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq with hkC0
  intro h hhA hhB hhC x hx hxK
  have hclosed := gu2_clear_closed hG hs hab hac hbc (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hX
  rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv] at hclosed
  have hxK' : x ∈ convexHull ℝ {crossingPoint (xPair (s176_hcab hj)), crossingPoint (xPair (s176_hcac hu)),
      crossingPoint (xPair (s176_hcbc hv))} := by
    rw [s176_xPair_j hj, s176_xPair_u hu, s176_xPair_v hv]; exact hxK
  have hx₀ := gu2_edgeSegment_sub hn hG hT q h hx
  obtain ⟨c₀, hc₀, hedge₀⟩ := geoCornerPolygon_edge_smul hn hG.cg hT q h
  -- a common point with another carrier edge is a corner, hence the `j`-corner, hence `h ∈ {kA, kA+1}`
  have hnotvertex : ∀ i, x = geoCornerPolygon hG.cg T q i → False := by
    intro i hxi
    have hi := s176_corner_mem_K hn hG hs hT q hab hac hbc hX hj hu hv hjT hQT hcorner i (hxi ▸ hxK)
    rw [hi] at hxi
    have hmem : geoCornerPolygon hG.cg T q (kA + 1) ∈ edgeSegment (geoCornerPolygon hG.cg T q) h :=
      hxi ▸ hx
    have hinc : incident (kA + 1) h := by
      by_contra hn'
      exact geoCornerPolygon_tail_off hn hG hT q (kA + 1) h hn' hmem
    rcases hinc with h1 | h1
    · exact hhA (by rw [h1, add_sub_cancel_right])
    · exact hhB h1
  have hspecA := G11_carrierEdge_spec hn hG hT q (visitOn u a (s176_mem_left hu)) huq
  have hspecB := G11_carrierEdge_spec hn hG hT q (visitOn v b (s176_mem_left hv)) hvq
  have hspecC := G11_carrierEdge_spec hn hG hT q (visitOn u c (s176_mem_right hu)) huq
  have hspecC' := G11_carrierEdge_spec hn hG hT q (visitOn v c (s176_mem_right hv)) hvq
  rw [hkB] at hspecB
  rw [hkC] at hspecC'
  set lab := (geoOutSlot hG.cg T (geoCornerMark hG.cg T q h)).1 with hlab
  by_cases hla : lab = a
  · rw [hla] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_e_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_j hj, s176_xPair_u hu] at hseg
    have hA : crossingPoint u ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := hspecA.1
    have hB : crossingPoint j ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := by
      rw [← hpt]
      exact ⟨1, zero_le_one, le_rfl, by rw [edgePoint_one]⟩
    have hxkA : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) kA := gu2_edgeSegment_convex hB hA hseg
    obtain ⟨cA, -, hedgeA⟩ := hspecA.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhA hedge₀ hedgeA hx hxkA
    exact hnotvertex i hi
  by_cases hlb : lab = b
  · rw [hlb] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_f_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_j hj, s176_xPair_v hv] at hseg
    have hA : crossingPoint v ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := hspecB.1
    have hB : crossingPoint j ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := by
      rw [← hpt]
      exact ⟨0, le_rfl, zero_le_one, by rw [edgePoint_zero]⟩
    have hxkB : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) (kA + 1) := gu2_edgeSegment_convex hB hA hseg
    obtain ⟨cB, -, hedgeB⟩ := hspecB.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhB hedge₀ hedgeB hx hxkB
    exact hnotvertex i hi
  by_cases hlc : lab = c
  · rw [hlc] at hx₀ hedge₀
    obtain ⟨t, -, -, hxt⟩ := hx₀
    have hseg := gu2_line_g_mem_segment hG (s176_hcab hj) (s176_hcac hu) (s176_hcbc hv) hxK' hxt
    rw [s176_xPair_u hu, s176_xPair_v hv] at hseg
    have hA : crossingPoint u ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := hspecC.1
    have hB : crossingPoint v ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := hspecC'.1
    have hxkC : x ∈ edgeSegment (geoCornerPolygon hG.cg T q) kC := gu2_edgeSegment_convex hA hB hseg
    obtain ⟨cC, -, hedgeC⟩ := hspecC.2
    obtain ⟨i, hi⟩ := gu2_parallel_meet_vertex hn hG hT q hhC hedge₀ hedgeC hx hxkC
    exact hnotvertex i hi
  exact hclosed lab hla hlb hlc x hx₀ hxK

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **The carrier corner site, case 1** (`u` before `j` on `a`): `e_in = kA` carries `u`, `e_out = kA + 1`
carries `v`, `s = kC`; `y₁ = lift u`, `y₂ = lift v`. -/
theorem s176_cornerSite_case1
    (hlt_a : visitParameter (visitOn u a (s176_mem_left hu)) < visitParameter (visitOn j a (s176_mem_left hj))) :
    ∃ Tsite : s176_CornerSite (geoPositiveLift hn hG hT q),
      Tsite.i = (0 : Fin 1) ∧ Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ ∧
        Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ := by
  obtain ⟨hcorner, hpt, hkB, hkC⟩ := s176_corner_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hlt_a
  have hclear := s176_clear_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hQT hlt_a
  set kA := G11_carrierEdge hn hG hT q (visitOn u a (s176_mem_left hu)) huq with hkA
  set kC := G11_carrierEdge hn hG hT q (visitOn u c (s176_mem_right hu)) huq with hkC0
  set liftU := (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ with hliftU
  set liftV := (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ with hliftV
  have hyU : liftU.val = {(⟨(0 : Fin 1), kA⟩ : (geoCarrierShadow hn hG hT q).Strand), ⟨(0 : Fin 1), kC⟩} := by
    have h0 : liftU.val = {(⟨(0 : Fin 1), kA⟩ : (geoCarrierShadow hn hG hT q).Strand),
        ⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitTwin (visitOn u a (s176_mem_left hu)))
          (by rw [visitTwin_crossing]; exact huq)⟩} :=
      s176_lift_val hn hG hT q (visitOn u a (s176_mem_left hu)) huq
    rw [gu2_carrierEdge_congr hn hG hT q (s176_visitTwin_eq hu hac _ (s176_mem_right hu)) _ huq] at h0
    exact h0
  have hyV : liftV.val = {(⟨(0 : Fin 1), kA + 1⟩ : (geoCarrierShadow hn hG hT q).Strand), ⟨(0 : Fin 1), kC⟩} := by
    have h0 : liftV.val = {(⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitOn v b (s176_mem_left hv)) hvq⟩ :
        (geoCarrierShadow hn hG hT q).Strand),
        ⟨(0 : Fin 1), G11_carrierEdge hn hG hT q (visitTwin (visitOn v b (s176_mem_left hv)))
          (by rw [visitTwin_crossing]; exact hvq)⟩} :=
      s176_lift_val hn hG hT q (visitOn v b (s176_mem_left hv)) hvq
    rw [gu2_carrierEdge_congr hn hG hT q (s176_visitTwin_eq hv hbc _ (s176_mem_right hv)) _ hvq, hkB, hkC] at h0
    exact h0
  have hclear' : ∀ h : ZMod (geoCornerCount hG.cg T q), h ≠ kA → h ≠ kA + 1 → h ≠ kC →
      ∀ x ∈ edgeSegment (geoCornerPolygon hG.cg T q) h,
        x ∉ convexHull ℝ {crossingPoint u, crossingPoint j, crossingPoint v} := by
    intro h hA hB hC x hx
    rw [Set.insert_comm]
    exact hclear h hA hB hC x hx
  have hcl'' := s176_clear_of_indices hn hG hT q kA (kA + 1) kC _ hclear'
  refine ⟨⟨(0 : Fin 1), kA, ?_, ⟨(0 : Fin 1), kC⟩, liftU, liftV, hyU, hyV,
    geoPositiveLift_isPositive hn hG hT q _, geoPositiveLift_isPositive hn hG hT q _, ?_⟩, rfl, rfl, rfl⟩
  · exact s176_four_le_of_crossing (geoPositiveLift hn hG hT q) (0 : Fin 1) kA kC liftU hyU
  · intro w hwA hwB hwC
    have hD := hcl'' w hwA hwB hwC
    convert hD using 2
    all_goals first
      | rfl
      | (show ({(geoCarrierShadow hn hG hT q).crossingPoint liftU, geoCornerPolygon hG.cg T q (kA + 1),
            (geoCarrierShadow hn hG hT q).crossingPoint liftV} : Set Plane) = _
         rw [hliftU, hliftV, s176_liftPoint hn hG hT q huq, s176_liftPoint hn hG hT q hvq, hpt])

include hn hab hac hbc hX hj hu hv hjT huq hvq hQT in
/-- **The carrier corner site of row 176** (`j ∈ T` the corner, `u = {a, c}`, `v = {b, c}` retained,
every other `T`-crossing foreign): a `s176_CornerSite` on the positive lift whose two crossings are the
lifts of `u` and `v`, in the order fixed by the orientation of the corner (`s176_cyclic`). -/
theorem s176_cornerSite_of_carrier :
    ∃ Tsite : s176_CornerSite (geoPositiveLift hn hG hT q), Tsite.i = (0 : Fin 1) ∧
      ((Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩ ∧
          Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩) ∨
        (Tsite.y₁ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨v, hvq⟩ ∧
          Tsite.y₂ = (geoCarrierCrossingEquiv hn hG hT q).symm ⟨u, huq⟩)) := by
  have hju : j ≠ u := s176_ne_of_supports hj hu hac hbc
  rcases lt_or_gt_of_ne (s176_param_ne hG hju.symm (s176_mem_left hu) (s176_mem_left hj)) with hlt | hgt
  · obtain ⟨Tsite, hi, h1, h2⟩ :=
      s176_cornerSite_case1 hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq hQT hlt
    exact ⟨Tsite, hi, Or.inl ⟨h1, h2⟩⟩
  · -- case 2: apply case 1 to the relabelled data `(b, a, c)`, `(j, v, u)`
    have hX' : ExactTriangleVisitOrders P P' b a c hs :=
      gu2_exact_of_eq hs (by ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto) hX
    have hQT' : ∀ x ∈ T, x ≠ j → ∃ ℓ ∈ x.val, ℓ ≠ b ∧ ℓ ≠ a ∧ ℓ ≠ c := by
      intro x hx hxj
      obtain ⟨ℓ, hℓ, h1, h2, h3⟩ := hQT x hx hxj
      exact ⟨ℓ, hℓ, h2, h1, h3⟩
    have hlt_b : visitParameter (visitOn v b (s176_mem_left hv)) <
        visitParameter (visitOn j b (s176_mem_right hj)) := by
      have hjv : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
      have hcyc := s176_cyclic hn hG hs hT q hab hac hbc hX hj hu hv hjT huq hvq
      have hnot : ¬ visitParameter (visitOn j b (s176_mem_right hj)) <
          visitParameter (visitOn v b (s176_mem_left hv)) := fun h => lt_asymm hgt (hcyc.mpr h)
      exact lt_of_le_of_ne (not_lt.mp hnot) (s176_param_ne hG hjv.symm _ _)
    obtain ⟨Tsite, hi, h1, h2⟩ :=
      s176_cornerSite_case1 hn hG hs hT q hab.symm hbc hac hX' (s176_pair_comm' hj) hv hu hjT hvq huq hQT' hlt_b
    exact ⟨Tsite, hi, Or.inr ⟨h1, h2⟩⟩

end S176Clear

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §D. The event-level site of row 176 (the binders of `est_port_relation`) -/

section S176Event

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- a crossing outside the triangle has a label outside `{e, f, g}` -/
theorem s176_foreign_label {P : LabelledTuple n} (x : Crossing P) (hx : x.val ∉ triangleSupports e f g) :
    ∃ ℓ ∈ x.val, ℓ ∉ ({e, f, g} : Finset (ZMod n)) := by
  classical
  obtain ⟨i, hi⟩ : x.val.Nonempty := Finset.card_pos.mp (by rw [crossing_card_two]; norm_num)
  obtain ⟨j₀, hij, hx₀⟩ := crossing_support_partner x i hi
  by_contra hcon
  have hcon' : ∀ ℓ ∈ x.val, ℓ ∈ ({e, f, g} : Finset (ZMod n)) := fun ℓ hℓ =>
    by_contra fun h => hcon ⟨ℓ, hℓ, h⟩
  clear hcon
  have hcon := hcon'
  apply hx
  rw [hx₀]
  have hi' := hcon i hi
  have hj' := hcon j₀ (by rw [hx₀]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  simp only [Finset.mem_insert, Finset.mem_singleton] at hi' hj'
  exact gu2_pair_mem_triangleSupports hij hi' hj'

/-- **The labelled event-level core**: with the labels `a` (shared by `j, u`), `b` (shared by `j, v`),
`c` (shared by `u, v`) fixed, the retained unselected crossing `u'` of the affected carrier `q₀'` forces
the third crossing `v'` to be retained too (`est_retained_u_iff` both ways: the two `c`-visits are
`ρ`-adjacent on `H`), and the carrier corner site exists on `carrierDiagram q₀'` with `{y₁, y₂} =
{lift u', lift v'}`. -/
theorem s176_event_site_core (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (habc : ({a, b, c} : Finset (ZMod n)) = {e, f, g})
    (hjab : j.val = {a, b}) (huac : u.val = {a, c}) {v : Crossing (E.curve t)} (hvbc : v.val = {b, c})
    (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    ∃ (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  have hS' := est_S'_ind hL ht ht' hop hs hQ hfull hj
  -- labels
  have hcu : c ∈ u.val := s176_mem_right huac
  have hcv : c ∈ v.val := s176_mem_right hvbc
  have hcj : c ∉ j.val := by
    rw [hjab, Finset.mem_insert, Finset.mem_singleton]
    rintro (h | h)
    · exact hac h.symm
    · exact hbc h.symm
  -- the H-side geometry: `u, v ∉ S`, the two `c`-visits are `ρ_S`-adjacent, so they have one owner
  have hQout : ∀ x ∈ Q, x.val ∉ triangleSupports e f g := fun x hxQ h =>
    Finset.disjoint_left.mp ((F1.mem_outsideSupports _ e f g Q).mp hQ).2 hxQ
      ((F1.mem_triangleCrossings e f g x).mpr h)
  have huS : u ∉ Q ∪ {j} := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hQout u h hu
    · exact hju (Finset.mem_singleton.mp h).symm
  have hvS : v ∉ Q ∪ {j} := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact hQout v h hv
    · exact hjv (Finset.mem_singleton.mp h).symm
  have hGH : CarrierGeometry (E.curve t) := CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn)
  have hXH : ExactTriangleVisitOrders (E.curve t) (E.curve t') c a b hs :=
    gu2_exact_of_eq hs (by rw [← habc]; ext z; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto)
      (hL.gauss_words t t' ht ht' hop hs)
  have hnbH := s176_no_visit_between hs hac.symm hbc.symm hab hXH (s176_pair_comm' huac) (s176_pair_comm' hvbc) hcu hcv
  have howner_u : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hcu hcj q).mp hu'
  have howner_v : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v c hcv)) = q := by
    rcases lt_or_gt_of_ne (s176_param_ne hGH huv hcu hcv) with hlt | hgt
    · have hsucc : geoSmoothingSuccessor (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u c hcu)) =
          Sum.inr (visitOn v c hcv) :=
        s176_succ_of_lt hn hGH hcu hcv huS hlt (fun w hw => (hnbH w hw).1)
      rw [← hsucc, geoOwner_successor]; exact howner_u
    · have hsucc : geoSmoothingSuccessor (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn v c hcv)) =
          Sum.inr (visitOn u c hcu) :=
        s176_succ_of_lt hn hGH hcv hcu hvS hgt (fun w hw => (hnbH w hw).2)
      rw [← geoOwner_successor, hsucc]; exact howner_u
  have hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv W q) :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hv hjv hcv hcj q).mpr howner_v
  refine ⟨hv', ?_⟩
  -- the L side
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
  have hQT : ∀ x ∈ transportSupport hs (Q ∪ {j}), x ≠ crossingTransport hs j →
      ∃ ℓ ∈ x.val, ℓ ≠ a ∧ ℓ ≠ b ∧ ℓ ≠ c := by
    intro x hx hxj
    obtain ⟨x₀, rfl⟩ := (crossingTransport hs).surjective x
    rw [mem_transportSupport_iff] at hx
    have hx₀j : x₀ ≠ j := fun h => hxj (by rw [h])
    have hx₀Q : x₀ ∈ Q := by
      rcases Finset.mem_union.mp hx with h | h
      · exact h
      · exact absurd (Finset.mem_singleton.mp h) hx₀j
    obtain ⟨ℓ, hℓ, hℓn⟩ := s176_foreign_label x₀ (hQout x₀ hx₀Q)
    rw [← habc, Finset.mem_insert, Finset.mem_insert, Finset.mem_singleton, not_or, not_or] at hℓn
    exact ⟨ℓ, hℓ, hℓn.1, hℓn.2.1, hℓn.2.2⟩
  obtain ⟨Tsite, -, hcases⟩ := s176_cornerSite_of_carrier hn (CarrierGeometry.ofDiagrammatic
    ((genericAt E t' ht'.1).diagrammatic hn)) hs' hT (GT_carrierEquiv W q) hab hac hbc hXL
    (j := crossingTransport hs j) (u := crossingTransport hs u) (v := crossingTransport hs v)
    hjab huac hvbc hjT hu' hv' hQT
  exact ⟨Tsite, hcases⟩

/-- **The site of row 176 at the event level** — the hypotheses are exactly the binders of
`est_port_relation` together with the retained unselected crossing `u` of the `∃`-premise: a corner site
on `D₊ = carrierDiagram q₀'` one of whose crossings is the lift `y` of `u'`.  Six relabellings of
`s176_event_site_core` (`GT_tri_cases` for `j` and `u`). -/
theorem s176_site_of_event (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    ∃ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂ := by
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
      ∃ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
          (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
        est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
        est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂ := by
    intro a b c hab hac hbc habc hjab huac v hvbc hv hjv huv
    obtain ⟨hv', Tsite, hc⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
      hab hac hbc habc hjab huac hvbc hv hjv huv
    refine ⟨Tsite, ?_⟩
    rcases hc with ⟨h1, -⟩ | ⟨-, h2⟩
    · exact Or.inl h1.symm
    · exact Or.inr h2.symm
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
  · -- j = x_ef, u = x_eg, v = x_fg: a = e, b = f, c = g
    exact key hef heg hfg rfl rfl rfl (v := xPair hfg') rfl h3 n13 n23
  · -- j = x_ef, u = x_fg, v = x_eg: a = f, b = e, c = g
    exact key hef.symm hfg heg p_feg (Finset.pair_comm e f) rfl
      (v := xPair heg') rfl h2 n12 n23.symm
  · -- j = x_eg, u = x_ef, v = x_fg: a = e, b = g, c = f
    exact key heg hef hfg.symm p_egf rfl rfl (v := xPair hfg')
      (Finset.pair_comm f g) h3 n23 n13
  · exact absurd rfl hju
  · -- j = x_eg, u = x_fg, v = x_ef: a = g, b = e, c = f
    exact key heg.symm hfg.symm hef p_gef (Finset.pair_comm e g)
      (Finset.pair_comm f g) (v := xPair hef') rfl h1 n12.symm n13.symm
  · -- j = x_fg, u = x_ef, v = x_eg: a = f, b = g, c = e
    exact key hfg hef.symm heg.symm p_fge rfl (Finset.pair_comm e f)
      (v := xPair heg') (Finset.pair_comm e g) h2 n23.symm n12
  · -- j = x_fg, u = x_eg, v = x_ef: a = g, b = f, c = e
    exact key hfg.symm heg.symm hef.symm p_gfe (Finset.pair_comm f g)
      (Finset.pair_comm e g) (v := xPair hef') (Finset.pair_comm e f) h1 n13.symm n12.symm
  · exact absurd rfl hju

end S176Event

/-! ## §E. The record identification `hrec` (stated), the composition into the weak port and into the
weak interface -/

/-- The reduced record of a bigon is the restriction to the complement of its two crossings. -/
theorem s176_reducedRecord_eq {D : Diagram} (B : BigonData D) {y₁ y₂ : D.Γ.Crossing}
    (h₁ : B.y = y₁) (h₂ : B.z = y₂) :
    B.reducedRecord = D.record.restrictCrossings
      {c | c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)} := by
  subst h₁ h₂; rfl

section S176Compose

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The wall transport of the reduced record (OPEN, consumer bookkeeping ≈ 1.0k lines, PLAN_FINAL §4.3 /
§6 R5)**: for the corner site on `D₊ = carrierDiagram q₀'` switched at `y = lift u'`, the record of
`D₊.switch y` with the four occurrences of `{y₁, y₂} = {lift u', lift v'}` deleted (`Record.restrictCrossings`,
first-return successor) is isomorphic to the record of `D₀ = carrierDiagram q₀`.  Content: the retained
crossings correspond (`est_retained_affected`: `q₀'` retains the transports of `q₀`'s crossings plus `u', v'`),
their visit orders are carried (`GT_Wall.key_lt` on non-triangle visits, as in `est_groupedPoly_eq_of_ne`), the
over bits agree (positive lifts, `switch` only touches `y`, and `y` is deleted), the signs are all `+1`; the
assembly is an `RecordIso` built against `restrictCrossings` (`RecordIso.ofOcc`, MarkedProducts) — the analogue
of `EXT_homfly_wall`'s `recordIsoOfData` with the two deleted crossings.  Stated as the Prop consumed below. -/
def s176_hrec_of_site (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂) →
    Nonempty (RecordIso
      (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
          (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.restrictCrossings
        {c | c ≠ ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
              (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.crossingOf
              (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
                (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).overVisit Tsite.y₁) ∧
             c ≠ ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
              (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).record.crossingOf
              (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).switch
                (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu')).overVisit Tsite.y₂)})
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- **The weak port of row 176 from the site and `hrec`** — (a) `s176_site_of_event` + the frozen leaf
through `s176_CornerSite.exists_bigon_switch₁/₂` + (b) `hrec` + `est_port_weak_of_bigon`. -/
theorem s176_port_weak_of_event (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hrec : s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  obtain ⟨Tsite, hy⟩ := s176_site_of_event hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q
    hu hju hu'
  unfold s176_hrec_of_site at hrec
  have hR' := hrec Tsite hy
  rcases hy with hy | hy
  · rw [hy] at hR' ⊢
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₁
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    exact hR'
  · rw [hy] at hR' ⊢
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₂
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    exact hR'

/-- **The weak interface of row 176 from the site**: given `hrec` and the non-move port data
(`s176_PortDataRest`, U_R176_REPORT §5 items 2–5) for every retained unselected crossing of every affected
carrier, `s176_est_port_relation_weak` holds — hence (`s176_est_ledger_weak`) the row in `RowShape`. -/
theorem s176_est_port_relation_weak_of
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu')
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end S176Compose

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §F. The switch drops out of `hrec`: the reduced record of `D.switch y` at a keep-set missing `y`
is the reduced record of `D` (identity on occurrences), so the record identification of row 176 is a
statement about the two UNSWITCHED positive lifts. -/

/-- two occurrences of one crossing name one record crossing -/
theorem s176_crossingOf_eq_of_fst (D : Diagram) (v w : D.Γ.Visit) (h : v.1 = w.1) :
    D.record.crossingOf v = D.record.crossingOf w := by
  rcases D.eq_or_eq_twin w v h with rfl | rfl
  · rfl
  · rw [← D.record_pair_apply, Record.crossingOf_pair]

/-- a retained occurrence is not at the deleted crossing -/
theorem s176_fst_ne_of_keep (D : Diagram) (x₀ : D.Γ.Crossing) (K : Set D.record.Crossing)
    (hK : D.record.crossingOf (D.overVisit x₀) ∉ K) (w : D.Γ.Visit) (hw : D.record.crossingOf w ∈ K) :
    w.1 ≠ x₀ := by
  intro h
  apply hK
  rw [← s176_crossingOf_eq_of_fst D w (D.overVisit x₀) h]
  exact hw

/-- **Deleting the switched crossing forgets the switch**: for a keep-set `K` not containing the crossing
of `x₀`, the restricted records of `D.switch x₀` and of `D` coincide (identity on circles and
occurrences; the first-return successor and the pairing are literally the same; bits and signs differ
only at the two deleted occurrences — `switch_overBit_of_ne`, `switch_sign_of_ne`). -/
def s176_switchRestrictIso (D : Diagram) (x₀ : D.Γ.Crossing) (K : Set D.record.Crossing)
    (hK : D.record.crossingOf (D.overVisit x₀) ∉ K) :
    RecordIso ((D.switch x₀).record.restrictCrossings K) (D.record.restrictCrossings K) where
  e := Equiv.refl _
  Φ := Equiv.refl _
  comp_eq _ := rfl
  succ_eq _ := rfl
  pair_eq _ := rfl
  bit_eq v := by
    show D.overBit v.1 = (D.switch x₀).overBit v.1
    exact (D.switch_overBit_of_ne x₀ v.1 (s176_fst_ne_of_keep D x₀ K hK v.1 v.2)).symm
  sgn_eq v := by
    show D.sign v.1.1 = (D.switch x₀).sign v.1.1
    exact (Diagram.switch_sign_of_ne D (s176_fst_ne_of_keep D x₀ K hK v.1 v.2)).symm

/-- the keep-set of a bigon on `D.switch y` read on `D` -/
theorem s176_keep_switch_eq (D : Diagram) (y y₁ y₂ : D.Γ.Crossing) :
    ({c | c ≠ (D.switch y).record.crossingOf ((D.switch y).overVisit y₁) ∧
        c ≠ (D.switch y).record.crossingOf ((D.switch y).overVisit y₂)} : Set (D.switch y).record.Crossing) =
      ({c | c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)} :
        Set D.record.Crossing) := by
  ext c
  show c ≠ D.record.crossingOf ((D.switch y).overVisit y₁) ∧ c ≠ D.record.crossingOf ((D.switch y).overVisit y₂) ↔
    c ≠ D.record.crossingOf (D.overVisit y₁) ∧ c ≠ D.record.crossingOf (D.overVisit y₂)
  rw [s176_crossingOf_eq_of_fst D ((D.switch y).overVisit y₁) (D.overVisit y₁) rfl,
    s176_crossingOf_eq_of_fst D ((D.switch y).overVisit y₂) (D.overVisit y₂) rfl]

/-- **`hrec` from the unswitched identification**: if the record of `D₊` with the crossings `y₁, y₂`
deleted is `D₀`'s record, so is the record of `D₊.switch y` with them deleted, for `y ∈ {y₁, y₂}`. -/
theorem s176_hrec_of_unswitched (Dp D₀ : Diagram) (y y₁ y₂ : Dp.Γ.Crossing) (hy : y = y₁ ∨ y = y₂)
    (h : Nonempty (RecordIso (Dp.record.restrictCrossings
      {c | c ≠ Dp.record.crossingOf (Dp.overVisit y₁) ∧ c ≠ Dp.record.crossingOf (Dp.overVisit y₂)}) D₀.record)) :
    Nonempty (RecordIso ((Dp.switch y).record.restrictCrossings
      {c | c ≠ (Dp.switch y).record.crossingOf ((Dp.switch y).overVisit y₁) ∧
           c ≠ (Dp.switch y).record.crossingOf ((Dp.switch y).overVisit y₂)}) D₀.record) := by
  obtain ⟨ι⟩ := h
  rw [s176_keep_switch_eq]
  have hK : Dp.record.crossingOf (Dp.overVisit y) ∉
      ({c | c ≠ Dp.record.crossingOf (Dp.overVisit y₁) ∧ c ≠ Dp.record.crossingOf (Dp.overVisit y₂)} :
        Set Dp.record.Crossing) := by
    rcases hy with rfl | rfl
    · exact fun h => h.1 rfl
    · exact fun h => h.2 rfl
  exact ⟨(s176_switchRestrictIso Dp y _ hK).trans ι⟩

section S176Unswitched

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The record identification of row 176 in its UNSWITCHED form (OPEN, ≈ 1.0k lines, the consumer's wall
transport)**: the record of the positive lift `D₊ = carrierDiagram q₀'` with the two crossings `{y₁, y₂} =
{lift u', lift v'}` of the corner site deleted (`Record.restrictCrossings`, first-return successor) is
isomorphic to the record of `D₀ = carrierDiagram q₀`.  No switch is involved (`s176_hrec_of_unswitched`).
Ingredients: `est_retained_affected` (retained sets), `GT_Wall.key_lt` (visit orders of the non-triangle
visits, as in `est_groupedPoly_eq_of_ne`), positivity (`geoPositiveLift_isPositive`) and
`GT_det_pos_iff_of_sign` (bits), all signs `+1`; assembly against `restrictCrossings` as in
`restrictCrossings_iso_of_recordIso` / `EXT_homfly_wall`. -/
def s176_hrec_unswitched (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
      (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₁ ∨
      est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' = Tsite.y₂) →
    Nonempty (RecordIso
      ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
        {c | c ≠ (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf
              ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).overVisit Tsite.y₁) ∧
             c ≠ (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.crossingOf
              ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
                (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).overVisit Tsite.y₂)})
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- the switched `hrec` of §E from the unswitched one -/
theorem s176_hrec_of_site_of_unswitched (hn : 3 ≤ n) (hL : LocalizationData E e f g δ)
    (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter}
    (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (h : s176_hrec_unswitched hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    s176_hrec_of_site hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' := by
  unfold s176_hrec_unswitched at h
  unfold s176_hrec_of_site
  intro Tsite hy
  exact s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ hy (h Tsite hy)

end S176Unswitched

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §G. The wall transport of the two-crossing-deleted record, modulo the successor clause: the
occurrence bijection and the clauses `comp`, `pair`, `bit`, `sgn` of `s176_hrec_unswitched` are PROVED at
the carrier level; `succ_eq` (the first-return successor against the cyclic order across the wall) is
isolated as the single remaining hypothesis. -/

/-- record crossings of two occurrences differ iff their diagram crossings differ -/
theorem s176_crossingOf_ne_iff (D : Diagram) (v w : D.Γ.Visit) :
    D.record.crossingOf v ≠ D.record.crossingOf w ↔ v.1 ≠ w.1 := by
  constructor
  · intro h hvw
    exact h (s176_crossingOf_eq_of_fst D v w hvw)
  · intro h heq
    apply h
    have hmem : v ∈ (D.record.crossingOf w).1 :=
      (Record.crossingOf_eq_iff D.record v (D.record.crossingOf w)).mp heq
    rcases (Finset.mem_insert.mp hmem) with h1 | h1
    · rw [h1]
    · rw [Finset.mem_singleton] at h1
      rw [h1]
      rfl

section S176Wall

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (hT : GeoIndependent hG.cg T)
  (hT' : GeoIndependent hG'.cg T') (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
  {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q')

/-- the keep-set of row 176 on the L-side lift: everything but the crossings at `u'`, `v'` -/
def s176_wallKeep : Set (geoPositiveLift hn hG' hT' q').record.Crossing :=
  {c | c ≠ (geoPositiveLift hn hG' hT' q').record.crossingOf
        ((geoPositiveLift hn hG' hT' q').overVisit ((geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨u', hu'⟩)) ∧
       c ≠ (geoPositiveLift hn hG' hT' q').record.crossingOf
        ((geoPositiveLift hn hG' hT' q').overVisit ((geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨v', hv'⟩))}

/-- an occurrence of the lift is at the lift of `x` iff its parent crossing is `x` -/
theorem s176_fst_eq_lift_iff (v : (geoPositiveLift hn hG' hT' q').Γ.Visit) {x : Crossing P'}
    (hx : x ∈ geoCarrierCrossings hG'.cg T' q') :
    v.1 = (geoCarrierCrossingEquiv hn hG' hT' q').symm ⟨x, hx⟩ ↔ (CV.liftVisit hn hG' hT' q' v).1 = x := by
  rw [CV.liftVisit_fst]
  show _ ↔ (geoCarrierCrossingEquiv hn hG' hT' q' v.1).1 = x
  constructor
  · intro h
    rw [h, Equiv.apply_symm_apply]
  · intro h
    apply (geoCarrierCrossingEquiv hn hG' hT' q').injective
    rw [Equiv.apply_symm_apply]
    exact Subtype.ext h

variable (hX : geoCarrierCrossings hG'.cg T' q' =
    (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding ∪ {u', v'})
  (hu_not : u' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hv_not : v' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)

include hX hu_not hv_not in
/-- **the retained occurrences are the lifts of the transported crossings of `q`** -/
theorem s176_crossKeep_iff (v : (geoPositiveLift hn hG' hT' q').Γ.Visit) :
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v ↔
      (CV.liftVisit hn hG' hT' q' v).1 ∈ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding := by
  have hmem := CV.liftVisit_mem hn hG' hT' q' v
  rw [hX, Finset.mem_union, Finset.mem_insert, Finset.mem_singleton] at hmem
  show (_ ≠ _ ∧ _ ≠ _) ↔ _
  rw [s176_crossingOf_ne_iff, s176_crossingOf_ne_iff]
  have e1 := (s176_fst_eq_lift_iff hn hG' hT' q' v hu').not
  have e2 := (s176_fst_eq_lift_iff hn hG' hT' q' v hv').not
  constructor
  · rintro ⟨h1, h2⟩
    have h1' := e1.mp h1
    have h2' := e2.mp h2
    rcases hmem with h | h | h
    · exact h
    · exact absurd h h1'
    · exact absurd h h2'
  · intro h
    exact ⟨e1.mpr (fun h1 => hu_not (h1 ▸ h)), e2.mpr (fun h2 => hv_not (h2 ▸ h))⟩

/-- **The occurrence bijection across the wall**: retained occurrences of the L-side lift (not at `u', v'`)
↔ occurrences of the H-side lift, through the parent visits and `visitTransport`. -/
def s176_wallΦ :
    {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
        (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v} ≃
      (geoPositiveLift hn hG hT q).Γ.Visit :=
  ((CV.liftVisitEquiv hn hG' hT' q').subtypeEquiv
      (q := fun w : {w : Visit P' // w.1 ∈ geoCarrierCrossings hG'.cg T' q'} =>
        w.1.1 ∈ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
      (fun v => s176_crossKeep_iff hn hG hG' hs hT' q q' hu' hv' hX hu_not hv_not v)).trans
    ((Equiv.subtypeSubtypeEquivSubtypeInter _ _).trans
      ((Equiv.subtypeEquivRight (fun w : Visit P' =>
          ⟨fun h => h.2, fun h => ⟨by rw [hX]; exact Finset.mem_union_left _ h, h⟩⟩)).trans
        (((visitTransport hs).symm.subtypeEquiv
            (fun w : Visit P' => (Finset.mem_map_equiv (f := crossingTransport hs)))).trans
          (CV.liftVisitEquiv hn hG hT q).symm)))

/-- the parent visit of the image is the transport of the parent visit -/
theorem s176_wallΦ_liftVisit (v : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v) =
      (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) := by
  unfold s176_wallΦ
  rw [Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, Equiv.trans_apply, CV.liftVisit_symm]
  rfl

/-- **The wall transport of the reduced record, modulo the successor clause.**  With the occurrence
bijection `s176_wallΦ`: `comp_eq` (one circle), `pair_eq` (`liftVisit_twin`, `visitTransport_visitTwin`),
`bit_eq` (the divide convention read on the parents, `overBit_eq_true_iff_parent`, and the sign data `hdet`),
`sgn_eq` (all `+1`) are PROVED; `succ_eq` — the first-return successor of the restricted record against the
H-side successor — is the hypothesis `hsucc`, the single remaining obligation of `hrec`. -/
theorem s176_hrec_unswitched_of_succ
    (hdet : ∀ w : Visit P, w.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P w.2.val) (edge P (visitTwin w).2.val) ↔
        0 < det (edge P' w.2.val) (edge P' (visitTwin w).2.val)))
    (hsucc : ∀ v, s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ v) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)) :
    Nonempty (RecordIso
      ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG hT q).record) := by
  set Φ := s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not with hΦ
  have hlift : ∀ v, CV.liftVisit hn hG hT q (Φ v) = (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) :=
    fun v => s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v
  refine ⟨⟨Equiv.refl (Fin 1), Φ, ?_, hsucc, ?_, ?_, ?_⟩⟩
  · intro v
    apply Fin.ext
    have h1 := ((geoPositiveLift hn hG hT q).compOf (Φ v)).isLt
    have h2 := ((geoPositiveLift hn hG' hT' q').compOf v.1).isLt
    change _ < 1 at h1 h2
    change ((geoPositiveLift hn hG hT q).compOf (Φ v)).val = ((geoPositiveLift hn hG' hT' q').compOf v.1).val
    omega
  · intro v
    apply CV.liftVisit_injective hn hG hT q
    have h1 := hlift (((geoPositiveLift hn hG' hT' q').record.restrictCrossings
      (s176_wallKeep hn hG' hT' q' hu' hv')).pair v)
    have h2 := hlift v
    refine h1.trans ?_
    change (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' ((geoPositiveLift hn hG' hT' q').twin v.1)) =
      CV.liftVisit hn hG hT q ((geoPositiveLift hn hG hT q).twin (Φ v))
    rw [CV.liftVisit_twin, CV.liftVisit_twin, h2]
    exact visitTransport_visitTwin (fun s => (hs s).symm) _
  · intro v
    change (geoPositiveLift hn hG hT q).overBit (Φ v) = (geoPositiveLift hn hG' hT' q').overBit v.1
    have h2 := hlift v
    rw [Bool.eq_iff_iff, CV.overBit_eq_true_iff_parent, CV.overBit_eq_true_iff_parent, h2]
    set w := (visitTransport hs).symm (CV.liftVisit hn hG' hT' q' v.1) with hw
    have hw' : CV.liftVisit hn hG' hT' q' v.1 = visitTransport hs w := by
      rw [hw, Equiv.apply_symm_apply]
    rw [hw', ← visitTransport_visitTwin, visitTransport_edge, visitTransport_edge]
    apply hdet
    rw [← h2]
    exact CV.liftVisit_mem hn hG hT q _
  · intro v
    change (geoPositiveLift hn hG hT q).sign (Φ v).1 = (geoPositiveLift hn hG' hT' q').sign v.1.1
    rw [geoPositiveLift_sign, geoPositiveLift_sign]

end S176Wall

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §H. The event-level closure of the `hrec` chain: the wall data of row 176 (`est_retained_affected`,
`est_not_retained_H`, the sign radius), the record identification for the SPECIFIC deleted crossings
`{lift u', lift v'}` (`s176_hrec_wall`), its reduction to the successor clause (`s176_hrec_wall_of_succ`,
through §G), the site with the identification of its two crossings (`s176_site_of_event'`), and the weak
port from `s176_hrec_wall` (`s176_port_weak_of_event'`). -/

section S176EventWall

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- the retained set of `q₀'` (`est_retained_affected`, with the shared label of `u, v`) -/
theorem s176_hX_event (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    {v : Crossing (E.curve t)} (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v) :
    geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) =
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding ∪
        {crossingTransport hs u, crossingTransport hs v} := by
  obtain ⟨ℓ, hℓu, hℓv⟩ := GT_shared_label hu hv huv
  have hℓj := est_shared_not_mem_third hef heg hfg hj hu hv hju hjv huv hℓu hℓv
  have hq : geoOwner (geomAt E t ht.1) (Q ∪ {j}) (Sum.inr (visitOn u ℓ hℓu)) = q :=
    (est_retained_u_iff hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hju hℓu hℓj q).mp hu'
  exact est_retained_affected hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj hu hv hju hjv huv hℓu hℓv q hq

/-- a triangle crossing is not a transported retained crossing of `q₀` (`est_not_retained_H`) -/
theorem s176_not_mem_map_event {t t' : E.Parameter} (ht : Punctured E δ t)
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {x : Crossing (E.curve t)} (hx : x.val ∈ triangleSupports e f g) :
    crossingTransport hs x ∉
      (geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q).map (crossingTransport hs).toEmbedding := by
  intro h
  rw [Finset.mem_map_equiv, Equiv.symm_apply_apply] at h
  exact est_not_retained_H ht hcomp hQ hfull hj q h hx

/-- the divide signs of the parent visits are carried across the wall (the sign radius) -/
theorem s176_hdet_event (hR : AV_EventRadius E δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (w : Visit (E.curve t)) :
    (0 < det (edge (E.curve t) w.2.val) (edge (E.curve t) (visitTwin w).2.val) ↔
      0 < det (edge (E.curve t') w.2.val) (edge (E.curve t') (visitTwin w).2.val)) :=
  GT_det_pos_iff_of_sign (hR.sign_eq t t' ht ht' _ _
    (by rw [← visit_crossing_val_eq_pair w]; exact w.1.property))

end S176EventWall

section S176HrecWall

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **The record identification of row 176 for the two deleted crossings `lift u', lift v'` (OPEN
modulo `succ_eq`, see `s176_hrec_wall_of_succ`)**: for every third triangle crossing `v` (with `v'` retained
by `q₀'`), the record of the UNSWITCHED lift `D₊` with the crossings at `u', v'` deleted is the record of `D₀`. -/
def s176_hrec_wall (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)}
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) : Prop :=
  ∀ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
    Nonempty (RecordIso
      ((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
        (s176_wallKeep hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
          (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record)

/-- **`s176_hrec_wall` from the successor clause alone** (§G: the occurrence bijection and the clauses
`comp`, `pair`, `bit`, `sgn` are proved; the wall data `hX`, `hu_not`, `hv_not`, `hdet` are the accepted
row-176 facts).  `hsucc` is THE remaining obligation of row 176's move: the first-return successor of the
restricted L-side record corresponds to the H-side successor under `s176_wallΦ`. -/
theorem s176_hrec_wall_of_succ (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hsucc : ∀ (v : Crossing (E.curve t)) (hv : v.val ∈ triangleSupports e f g) (hjv : j ≠ v) (huv : u ≠ v)
      (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      ∀ w, s176_wallΦ hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
          (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs
          (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj))
          (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)) q
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
          (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
          (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
          (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
          (((CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
            (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).record.restrictCrossings
            (s176_wallKeep hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
              (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
              (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv')).succ w) =
        (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q).record.succ
          (s176_wallΦ hn (CarrierGeometry.ofDiagrammatic ((genericAt E t ht.1).diagrammatic hn))
            (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn)) hs
            (CV.geoIndependent_of_mem_Ind _ (est_S_ind ht.1 hQ hfull hj))
            (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)) q
            (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
            (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
            (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
            (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv) w)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' := by
  intro v hv hjv huv hv'
  exact s176_hrec_unswitched_of_succ hn _ _ hs _ _ q _ hu' hv'
    (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
    (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
    (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
    (fun w _ => s176_hdet_event hR ht ht' w)
    (hsucc v hv hjv huv hv')

/-- **The site with its two crossings identified**: `s176_site_of_event` strengthened by the third
crossing `v`, its retention `hv'`, and `{Tsite.y₁, Tsite.y₂} = {lift u', lift v'}`. -/
theorem s176_site_of_event' (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    ∃ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
      (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
      (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
        Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
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
      ∃ (v : Crossing (E.curve t)) (_hv : v.val ∈ triangleSupports e f g) (_hjv : j ≠ v) (_huv : u ≠ v)
        (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
        (Tsite : s176_CornerSite (CV.carrierDiagram hn (genericAt E t' ht'.1)
          (est_S'_ind hL ht ht' hop hs hQ hfull hj)
          (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))),
        (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∧
          Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv') ∨
        (Tsite.y₁ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv' ∧
          Tsite.y₂ = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
    intro a b c hab hac hbc habc hjab huac v hvbc hv hjv huv
    obtain ⟨hv', Tsite, hc⟩ := s176_event_site_core hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
      hab hac hbc habc hjab huac hvbc hv hjv huv
    exact ⟨v, hv, hjv, huv, hv', Tsite, hc⟩
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

/-- the keep-set is symmetric in the two deleted crossings -/
theorem s176_wallKeep_comm (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CarrierGeometry P')
    {T' : Finset (Crossing P')} (hT' : GeoIndependent hG'.cg T') (q' : GeoComponent hG'.cg T')
    {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q') :
    s176_wallKeep hn hG' hT' q' hu' hv' = s176_wallKeep hn hG' hT' q' hv' hu' := by
  ext c
  exact and_comm

/-- **The weak port of row 176 from the site and `s176_hrec_wall`** (item (c), with `hrec` in the
specific-crossings form): `s176_site_of_event'` + the frozen leaf + `s176_hrec_of_unswitched` +
`est_port_weak_of_bigon`. -/
theorem s176_port_weak_of_event' (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hrec : s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') := by
  obtain ⟨v, hv, hjv, huv, hv', Tsite, hc⟩ := s176_site_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg'
    hcomp hQ hfull hj q hu hju hu'
  unfold s176_hrec_wall at hrec
  have hR' := hrec v hv hjv huv hv'
  rcases hc with ⟨hy₁, hy₂⟩ | ⟨hy₁, hy₂⟩
  · -- `y = Tsite.y₁ = lift u'`, `Tsite.y₂ = lift v'`
    rw [← hy₁]
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₁
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    refine s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ (Or.inl rfl) ?_
    rw [hy₁, hy₂]
    exact hR'
  · -- `y = Tsite.y₂ = lift u'`, `Tsite.y₁ = lift v'`
    rw [← hy₂]
    obtain ⟨B, -, hB₁, hB₂⟩ := Tsite.exists_bigon_switch₂
    refine est_port_weak_of_bigon _ _ _ rfl rfl B ?_
    rw [s176_reducedRecord_eq B hB₁ hB₂]
    refine s176_hrec_of_unswitched _ _ _ Tsite.y₁ Tsite.y₂ (Or.inr rfl) ?_
    rw [hy₁, hy₂]
    have hcomm := s176_wallKeep_comm hn (CarrierGeometry.ofDiagrammatic ((genericAt E t' ht'.1).diagrammatic hn))
      (CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) hu' hv'
    rw [hcomm] at hR'
    exact hR'

/-- **The weak interface of row 176 from `s176_hrec_wall` and the non-move port data** (the specific-crossings
form of `s176_est_port_relation_weak_of`). -/
theorem s176_est_port_relation_weak_of'
    (hrec : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu')
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end S176HrecWall

end

end RProof

/-! # R176_HSUCC — the successor clause `hsucc` of `hrec` (row 176), and the discharge of the chain

Unit HSUCC (2026-09-15).  Everything above this line is `Site_176.lean`, frozen.  This appendix proves the
single remaining clause of the record identification `hrec` of row 176 (Site_176_REPORT §3):

  `hsucc : ∀ w, Φ ((D₊.record.restrictCrossings (s176_wallKeep u' v')).succ w) = D₀.record.succ (Φ w)`

— the first-return successor of a retained occurrence of the L-side lift `D₊` (the crossings at `u', v'`
deleted) corresponds under the wall bijection `s176_wallΦ` to the H-side successor.  Proof shape (the W1
skeleton's `m6_succ`, with two deleted crossings and a wall instead of a deletion): the cyclic order of three
retained occurrences is read on the parents (`CV.visitBetween_iff_key` on both lifts) and carried across the wall
by `GT_Wall.key_lt` (every pair of retained parent visits of `q₀` is non-reversed: retained crossings of `q₀` are
not triangle crossings, `est_not_retained_H`, so `GT_not_rev_of_not_mem_left`); the first return has no retained
occurrence strictly between (`firstReturn_no_between` with `nextVisit_no_between`), the H-side successor has no
occurrence strictly between (`nextVisit_no_between`), both differ from the start (`Record.firstReturn_val_ne` with
the twin, `nextVisit_ne_self`), and `cycNext_unique` on the H-side traversal coordinate identifies them.

Then the chain: `r176h_hrec_wall_proof : s176_hrec_wall …` (via `s176_hrec_wall_of_succ`),
`r176h_est_port_weak : est_port_weak (carrierDiagram q₀') (carrierDiagram q₀) (est_liftCrossing … hu')` (via
`s176_port_weak_of_event'`), the weak interface from the non-move port data alone
(`r176h_est_port_relation_weak_of_rest`), and the weak ledger from it (`r176h_est_ledger_weak_of_rest`).
All names `r176h_`. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §I. One-component bookkeeping of a positive lift -/

/-- all occurrences of a positive lift lie on its single component -/
theorem r176h_compOf_eq (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P) {T : Finset (Crossing P)}
    (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) (v w : (geoPositiveLift hn hG hT q).Γ.Visit) :
    (geoPositiveLift hn hG hT q).compOf v = (geoPositiveLift hn hG hT q).compOf w := by
  apply Fin.ext
  have h1 := ((geoPositiveLift hn hG hT q).compOf v).isLt
  have h2 := ((geoPositiveLift hn hG hT q).compOf w).isLt
  change _ < 1 at h1 h2
  omega

/-- the traversal coordinate of a positive lift is injective (one component) -/
theorem r176h_visitCoord_injective (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) :
    Function.Injective (geoPositiveLift hn hG hT q).visitCoord :=
  fun v w h => (geoPositiveLift hn hG hT q).visitCoord_injOn (r176h_compOf_eq hn hG hT q v w) h

/-- the record of a positive lift has one component -/
theorem r176h_record_componentCount (hn : 3 ≤ n) {P : LabelledTuple n} (hG : CarrierGeometry P)
    {T : Finset (Crossing P)} (hT : GeoIndependent hG.cg T) (q : GeoComponent hG.cg T) :
    (geoPositiveLift hn hG hT q).record.componentCount = 1 :=
  ((geoPositiveLift hn hG hT q).record_componentCount).trans (geoPositiveLift_componentCount hn hG hT q)

/-! ## §J. The successor clause at the carrier level -/

section R176HWall

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CarrierGeometry P) (hG' : CarrierGeometry P')
  (hs : ∀ s, IsCrossing P s ↔ IsCrossing P' s)
  {T : Finset (Crossing P)} {T' : Finset (Crossing P')} (hT : GeoIndependent hG.cg T)
  (hT' : GeoIndependent hG'.cg T') (q : GeoComponent hG.cg T) (q' : GeoComponent hG'.cg T')
  {u' v' : Crossing P'} (hu' : u' ∈ geoCarrierCrossings hG'.cg T' q') (hv' : v' ∈ geoCarrierCrossings hG'.cg T' q')
  (hX : geoCarrierCrossings hG'.cg T' q' =
    (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding ∪ {u', v'})
  (hu_not : u' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hv_not : v' ∉ (geoCarrierCrossings hG.cg T q).map (crossingTransport hs).toEmbedding)
  (hkey : ∀ v w : Visit P, v.1 ∈ geoCarrierCrossings hG.cg T q → w.1 ∈ geoCarrierCrossings hG.cg T q →
    (geometricVisitKey hG.cg v < geometricVisitKey hG.cg w ↔
      geometricVisitKey hG'.cg (visitTransport hs v) < geometricVisitKey hG'.cg (visitTransport hs w)))

include hkey in
/-- the key order of the parent visits of two retained occurrences is carried across the wall
(`s176_wallΦ_liftVisit` + `hkey` at the transported-back parents) -/
theorem r176h_key_lt_iff (v u : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    geometricVisitKey hG.cg (CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)) <
        geometricVisitKey hG.cg (CV.liftVisit hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u)) ↔
      geometricVisitKey hG'.cg (CV.liftVisit hn hG' hT' q' v.1) <
        geometricVisitKey hG'.cg (CV.liftVisit hn hG' hT' q' u.1) := by
  have h := hkey _ _
    (CV.liftVisit_mem hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v))
    (CV.liftVisit_mem hn hG hT q (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u))
  rw [s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v,
    s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply] at h
  rw [s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v,
    s176_wallΦ_liftVisit hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u]
  exact h

include hkey in
/-- the oriented cyclic order of three retained occurrences is carried across the wall
(`CV.visitBetween_iff_key` on both lifts, `r176h_key_lt_iff` on the three pairs) -/
theorem r176h_cycBetween_iff (v u x : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    cycBetween
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v))
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u))
        ((geoPositiveLift hn hG hT q).visitCoord (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not x)) ↔
      cycBetween ((geoPositiveLift hn hG' hT' q').visitCoord v.1) ((geoPositiveLift hn hG' hT' q').visitCoord u.1)
        ((geoPositiveLift hn hG' hT' q').visitCoord x.1) := by
  show (geoPositiveLift hn hG hT q).VisitBetween (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not v)
      (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not u)
      (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not x) ↔
    (geoPositiveLift hn hG' hT' q').VisitBetween v.1 u.1 x.1
  rw [CV.visitBetween_iff_key, CV.visitBetween_iff_key]
  unfold cycBetween
  rw [r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey v u,
    r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey u x,
    r176h_key_lt_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey x v]

include hkey in
/-- **`hsucc` in the `firstReturn` form**: the first return of the L-side successor to the retained occurrences
corresponds under `s176_wallΦ` to the H-side successor.  `cycNext_unique` on the H-side traversal coordinate: both
candidates differ from `Φ w` (`Record.firstReturn_val_ne` with the retained twin; `record_succ_eq_self_iff` with the
twin), and neither has an occurrence strictly between `Φ w` and itself (`firstReturn_no_between` carried across the
wall by `r176h_cycBetween_iff`; `record_succ_no_between`). -/
theorem r176h_succ_firstReturn (w : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (firstReturn (geoPositiveLift hn hG' hT' q').record.succ
          ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w) := by
  have h1 : (geoPositiveLift hn hG' hT' q').record.componentCount = 1 := r176h_record_componentCount hn hG' hT' q'
  obtain ⟨k, hk, hkw⟩ :=
    (geoPositiveLift hn hG' hT' q').record.crossKeep_exists_ne (s176_wallKeep hn hG' hT' q' hu' hv') w.2
  have hne : firstReturn (geoPositiveLift hn hG' hT' q').record.succ
      ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w ≠ w := by
    intro h
    exact (geoPositiveLift hn hG' hT' q').record.firstReturn_val_ne _ h1 w hk hkw (congrArg Subtype.val h)
  refine cycNext_unique (k := (geoPositiveLift hn hG hT q).visitCoord)
    (v := s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)
    (r176h_visitCoord_injective hn hG hT q)
    (fun h => hne ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).injective h)) ?_ ?_ ?_
  · intro h
    exact (geoPositiveLift hn hG hT q).twin_ne (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)
      (((geoPositiveLift hn hG hT q).record_succ_eq_self_iff
          (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)).mp h
        ((geoPositiveLift hn hG hT q).twin (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w))
        (r176h_compOf_eq hn hG hT q
          ((geoPositiveLift hn hG hT q).twin (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w))
          (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w)))
  · intro u hb
    -- read `u` as the image of a retained occurrence and carry the cyclic order back to the L side
    have hb' := (r176h_cycBetween_iff hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey w
      ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u)
      (firstReturn (geoPositiveLift hn hG' hT' q').record.succ
        ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w)).mp
      (by rwa [Equiv.apply_symm_apply])
    exact firstReturn_no_between (geoPositiveLift hn hG' hT' q').record.succ
      ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG' hT' q').visitCoord
      (fun a b _ he => (geoPositiveLift hn hG' hT' q').visitCoord_injOn (r176h_compOf_eq hn hG' hT' q' b a) he)
      (fun a b _ => (geoPositiveLift hn hG' hT' q').record_succ_no_between a b (r176h_compOf_eq hn hG' hT' q' b a))
      w ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u).1
      (((geoPositiveLift hn hG' hT' q').record.sameCycle_iff_comp_eq _ _).mpr
        (r176h_compOf_eq hn hG' hT' q' _ _))
      ((s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not).symm u).2 hb'
  · intro u
    exact (geoPositiveLift hn hG hT q).record_succ_no_between _ u (r176h_compOf_eq hn hG hT q u _)

include hkey in
/-- **`hsucc` — the successor clause of `hrec`** (Site_176_REPORT §3), in the exact shape of the hypothesis of
`s176_hrec_unswitched_of_succ`: the successor of the restricted record is the first return
(`Record.restrictCrossings_succ_val`, `rfl`). -/
theorem r176h_succ (w : {v : (geoPositiveLift hn hG' hT' q').Γ.Visit //
    (geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv') v}) :
    s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not
        (((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ w) =
      (geoPositiveLift hn hG hT q).record.succ (s176_wallΦ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not w) := by
  have e : ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv')).succ w =
      firstReturn (geoPositiveLift hn hG' hT' q').record.succ
        ((geoPositiveLift hn hG' hT' q').record.CrossKeep (s176_wallKeep hn hG' hT' q' hu' hv')) w :=
    Subtype.ext ((geoPositiveLift hn hG' hT' q').record.restrictCrossings_succ_val
      (s176_wallKeep hn hG' hT' q' hu' hv') w)
  rw [e]
  exact r176h_succ_firstReturn hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey w

include hX hu_not hv_not hkey in
/-- **`hrec` at the carrier level, closed**: the wall transport of the two-crossing-deleted record
(`s176_hrec_unswitched_of_succ` with `r176h_succ`). -/
theorem r176h_hrec_unswitched
    (hdet : ∀ w : Visit P, w.1 ∈ geoCarrierCrossings hG.cg T q →
      (0 < det (edge P w.2.val) (edge P (visitTwin w).2.val) ↔
        0 < det (edge P' w.2.val) (edge P' (visitTwin w).2.val))) :
    Nonempty (RecordIso
      ((geoPositiveLift hn hG' hT' q').record.restrictCrossings (s176_wallKeep hn hG' hT' q' hu' hv'))
      (geoPositiveLift hn hG hT q).record) :=
  s176_hrec_unswitched_of_succ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hdet
    (r176h_succ hn hG hG' hs hT hT' q q' hu' hv' hX hu_not hv_not hkey)

end R176HWall

end

end RProof

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §K. The event level: `hkey` from the wall data, `s176_hrec_wall` PROVED, the weak port, the weak
interface and the weak ledger from the non-move port data alone -/

section R176HEvent

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- the key order of the parent visits is carried across the wall for every pair whose first visit is at a
retained crossing of `q₀` (`est_wall.key_lt`; a retained crossing of `q₀` is not a triangle crossing,
`est_not_retained_H`, so the pair is not reversed, `GT_not_rev_of_not_mem_left`) -/
theorem r176h_hkey_event (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (v w : Visit (E.curve t)) (hv : v.1 ∈ geoCarrierCrossings (geomAt E t ht.1) (Q ∪ {j}) q) :
    geometricVisitKey (geomAt E t ht.1) v < geometricVisitKey (geomAt E t ht.1) w ↔
      geometricVisitKey (geomAt E t' ht'.1) (visitTransport hs v) <
        geometricVisitKey (geomAt E t' ht'.1) (visitTransport hs w) :=
  (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj).key_lt v w
    (GT_not_rev_of_not_mem_left fun h =>
      est_not_retained_H ht hcomp hQ hfull hj q hv ((F1.mem_triangleCrossings e f g v.1).mp h))

/-- **`s176_hrec_wall` PROVED** (rule (1) form `r176h_<name>_proof`): the record identification of row 176 for the
deleted crossings `lift u', lift v'`, for every third triangle crossing `v` with `v'` retained — through
`s176_hrec_wall_of_succ` with the successor clause `r176h_succ` and the wall key order `r176h_hkey_event`. -/
theorem r176h_hrec_wall_proof (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' :=
  s176_hrec_wall_of_succ hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'
    (fun _v hv hjv huv hv' w => r176h_succ hn _ _ hs _ _ q _ hu' hv'
      (s176_hX_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu' hv hjv huv)
      (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hu)
      (s176_not_mem_map_event ht hs hcomp hQ hfull hj q hv)
      (fun a b ha _ => r176h_hkey_event hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q a b ha) w)

/-- `s176_hrec_wall`, under the unit's own name. -/
theorem r176h_hrec_wall (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu' :=
  r176h_hrec_wall_proof hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu'

/-- **The weak RII port of row 176** (item (c) of the site unit, now with `hrec` DISCHARGED):
`est_port_weak (carrierDiagram q₀') (carrierDiagram q₀) (est_liftCrossing … hu')`, through the frozen leaf
`exists_bigonData_of_triangle` only (`s176_port_weak_of_event'` + `r176h_hrec_wall_proof`). -/
theorem r176h_est_port_weak (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {u : Crossing (E.curve t)} (hu : u.val ∈ triangleSupports e f g) (hju : j ≠ u)
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) :
    est_port_weak
      (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
      (CV.carrierDiagram hn (genericAt E t ht.1) (est_S_ind ht.1 hQ hfull hj) q)
      (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu') :=
  s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju hu'
    (r176h_hrec_wall_proof hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hu hju hu')

end R176HEvent

/-- **The weak interface of row 176 from the non-move port data ALONE** — `s176_est_port_relation_weak_of'`
with its `hrec` hypothesis discharged.  (The frozen `s176_est_port_relation_weak_of'` quantifies `hrec` without
`hcomp`, `hu`, `hju`, which `s176_hrec_wall_of_succ` needs; its `intro` has them, so the port is built here
directly from `r176h_est_port_weak`.)  The `hrest` binder is byte-identical to that of
`s176_est_port_relation_weak_of'`. -/
theorem r176h_est_port_relation_weak_of_rest
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    s176_est_port_relation_weak := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := hrest n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact r176h_est_port_weak hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm hu'

/-- **The weak RA ledger of row 176 from the non-move port data alone** (`s176_est_ledger_weak` +
`r176h_est_port_relation_weak_of_rest`): what row 176 still owes is exactly `s176_PortDataRest`
(U_R176_REPORT §5 items 2–5) and the F-176-1 acceptance. -/
theorem r176h_est_ledger_weak_of_rest (hF : CV.CarrierSlotFloor)
    (hrest : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
      (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
      (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
      (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
      (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
      (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
      (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
      (u : Crossing (E.curve t))
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (s176_PortDataRest hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))) :
    RowShape @ExtremeTransportData :=
  s176_est_ledger_weak hF (r176h_est_port_relation_weak_of_rest hrest)

end

end RProof
