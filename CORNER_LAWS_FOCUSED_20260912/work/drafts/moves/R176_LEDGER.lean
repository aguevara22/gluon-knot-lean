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


/-! # R176_LEDGER — row 176 (R:extreme_transport), the LEDGER unit: items (14), (13), (12) of
`s176_PortDataRest`

APPENDED by the LEDGER prover, 2026-09-15, to `Site_176.lean` (byte-identical above this line).
Companion report: `R176_LEDGER_REPORT.md`.  All names carry the prefix `r176l_`; nothing above is
modified.  The oriented smoothing `D_A`, its component tags and the exact owner map (`poly₁`, `poly₂`)
are the SMOOTH unit's and enter only through the black-box structure `r176l_SmoothData`.

Sections: §L0 abstract sign/rotation ledgers on labelled tuples ((12) from a one-dissent corner-sign
shape, `σ·rot ≥ 1`, the uniform triangle, the `|·|`-ledger arithmetic of (13)); §L1 `mixedSignSum` as
the number of mixed crossings when every crossing is positive; §L2 the interface — the two clean outer
children `r176l_Children`, the mask-`uv` survivors `r176l_mixedSet`, the L-side retained-set
decomposition (14), the black box `r176l_SmoothData`, and the assembly `r176l_portDataRest_of`; §L3 the
geometric realisation on the labelled corner (case 1): the two-step split of the affected carrier by
`u', v'`, the central triangle, the children, the corner marks and turns of the outer carriers, the
one-dissent shapes (12) and the rotation additivity (13); §L4 the event level. -/

namespace RProof

open SM SM.GeoCarrier SM.Carrier SM.Link

noncomputable section

variable {n : ℕ} [NeZero n]

/-! ## §L0. Abstract sign and rotation ledgers on labelled tuples -/

/-- **The corner-sign shape of a clean outer carrier** (RA (12): "exactly one `-σ` local corner and
all inherited corners have sign `σ`"): every turn of `L` is `σ` except exactly one, which is `-σ`. -/
def r176l_OneDissentShape {c : ℕ} (L : LabelledTuple c) (σ : SignType) : Prop :=
  ∃ k₀ : ZMod c, turn L k₀ = -σ ∧ ∀ k, k ≠ k₀ → turn L k = σ

theorem r176l_principalTurn_pos_of_turn {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    {k : ZMod c} (h : turn L k = 1) : 0 < CV.principalTurn L k := by
  rw [CV.principalTurn_eq_sm]
  exact sign_eq_one_iff.mp ((principalTurn_sign ((CV.regular_iff_sm L).mp hL) k).trans h)

theorem r176l_principalTurn_neg_of_turn {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    {k : ZMod c} (h : turn L k = -1) : CV.principalTurn L k < 0 := by
  rw [CV.principalTurn_eq_sm]
  exact sign_eq_neg_one_iff.mp ((principalTurn_sign ((CV.regular_iff_sm L).mp hL) k).trans h)

/-- **(12)**: a one-dissent shape with `σ ≠ 0` is uniform-or-one-dissent in CV's sense: for `σ = 1`
directly (one negative turn, all others positive), for `σ = -1` after the orientation reversal
(`principalTurn_reversal` negates every turn). -/
theorem r176l_uniformOrOneDissent_of_shape {c : ℕ} [NeZero c] {L : LabelledTuple c}
    (hL : CV.Regular L) {σ : SignType} (hσ : σ ≠ 0) (h : r176l_OneDissentShape L σ) :
    CV.UniformOrOneDissentCV L := by
  obtain ⟨k₀, hk₀, hk⟩ := h
  have hSM : Regular L := (CV.regular_iff_sm L).mp hL
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    left; right
    exact ⟨k₀, r176l_principalTurn_neg_of_turn hL hk₀,
      fun k hk' => r176l_principalTurn_pos_of_turn hL (hk k hk')⟩
  | neg =>
    right; right
    refine ⟨2 - k₀, ?_, ?_⟩
    · rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have h1 : turn L (2 - (2 - k₀)) = 1 := by
        rw [show (2 : ZMod c) - (2 - k₀) = k₀ by ring]; exact hk₀
      have := r176l_principalTurn_pos_of_turn hL h1
      rw [CV.principalTurn_eq_sm] at this; linarith
    · intro i hi
      rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have hne : 2 - i ≠ k₀ := fun h => hi (by rw [← h]; ring)
      have := r176l_principalTurn_neg_of_turn hL (hk _ hne)
      rw [CV.principalTurn_eq_sm] at this; linarith

/-- The signed rotation of a one-dissent-shaped polygon has the sign `σ` and is nonzero
(CV lem:uniformrot (ii), after a possible reversal): `σ · rot(L) ≥ 1`. -/
theorem r176l_one_le_sign_mul_rot_of_shape {c : ℕ} [NeZero c] {L : LabelledTuple c}
    (hL : CV.Regular L) {σ : SignType} (hσ : σ ≠ 0) (h : r176l_OneDissentShape L σ) :
    1 ≤ (σ : ℤ) * CV.rot L hL := by
  obtain ⟨k₀, hk₀, hk⟩ := h
  have hSM : Regular L := (CV.regular_iff_sm L).mp hL
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    have := CV.one_le_rot_of_one_dissent hL k₀
      (fun i hi => (r176l_principalTurn_pos_of_turn hL (hk i hi)).le)
    simpa using this
  | neg =>
    have hrev := CV.regular_reversal' hL
    have h1 : 1 ≤ CV.rot (reversal L) hrev := by
      refine CV.one_le_rot_of_one_dissent hrev (2 - k₀) fun i hi => ?_
      rw [CV.principalTurn_eq_sm, principalTurn_reversal hSM]
      have hne : 2 - i ≠ k₀ := fun h => hi (by rw [← h]; ring)
      have := r176l_principalTurn_neg_of_turn hL (hk _ hne)
      rw [CV.principalTurn_eq_sm] at this; linarith
    rw [CV.rot_reversal hL hrev] at h1
    simpa using h1

/-- The rotation of a uniform three-corner polygon is its common turn sign (CV lem:uniformrot (i),
"with equality if `L` has three corners"). -/
theorem r176l_rot_uniform_three {c : ℕ} [NeZero c] {L : LabelledTuple c} (hL : CV.Regular L)
    (h3 : c = 3) {σ : SignType} (hσ : σ ≠ 0) (h : ∀ k, turn L k = σ) : CV.rot L hL = (σ : ℤ) := by
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    have := CV.uniformrot.pos_three c L hL (fun i => r176l_principalTurn_pos_of_turn hL (h i)) h3
    simpa using this
  | neg =>
    have := CV.uniformrot.neg_three c L hL (fun i => r176l_principalTurn_neg_of_turn hL (h i)) h3
    simpa using this

/-- **The `|·|`-arithmetic of (13)**: three signed rotations of one sign `σ` add up in absolute value. -/
theorem r176l_abs_ledger {r r₁ r₂ : ℤ} {σ : SignType} (hσ : σ ≠ 0) (h : r = r₁ + r₂ + (σ : ℤ))
    (h₁ : 1 ≤ (σ : ℤ) * r₁) (h₂ : 1 ≤ (σ : ℤ) * r₂) : |r| = |r₁| + |r₂| + 1 := by
  cases σ with
  | zero => exact absurd rfl hσ
  | pos =>
    simp only [SignType.pos_eq_one, SignType.coe_one, one_mul] at h h₁ h₂
    rw [abs_of_pos (by omega), abs_of_pos (by omega), abs_of_pos (by omega)]
    omega
  | neg =>
    simp only [SignType.neg_eq_neg_one, SignType.coe_neg, SignType.coe_one, neg_mul, one_mul] at h h₁ h₂
    rw [abs_of_neg (by omega), abs_of_neg (by omega), abs_of_neg (by omega)]
    omega

/-! ## §L1. `2ℓ` as the number of mixed crossings when every crossing is positive -/

/-- A crossing of `D` between the components `i` and `j` ("mixed"). -/
def r176l_IsMixed (D : Diagram) (i j : Fin D.Γ.c) (x : D.Γ.Crossing) : Prop :=
  ((D.overStrand x).1 = i ∧ (D.underStrand x).1 = j) ∨
  ((D.overStrand x).1 = j ∧ (D.underStrand x).1 = i)

open scoped Classical in
/-- `2ℓ_ij` as a sum over the mixed crossings (each mixed crossing is exactly one ordered strand pair
`(s, t)` with `s` on `i`, `t` on `j`); the proof is the accepted `SM.s7h_mixedSignSum_eq`
(SM/CornerChainUnits.lean, not imported here), copied. -/
theorem r176l_mixedSignSum_eq (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j) :
    mixedSignSum D i j =
      ∑ x ∈ Finset.univ.filter (r176l_IsMixed D i j), (D.sign x : ℤ) := by
  unfold mixedSignSum
  rw [← Finset.sum_product' Finset.univ Finset.univ (fun s t : D.Γ.Strand =>
    if h : D.Γ.MixedPair i j s t then ((D.sign ⟨{s, t}, h.2.2⟩ : SignType) : ℤ) else 0)]
  have hmp : ∀ p : D.Γ.Strand × D.Γ.Strand,
      (if h : D.Γ.MixedPair i j p.1 p.2 then ((D.sign ⟨{p.1, p.2}, h.2.2⟩ : SignType) : ℤ) else 0) ≠ 0 →
      D.Γ.MixedPair i j p.1 p.2 := by
    intro p hne
    by_contra hm
    exact hne (dite_eq_right hm)
  refine Finset.sum_bij_ne_zero (fun p _ hne => ⟨{p.1, p.2}, (hmp p hne).2.2⟩) ?_ ?_ ?_ ?_
  · intro p _ hne
    have hm := hmp p hne
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    rcases D.eq_over_under_of_crossing_eq hm.2.2 rfl with ⟨hs, ht⟩ | ⟨hs, ht⟩
    · left; exact ⟨by rw [← hs]; exact hm.1, by rw [← ht]; exact hm.2.1⟩
    · right; exact ⟨by rw [← ht]; exact hm.2.1, by rw [← hs]; exact hm.1⟩
  · intro p₁ _ hne₁ p₂ _ hne₂ e
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
  · intro x hx _
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
  · intro p _ hne
    rw [dite_eq_left (hmp p hne)]

open scoped Classical in
/-- **"Since every mixed retained crossing is positive … exactly `2ℓ` complementary-mask crossings
occur"**: with every crossing positive, `2ℓ_ij` is the number of mixed crossings. -/
theorem r176l_mixedSignSum_eq_card (D : Diagram) (i j : Fin D.Γ.c) (hij : i ≠ j)
    (hpos : ∀ x : D.Γ.Crossing, D.sign x = 1) :
    mixedSignSum D i j = ((Finset.univ.filter (r176l_IsMixed D i j)).card : ℤ) := by
  rw [r176l_mixedSignSum_eq D i j hij, Finset.card_eq_sum_ones, Nat.cast_sum]
  exact Finset.sum_congr rfl fun x _ => by rw [hpos x]; rfl

/-! ## §L2. The interface: the two clean outer children, the mask-`uv` survivors, the black box -/

section L2Children

variable {P : LabelledTuple n} (hP : CrossingGeometry P)

/-- **The two clean outer children** `Λ₁, Λ₂` of the affected carrier `q'` of `S'` inside the full
support `Sf ⊇ S'` (RA §2: "the two successive smoothings `q, r` split that carrier into the two clean
outer carriers … and the central triangle"): both lie inside `q'`, they are distinct, and every visit
of an unselected (in `Sf`) crossing that `q'` owns is owned by one of them (the central triangle owns
only the three local corner marks). -/
structure r176l_Children (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (Λ₁ Λ₂ : GeoComponent hP Sf) : Prop where
  sub₁ : ∀ m : Mark P, geoOwner hP Sf m = Λ₁ → geoOwner hP S' m = q'
  sub₂ : ∀ m : Mark P, geoOwner hP Sf m = Λ₂ → geoOwner hP S' m = q'
  ne : Λ₁ ≠ Λ₂
  cover : ∀ w : Visit P, w.1 ∉ Sf → geoOwner hP S' (Sum.inr w) = q' →
    geoOwner hP Sf (Sum.inr w) = Λ₁ ∨ geoOwner hP Sf (Sum.inr w) = Λ₂

open scoped Classical in
/-- **The mask-`uv` survivors** (R-PAR `interlaced_pair`; RA (5) "every two-letter-mask survivor has
one visit in each of the two affected gaps"): the retained crossings of `q'`, unselected in `Sf`, whose
two visits lie on different children — exactly the mixed crossings of `D_A` (14). -/
def r176l_mixedSet (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S')
    (Λ₁ Λ₂ : GeoComponent hP Sf) : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∉ Sf ∧
    ∃ v w : Visit P, v.1 = x ∧ w.1 = x ∧
      geoOwner hP Sf (Sum.inr v) = Λ₁ ∧ geoOwner hP Sf (Sum.inr w) = Λ₂

open scoped Classical in
/-- The retained crossings of `q'` that are selected in `Sf` (at the 176 site: `{u', v'}`). -/
def r176l_selectedPart (S' Sf : Finset (Crossing P)) (q' : GeoComponent hP S') : Finset (Crossing P) :=
  (geoCarrierCrossings hP S' q').filter fun x => x ∈ Sf

variable {S' Sf : Finset (Crossing P)} {q' : GeoComponent hP S'} {Λ₁ Λ₂ : GeoComponent hP Sf}

/-- The retained set of a child is inside the retained set of `q'`, off `Sf`. -/
theorem r176l_retained_child_subset (hSS : S' ⊆ Sf)
    (hsub : ∀ m : Mark P, geoOwner hP Sf m = Λ₁ → geoOwner hP S' m = q') {x : Crossing P}
    (hx : x ∈ geoCarrierCrossings hP Sf Λ₁) : x ∈ geoCarrierCrossings hP S' q' ∧ x ∉ Sf := by
  rw [mem_geoCarrierCrossings] at hx ⊢
  exact ⟨⟨fun h => hx.1 (hSS h), fun v hv => hsub _ (hx.2 v hv)⟩, hx.1⟩

/-- **The L-side decomposition of the retained set of the affected carrier** (RA (14): "`D_0` contains
the two outer self-crossing sets and the `2ℓ` positive crossings which become mixed in `D_A`", plus
the two local crossings selected in `Sf`). -/
theorem r176l_retained_decomp (hSS : S' ⊆ Sf) (hC : r176l_Children hP S' Sf q' Λ₁ Λ₂) :
    geoCarrierCrossings hP S' q' =
      geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂ ∪
        r176l_mixedSet hP S' Sf q' Λ₁ Λ₂ ∪ r176l_selectedPart hP S' Sf q' := by
  classical
  ext x
  simp only [Finset.mem_union, r176l_mixedSet, r176l_selectedPart, Finset.mem_filter]
  constructor
  · intro hx
    by_cases hxSf : x ∈ Sf
    · exact Or.inr ⟨hx, hxSf⟩
    · have hx' := (mem_geoCarrierCrossings hP S' q' x).mp hx
      obtain ⟨i, -, -⟩ := crossing_visits_exist x
      set v₀ : Visit P := ⟨x, i⟩ with hv₀
      have hall : ∀ w : Visit P, w.1 = x → w = v₀ ∨ w = visitTwin v₀ := fun w hw =>
        visit_eq_or_twin v₀ w hw
      have ho₀ := hC.cover v₀ hxSf (hx'.2 v₀ rfl)
      have ho₁ := hC.cover (visitTwin v₀) hxSf (hx'.2 _ rfl)
      rcases ho₀ with h₀ | h₀ <;> rcases ho₁ with h₁ | h₁
      · left; left; left
        rw [mem_geoCarrierCrossings]
        refine ⟨hxSf, fun w hw => ?_⟩
        rcases hall w hw with rfl | rfl
        · exact h₀
        · exact h₁
      · left; right
        exact ⟨hx, hxSf, v₀, visitTwin v₀, rfl, rfl, h₀, h₁⟩
      · left; right
        exact ⟨hx, hxSf, visitTwin v₀, v₀, rfl, rfl, h₁, h₀⟩
      · left; left; right
        rw [mem_geoCarrierCrossings]
        refine ⟨hxSf, fun w hw => ?_⟩
        rcases hall w hw with rfl | rfl
        · exact h₀
        · exact h₁
  · rintro (((h | h) | ⟨h, -⟩) | ⟨h, -⟩)
    · exact (r176l_retained_child_subset hP hSS hC.sub₁ h).1
    · exact (r176l_retained_child_subset hP hSS hC.sub₂ h).1
    · exact h
    · exact h

/-- The four parts are pairwise disjoint, so the cardinalities add (14). -/
theorem r176l_card_retained (hSS : S' ⊆ Sf) (hC : r176l_Children hP S' Sf q' Λ₁ Λ₂) :
    (geoCarrierCrossings hP S' q').card =
      (geoCarrierCrossings hP Sf Λ₁).card + (geoCarrierCrossings hP Sf Λ₂).card +
        (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂).card + (r176l_selectedPart hP S' Sf q').card := by
  classical
  have hd₁₂ : Disjoint (geoCarrierCrossings hP Sf Λ₁) (geoCarrierCrossings hP Sf Λ₂) := by
    rw [Finset.disjoint_left]
    intro x h₁ h₂
    obtain ⟨i, -, -⟩ := crossing_visits_exist x
    have e₁ := ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h₁).2 ⟨x, i⟩ rfl
    have e₂ := ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h₂).2 ⟨x, i⟩ rfl
    exact hC.ne (e₁.symm.trans e₂)
  have hdM : Disjoint (geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂)
      (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂) := by
    rw [Finset.disjoint_left]
    intro x hx hM
    obtain ⟨-, -, v, w, hv, hw, hov, how⟩ := Finset.mem_filter.mp hM
    rcases Finset.mem_union.mp hx with h | h
    · have := ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h).2 w hw
      exact hC.ne (this.symm.trans how)
    · have := ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h).2 v hv
      exact hC.ne (hov.symm.trans this)
  have hdS : Disjoint (geoCarrierCrossings hP Sf Λ₁ ∪ geoCarrierCrossings hP Sf Λ₂ ∪
      r176l_mixedSet hP S' Sf q' Λ₁ Λ₂) (r176l_selectedPart hP S' Sf q') := by
    rw [Finset.disjoint_left]
    intro x hx hS
    have hxSf : x ∈ Sf := (Finset.mem_filter.mp hS).2
    rcases Finset.mem_union.mp hx with h | h
    · rcases Finset.mem_union.mp h with h | h
      · exact ((mem_geoCarrierCrossings hP Sf Λ₁ x).mp h).1 hxSf
      · exact ((mem_geoCarrierCrossings hP Sf Λ₂ x).mp h).1 hxSf
    · exact (Finset.mem_filter.mp h).2.1 hxSf
  rw [r176l_retained_decomp hP hSS hC, Finset.card_union_of_disjoint hdS,
    Finset.card_union_of_disjoint hdM, Finset.card_union_of_disjoint hd₁₂]

end L2Children

/-! ### The black box from the SMOOTH unit -/

/-- **The SMOOTH unit's data, as a black box** (U_R176_REPORT §5 items 2–3): the oriented smoothing
`D_A` of `D₊ = carrierDiagram q'` at `y` with two components `i ≠ j`, the exact owner map (9)/(9a)
`poly₁ poly₂` (the record isomorphisms of the two component restrictions with the lifts of the clean
outer carriers `Λ₁, Λ₂` of `S_full`, the kink removed by lc:single-crossing — SMOOTH's), and the bridge
for (14): the mixed crossings of `D_A` are the mask-`uv` survivors, all positive, so `2ℓ = mixedSignSum`
is their number (`r176l_mixedSignSum_eq_card` reduces this to a bijection between the mixed crossings of
`D_A` and `r176l_mixedSet`).  The support `Sf` and the children `Λ₁, Λ₂` are PARAMETERS: they are
defined geometrically in §L3 by this unit. -/
structure r176l_SmoothData (hn : 3 ≤ n) {P' : LabelledTuple n} (hG' : CV.Generic P')
    {S' : Finset (Crossing P')} (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
    (q' : GeoComponent hG'.crossingGeometry S') (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
    (Sf : Finset (Crossing P')) (hSf : Sf ∈ CV.Ind hG'.crossingGeometry)
    (Λ₁ Λ₂ : GeoComponent hG'.crossingGeometry Sf) where
  DA : Diagram
  smooth : IsOrientedSmoothing (CV.carrierDiagram hn hG' hS' q') y DA
  two : DA.componentCount = 2
  i : Fin DA.Γ.c
  j : Fin DA.Γ.c
  ij : i ≠ j
  poly₁ : homfly (DA.knotRestrict i) = CV.groupedPoly hn hG' hSf Λ₁
  poly₂ : homfly (DA.knotRestrict j) = CV.groupedPoly hn hG' hSf Λ₂
  /-- (14) bridge: `2ℓ` = the number of mask-`uv` survivors -/
  mixed : mixedSignSum DA i j = ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ)

section L2Assembly

variable (hn : 3 ≤ n) {P P' : LabelledTuple n} (hG : CV.Generic P) (hG' : CV.Generic P')
  {S : Finset (Crossing P)} {S' : Finset (Crossing P')}
  (hS : S ∈ CV.Ind hG.crossingGeometry) (hS' : S' ∈ CV.Ind hG'.crossingGeometry)
  (q : GeoComponent hG.crossingGeometry S) (q' : GeoComponent hG'.crossingGeometry S')
  (y : (CV.carrierDiagram hn hG' hS' q').Γ.Crossing)
  {Sf : Finset (Crossing P')} {hSf : Sf ∈ CV.Ind hG'.crossingGeometry}
  {Λ₁ Λ₂ : GeoComponent hG'.crossingGeometry Sf}

/-- **The linking number** `ℓ` of the two components of `D_A` (`CV.exists_linkingNumber`). -/
def r176l_ell (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) : ℤ :=
  Classical.choose (CV.exists_linkingNumber D.DA D.i D.j D.ij)

theorem r176l_ell_spec (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) :
    CV.IsLinkingNumber D.DA D.i D.j (r176l_ell hn hG' hS' q' y D) :=
  Classical.choose_spec (CV.exists_linkingNumber D.DA D.i D.j D.ij)

/-- `2ℓ` is the number of mask-`uv` survivors. -/
theorem r176l_two_mul_ell (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂) :
    2 * r176l_ell hn hG' hS' q' y D =
      ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ) :=
  (r176l_ell_spec hn hG' hS' q' y D).trans D.mixed

/-- **The non-move port data from the black box and the three ledgers**: (14) in the form
`w₀ = w₁ + w₂ + |mixedSet|`, (13), and the two one-dissent shapes (12). -/
def r176l_portDataRest_of (D : r176l_SmoothData hn hG' hS' q' y Sf hSf Λ₁ Λ₂)
    (hw : CV.groupedWrithe hG q = CV.groupedWrithe hG' Λ₁ + CV.groupedWrithe hG' Λ₂ +
      ((r176l_mixedSet hG'.crossingGeometry S' Sf q' Λ₁ Λ₂).card : ℤ))
    (hrot : (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1)
    (alt₁ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁))
    (alt₂ : CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂)) :
    s176_PortDataRest hn hG hG' hS hS' q q' y :=
  ⟨D.DA, D.smooth, D.two, D.i, D.j, D.ij, Sf, hSf, Λ₁, Λ₂, D.poly₁, D.poly₂,
    r176l_ell hn hG' hS' q' y D, r176l_ell_spec hn hG' hS' q' y D,
    by rw [hw, r176l_two_mul_ell hn hG' hS' q' y D], hrot, alt₁, alt₂⟩

include hn hSf in
/-- (12) for both children from their one-dissent shapes. -/
theorem r176l_alt_of_shape {σ : SignType} (hσ : σ ≠ 0)
    (h₁ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) σ)
    (h₂ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) σ) :
    CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) ∧
    CV.UniformOrOneDissentCV (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) :=
  ⟨r176l_uniformOrOneDissent_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) hσ h₁,
    r176l_uniformOrOneDissent_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) hσ h₂⟩

/-- **(13) from the signed additivity and the shapes**: `R(D₊) = R(D₀)` (`GT_carrierR_eq`, consumed as
`hRR`), `rot(q') = rot(Λ₁) + rot(Λ₂) + σ` (turnlift (ii) with the opposite new turns, `hadd`), and the
one-dissent shapes give `σ·rot(Λᵢ) ≥ 1`, so the absolute values add. -/
theorem r176l_rot_ledger {σ : SignType} (hσ : σ ≠ 0)
    (hRR : CV.carrierR hn hG' hS' q' = CV.carrierR hn hG hS q)
    (hadd : CV.rot (geoCornerPolygon hG'.crossingGeometry S' q') (CV.carrierPolygon_cvRegular hn hG' hS' q') =
      CV.rot (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) +
      CV.rot (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) +
      (σ : ℤ))
    (h₁ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₁) σ)
    (h₂ : r176l_OneDissentShape (geoCornerPolygon hG'.crossingGeometry Sf Λ₂) σ) :
    (CV.carrierR hn hG hS q : ℤ) = CV.carrierR hn hG' hSf Λ₁ + CV.carrierR hn hG' hSf Λ₂ + 1 := by
  rw [← hRR, CV.carrierR_cast, CV.carrierR_cast, CV.carrierR_cast]
  exact r176l_abs_ledger hσ hadd
    (r176l_one_le_sign_mul_rot_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₁) hσ h₁)
    (r176l_one_le_sign_mul_rot_of_shape (CV.carrierPolygon_cvRegular hn hG' hSf Λ₂) hσ h₂)

end L2Assembly

/-! ## §L3. The geometric realisation on the labelled corner (case 1)

The labelled corner of Site_176 §C: `j = {a, b} ∈ T` the selected corner, `u = {a, c}`, `v = {b, c}`
the two retained (unselected) local crossings of the carrier `q`, in the orientation of case 1
(`u` before `j` on `a`, `j` before `v` on `b`, `v` before `u` on `c`; the third order is FORCED by the
independence of `S_full`, §L3.4).  The full support is `Sf = T ∪ {u, v}`, its three children inside
`q` are the central triangle `Z = owner (j, a) = {(u, c), (j, a), (v, b)}` and the two clean outer
carriers `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`.

Decidability: the accepted insertion lemmas of SM/GeoCarrierCount.lean state `insert v.1 S` with the
classical instance `fun a b => Classical.propDecidable (a = b)`, while this file resolves
`DecidableEq (Crossing P)` to `RProof.instDecidableEqCrossing`; the two `insert`s are not
definitionally equal, so the supports are written with the explicit classical instance (`r176l_ins`). -/

section L3

variable (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)
  {T : Finset (Crossing P)} (hT : GeoIndependent hP T) (q : GeoComponent hP T)
  {a b c : ZMod n} (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
  {j u v : Crossing P} (hj : j.val = {a, b}) (hu : u.val = {a, c}) (hv : v.val = {b, c})
  (hjT : j ∈ T) (huq : u ∈ geoCarrierCrossings hP T q) (hvq : v ∈ geoCarrierCrossings hP T q)

/-! ### L3.1 The six local visits and the full support -/

omit [NeZero n] in
/-- The classical `DecidableEq (Crossing P)` of the accepted insertion lemmas (reducible, so that
`insert` below is definitionally the library's `insert`). -/
abbrev r176l_decEq (P : LabelledTuple n) : DecidableEq (Crossing P) :=
  fun a b => Classical.propDecidable (a = b)

attribute [local instance 2000] r176l_decEq

omit [NeZero n] in
/-- `insert` with the classical instance. -/
abbrev r176l_ins (x : Crossing P) (S : Finset (Crossing P)) : Finset (Crossing P) := insert x S

omit [NeZero n] in
theorem r176l_mem_ins {x y : Crossing P} {S : Finset (Crossing P)} :
    y ∈ r176l_ins x S ↔ y = x ∨ y ∈ S := Finset.mem_insert

omit [NeZero n] in
/-- the visit of `u` on `a` -/
def r176l_ua {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) : Visit P := visitOn u a (s176_mem_left hu)
omit [NeZero n] in
/-- the visit of `u` on `c` -/
def r176l_uc {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) : Visit P := visitOn u c (s176_mem_right hu)

omit [NeZero n] in
theorem r176l_twin_ua {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) (hac : a ≠ c) :
    visitTwin (r176l_ua hu) = r176l_uc hu :=
  s176_visitTwin_eq hu hac _ _
omit [NeZero n] in
theorem r176l_twin_uc {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) (hac : a ≠ c) :
    visitTwin (r176l_uc hu) = r176l_ua hu :=
  s176_visitTwin_eq (s176_pair_comm' hu) hac.symm _ _
omit [NeZero n] in
theorem r176l_twin_vb {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) (hbc : b ≠ c) :
    visitTwin (visitOn v b (s176_mem_left hv)) = visitOn v c (s176_mem_right hv) :=
  s176_visitTwin_eq hv hbc _ _
omit [NeZero n] in
theorem r176l_twin_vc {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) (hbc : b ≠ c) :
    visitTwin (visitOn v c (s176_mem_right hv)) = visitOn v b (s176_mem_left hv) :=
  s176_visitTwin_eq (s176_pair_comm' hv) hbc.symm _ _

omit [NeZero n] in
/-- two visits of distinct crossings are distinct -/
theorem r176l_visit_ne_of_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ m : ZMod n} (hx : ℓ ∈ x.val) (hy : m ∈ y.val) :
    visitOn x ℓ hx ≠ visitOn y m hy := fun h => hxy (congrArg (fun w : Visit P => w.1) h)

omit [NeZero n] in
/-- two visits of one crossing on distinct edges are distinct -/
theorem r176l_visit_ne_of_edge_ne {x : Crossing P} {ℓ m : ZMod n} (hℓm : ℓ ≠ m) (hx : ℓ ∈ x.val) (hy : m ∈ x.val) :
    visitOn x ℓ hx ≠ visitOn x m hy := fun h => hℓm (congrArg (fun w : Visit P => w.2.val) h)

/-- the first insertion `S₁ = T ∪ {u}` -/
abbrev r176l_S1 (T : Finset (Crossing P)) (u : Crossing P) : Finset (Crossing P) := r176l_ins u T

/-- The full support `S_full = T ∪ {u, v}`. -/
abbrev r176l_Sf (T : Finset (Crossing P)) (u v : Crossing P) : Finset (Crossing P) := r176l_ins v (r176l_ins u T)

omit [NeZero n] in
theorem r176l_indep_mono {S S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (h : S ⊆ S') :
    GeoIndependent hP S := fun x hx y hy hxy => hS' x (h hx) y (h hy) hxy

omit [NeZero n] in
theorem r176l_subset_S1 (T : Finset (Crossing P)) (u : Crossing P) : T ⊆ r176l_S1 T u :=
  fun _ h => r176l_mem_ins.mpr (Or.inr h)
omit [NeZero n] in
theorem r176l_S1_subset_Sf (T : Finset (Crossing P)) (u v : Crossing P) : r176l_S1 T u ⊆ r176l_Sf T u v :=
  fun _ h => r176l_mem_ins.mpr (Or.inr h)
omit [NeZero n] in
theorem r176l_subset_Sf (T : Finset (Crossing P)) (u v : Crossing P) : T ⊆ r176l_Sf T u v :=
  (r176l_subset_S1 T u).trans (r176l_S1_subset_Sf T u v)
omit [NeZero n] in
theorem r176l_u_mem_S1 (T : Finset (Crossing P)) (u : Crossing P) : u ∈ r176l_S1 T u :=
  r176l_mem_ins.mpr (Or.inl rfl)
omit [NeZero n] in
theorem r176l_u_mem_Sf (T : Finset (Crossing P)) (u v : Crossing P) : u ∈ r176l_Sf T u v :=
  r176l_S1_subset_Sf T u v (r176l_u_mem_S1 T u)
omit [NeZero n] in
theorem r176l_v_mem_Sf (T : Finset (Crossing P)) (u v : Crossing P) : v ∈ r176l_Sf T u v :=
  r176l_mem_ins.mpr (Or.inl rfl)

/-! ### L3.2 Distinctness and membership -/

include huq in
theorem r176l_u_not_mem : u ∉ T := ((mem_geoCarrierCrossings hP T q u).mp huq).1
include hvq in
theorem r176l_v_not_mem : v ∉ T := ((mem_geoCarrierCrossings hP T q v).mp hvq).1

omit [NeZero n] in
include hac hbc hj hu in
theorem r176l_j_ne_u : j ≠ u := s176_ne_of_supports hj hu hac hbc
omit [NeZero n] in
include hac hbc hj hv in
theorem r176l_j_ne_v : j ≠ v := s176_ne_of_supports (s176_pair_comm' hj) hv hbc hac
omit [NeZero n] in
include hab hbc hu hv in
theorem r176l_u_ne_v : u ≠ v := s176_ne_of_supports (s176_pair_comm' hu) (s176_pair_comm' hv) hbc.symm hab

include hab hbc hu hv hvq in
theorem r176l_v_not_mem_S1 : v ∉ r176l_S1 T u := by
  intro h
  rcases r176l_mem_ins.mp h with h | h
  · exact r176l_u_ne_v hab hbc hu hv h.symm
  · exact r176l_v_not_mem hP q hvq h

include huq in
/-- the retained visits of `u` are owned by `q` -/
theorem r176l_owner_ua : geoOwner hP T (Sum.inr (r176l_ua hu)) = q :=
  ((mem_geoCarrierCrossings hP T q u).mp huq).2 _ rfl
include huq in
theorem r176l_owner_uc : geoOwner hP T (Sum.inr (r176l_uc hu)) = q :=
  ((mem_geoCarrierCrossings hP T q u).mp huq).2 _ rfl
include hvq in
theorem r176l_owner_vb : geoOwner hP T (Sum.inr (visitOn v b (s176_mem_left hv))) = q :=
  ((mem_geoCarrierCrossings hP T q v).mp hvq).2 _ rfl
include hvq in
theorem r176l_owner_vc : geoOwner hP T (Sum.inr (visitOn v c (s176_mem_right hv))) = q :=
  ((mem_geoCarrierCrossings hP T q v).mp hvq).2 _ rfl

/-! ### L3.3 The successor facts of case 1 -/

section Case1

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))

include huq hρa in
/-- `ρ_T (u, a) = (j, a)` -/
theorem r176l_succT_ua :
    geoSmoothingSuccessor hP T (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_u_not_mem hP q huq)]
  exact hρa

include hab hjT hρb in
/-- `ρ_T (j, a) = (v, b)` -/
theorem r176l_succT_ja :
    geoSmoothingSuccessor hP T (Sum.inr (visitOn j a (s176_mem_left hj))) = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  rw [geoSmoothingSuccessor_visit_of_mem hP T _ hjT, s176_visitTwin_eq hj hab _ _]
  exact hρb

include hvq hρc in
/-- `ρ_T (v, c) = (u, c)` -/
theorem r176l_succT_vc :
    geoSmoothingSuccessor hP T (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  rw [geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_v_not_mem hP q hvq)]
  exact hρc

include hac hj huq hρa in
/-- `ρ_{S₁} (u, c) = (j, a)` -/
theorem r176l_succS1_uc :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  have h := geoSmoothingSuccessor_insert_twin hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
  rw [r176l_twin_ua hu hac] at h
  exact h.trans (r176l_succT_ua hP q hj hu huq hρa)

include hab hac hbc hu hjT huq hρb in
/-- `ρ_{S₁} (j, a) = (v, b)` -/
theorem r176l_succS1_ja :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      Sum.inr (visitOn v b (s176_mem_left hv)) := by
  have hju : j ≠ u := r176l_j_ne_u hac hbc hj hu
  have h := geoSmoothingSuccessor_insert_other hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
    (Sum.inr (visitOn j a (s176_mem_left hj)))
    (fun e => r176l_visit_ne_of_ne hju _ _ (Sum.inr.inj e))
    (by rw [r176l_twin_ua hu hac]; exact fun e => r176l_visit_ne_of_ne hju _ _ (Sum.inr.inj e))
  exact h.trans (r176l_succT_ja hP hab hj hv hjT hρb)

include hab hac hbc huq hvq hρc in
/-- `ρ_{S₁} (v, c) = (u, c)` -/
theorem r176l_succS1_vc :
    geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have h := geoSmoothingSuccessor_insert_other hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
    (Sum.inr (visitOn v c (s176_mem_right hv)))
    (fun e => r176l_visit_ne_of_ne huv.symm _ _ (Sum.inr.inj e))
    (by rw [r176l_twin_ua hu hac]; exact fun e => r176l_visit_ne_of_ne huv.symm _ _ (Sum.inr.inj e))
  exact h.trans (r176l_succT_vc hP q hu hv hvq hρc)

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The central triangle is a `ρ_{Sf}`-3-cycle**: `(u, c) → (j, a) → (v, b) → (u, c)`. -/
theorem r176l_succSf_cycle :
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn j a (s176_mem_left hj)) ∧
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      Sum.inr (visitOn v b (s176_mem_left hv)) ∧
    geoSmoothingSuccessor hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) = Sum.inr (r176l_uc hu) := by
  have hjv : j ≠ v := r176l_j_ne_v hac hbc hj hv
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have hvS1 : v ∉ r176l_S1 T u := r176l_v_not_mem_S1 hP q hab hbc hu hv hvq
  refine ⟨?_, ?_, ?_⟩
  · have h := geoSmoothingSuccessor_insert_other hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
      (Sum.inr (r176l_uc hu)) (fun e => r176l_visit_ne_of_ne huv _ _ (Sum.inr.inj e))
      (by rw [r176l_twin_vb hv hbc]; exact fun e => r176l_visit_ne_of_ne huv _ _ (Sum.inr.inj e))
    exact h.trans (r176l_succS1_uc hP q hac hj hu huq hρa)
  · have h := geoSmoothingSuccessor_insert_other hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
      (Sum.inr (visitOn j a (s176_mem_left hj))) (fun e => r176l_visit_ne_of_ne hjv _ _ (Sum.inr.inj e))
      (by rw [r176l_twin_vb hv hbc]; exact fun e => r176l_visit_ne_of_ne hjv _ _ (Sum.inr.inj e))
    exact h.trans (r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb)
  · have h := geoSmoothingSuccessor_insert_visit hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv)) hvS1
    rw [r176l_twin_vb hv hbc] at h
    exact h.trans (r176l_succS1_vc hP q hab hac hbc hu hv huq hvq hρc)

end Case1

/-! ### L3.4 The children of the affected carrier in the full support -/

omit [NeZero n] in
/-- Membership in a 3-cycle of a permutation: the `SameCycle` class of `x` under `f` with
`f x = y`, `f y = z`, `f z = x` is `{x, y, z}`. -/
theorem r176l_sameCycle_three {α : Type*} [Fintype α] (f : Equiv.Perm α) {x y z : α}
    (hx : f x = y) (hy : f y = z) (hz : f z = x) {m : α} (h : f.SameCycle x m) :
    m = x ∨ m = y ∨ m = z := by
  obtain ⟨k, hk⟩ := h.exists_nat_pow_eq
  rw [← hk]
  clear hk h
  induction k with
  | zero => left; rfl
  | succ k ih =>
    rw [pow_succ', Equiv.Perm.mul_apply]
    rcases ih with h | h | h <;> rw [h]
    · right; left; exact hx
    · right; right; exact hy
    · left; exact hz

/-- **The two-child split** (the exact split of `geoSmoothingSuccessor_insert_child_data`, read as a
disjunction): inserting a crossing `w` whose two visits lie on one carrier of `T` sends every mark of
that carrier to the carrier of `w` or to the carrier of its twin. -/
theorem r176l_owner_insert_or (T : Finset (Crossing P)) (hI : GeoInheritsMarkOrder hP T) (w : Visit P)
    (hw : w.1 ∉ T) (hc : geoOwner hP T (Sum.inr w) = geoOwner hP T (Sum.inr (visitTwin w))) (m : Mark P)
    (hm : geoOwner hP T m = geoOwner hP T (Sum.inr w)) :
    geoOwner hP (insert w.1 T) m = geoOwner hP (insert w.1 T) (Sum.inr w) ∨
    geoOwner hP (insert w.1 T) m = geoOwner hP (insert w.1 T) (Sum.inr (visitTwin w)) := by
  obtain ⟨k, A, B, hrot, -, -, -, hleft, hright, -, -⟩ :=
    geoSmoothingSuccessor_insert_child_data hP T hI w hw hc
  have hmem : m ∈ (geoMarkList hP).rotate k := List.mem_rotate.mpr (mem_geoMarkList hP m)
  rw [hrot] at hmem
  simp only [List.mem_cons, List.mem_append] at hmem
  rcases hmem with h | h | h | h
  · left; rw [h]
  · right
    rw [hright]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨h, hm⟩
  · right; rw [h]
  · left
    rw [hleft]
    simp only [List.mem_cons, List.mem_filter, decide_eq_true_eq]
    exact Or.inr ⟨h, hm⟩

section Children

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))

/-- the central triangle `Z = owner_{Sf} (j, a)` -/
abbrev r176l_Z (T : Finset (Crossing P)) (u v : Crossing P) {j : Crossing P} {a b : ZMod n} (hj : j.val = {a, b}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj)))
/-- the clean outer carrier `Λ₁ = owner_{Sf} (v, c)` -/
abbrev r176l_L1 (T : Finset (Crossing P)) (u : Crossing P) {v : Crossing P} {b c : ZMod n} (hv : v.val = {b, c}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv)))
/-- the clean outer carrier `Λ₂ = owner_{Sf} (u, a)` -/
abbrev r176l_L2 (T : Finset (Crossing P)) (v : Crossing P) {u : Crossing P} {a c : ZMod n} (hu : u.val = {a, c}) :
    GeoComponent hP (r176l_Sf T u v) :=
  geoOwner hP (r176l_Sf T u v) (Sum.inr (r176l_ua hu))

omit [NeZero n] in
include hSf in
theorem r176l_indep_S1 : GeoIndependent hP (r176l_S1 T u) :=
  r176l_indep_mono hP hSf (r176l_S1_subset_Sf T u v)

include hab hbc hu hvq hSf in
/-- in `S₁ = T ∪ {u}` the two visits of `v` still share a carrier -/
theorem r176l_owner_S1_vb_vc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) =
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) := by
  have h := geoIndependent_remaining_pair_owners hP hSf (r176l_S1 T u) (r176l_S1_subset_Sf T u v)
    (visitOn v b (s176_mem_left hv)) (r176l_v_mem_Sf T u v) (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq)
  rwa [r176l_twin_vb hv hbc] at h

include hac hSf in
/-- in `S₁` the two visits of `u` are separated -/
theorem r176l_owner_S1_ua_ne_uc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠ geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) := by
  have h := geo_selected_visits_separated hP (r176l_indep_S1 hP hSf) (r176l_ua hu) (r176l_u_mem_S1 T u)
  rwa [r176l_twin_ua hu hac] at h

include hac huq hρa in
/-- in `S₁`, `(u, c)`, `(j, a)`, `(v, b)` share a carrier -/
theorem r176l_owner_S1_uc_ja :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) = geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) := by
  rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)), r176l_succS1_uc hP q hac hj hu huq hρa]
include hab hac hbc hu hjT huq hρb in
theorem r176l_owner_S1_ja_vb :
    geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))) =
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
  rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))),
    r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb]

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- `(u, a)` and `(v, c)` are separated in `S₁` -/
theorem r176l_owner_S1_ua_ne_vc :
    geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v c (s176_mem_right hv))) := by
  rw [← r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf, ← r176l_owner_S1_ja_vb hP q hab hac hbc hj hu hv hjT huq hρb,
    ← r176l_owner_S1_uc_ja hP q hac hj hu huq hρa]
  exact r176l_owner_S1_ua_ne_uc hP hac hu hSf

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- **The carrier of `(u, a)` is unaffected by the second insertion**: a mark lies on `Λ₂` iff it lies
on the `S₁`-carrier of `(u, a)`. -/
theorem r176l_owner_Sf_L2_iff (z : Mark P) :
    geoOwner hP (r176l_Sf T u v) z = r176l_L2 hP T v hu ↔
      geoOwner hP (r176l_S1 T u) z = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) := by
  have hc := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
  rw [← r176l_twin_vb hv hbc] at hc
  have hne : geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ≠
      geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
    rw [r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf]
    exact r176l_owner_S1_ua_ne_vc hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
  exact geoOwner_insert_iff_of_unaffected hP (r176l_S1 T u) (visitOn v b (s176_mem_left hv))
    (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq) hc _ hne (Sum.inr (r176l_ua hu)) rfl z

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the marks of the central triangle: `Z = owner (u, c) = owner (j, a) = owner (v, b)` -/
theorem r176l_Z_eq :
    geoOwner hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) = r176l_Z hP T u v hj ∧
    geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) = r176l_Z hP T u v hj := by
  obtain ⟨h1, h2, -⟩ := r176l_succSf_cycle hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  constructor
  · rw [← geoOwner_successor hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)), h1]
  · rw [show r176l_Z hP T u v hj = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) from rfl,
      ← geoOwner_successor hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))), h2]

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The central triangle owns exactly its three corner marks.** -/
theorem r176l_mem_Z (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_Z hP T u v hj) :
    m = Sum.inr (r176l_uc hu) ∨ m = Sum.inr (visitOn j a (s176_mem_left hj)) ∨
      m = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  obtain ⟨h1, h2, h3⟩ := r176l_succSf_cycle hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  have hZ := (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).1
  have hsc : (geoSmoothingSuccessor hP (r176l_Sf T u v)).SameCycle (Sum.inr (r176l_uc hu)) m :=
    (geoOwner_eq_iff hP (r176l_Sf T u v) _ _).mp (hZ.trans h.symm)
  exact r176l_sameCycle_three _ h1 h2 h3 hsc

include hab hac hbc hjT huq hvq hρa hρb hSf in
/-- `Λ₁ ≠ Λ₂` -/
theorem r176l_L1_ne_L2 : r176l_L1 hP T u hv ≠ r176l_L2 hP T v hu := by
  intro h
  exact r176l_owner_S1_ua_ne_vc hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
    ((r176l_owner_Sf_L2_iff hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf _).mp h).symm

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- `Λ₁ ≠ Z` -/
theorem r176l_L1_ne_Z : r176l_L1 hP T u hv ≠ r176l_Z hP T u v hj := by
  intro h
  have hsep := geo_selected_visits_separated hP hSf (visitOn v b (s176_mem_left hv)) (r176l_v_mem_Sf T u v)
  rw [r176l_twin_vb hv hbc, (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2] at hsep
  exact hsep h.symm

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- `Λ₂ ≠ Z` -/
theorem r176l_L2_ne_Z : r176l_L2 hP T v hu ≠ r176l_Z hP T u v hj := by
  intro h
  have hsep := geo_selected_visits_separated hP hSf (r176l_ua hu) (r176l_u_mem_Sf T u v)
  rw [r176l_twin_ua hu hac, (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).1] at hsep
  exact hsep h

include hvq hSf in
theorem r176l_sub_L1 (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) :
    geoOwner hP T m = q :=
  (geoOwner_eq_of_subset hP hSf (r176l_subset_Sf T u v) m _ h).trans (r176l_owner_vc hP q hv hvq)

include huq hSf in
theorem r176l_sub_L2 (m : Mark P) (h : geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) :
    geoOwner hP T m = q :=
  (geoOwner_eq_of_subset hP hSf (r176l_subset_Sf T u v) m _ h).trans (r176l_owner_ua hP q hu huq)

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **Every mark of `q` lies on `Λ₁`, `Λ₂` or `Z`** (the two-step split). -/
theorem r176l_owner_Sf_cases (m : Mark P) (hm : geoOwner hP T m = q) :
    geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv ∨
    geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu ∨
    geoOwner hP (r176l_Sf T u v) m = r176l_Z hP T u v hj := by
  have hI_T := geoInheritsMarkOrder_of_independent hP hT
  have hI_S1 := geoInheritsMarkOrder_of_independent hP (r176l_indep_S1 hP hSf)
  have hcT : geoOwner hP T (Sum.inr (r176l_ua hu)) = geoOwner hP T (Sum.inr (visitTwin (r176l_ua hu))) := by
    rw [r176l_twin_ua hu hac, r176l_owner_ua hP q hu huq, r176l_owner_uc hP q hu huq]
  have hstep1 := r176l_owner_insert_or hP T hI_T (r176l_ua hu) (r176l_u_not_mem hP q huq) hcT m
    (by rw [hm, r176l_owner_ua hP q hu huq])
  rw [r176l_twin_ua hu hac] at hstep1
  have hstep1' : geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) ∨
      geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)) := hstep1
  rcases hstep1' with h1 | h1
  · right; left
    exact (r176l_owner_Sf_L2_iff hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf m).mpr h1
  · have hcS1 := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
    rw [← r176l_twin_vb hv hbc] at hcS1
    have hm1 : geoOwner hP (r176l_S1 T u) m = geoOwner hP (r176l_S1 T u) (Sum.inr (visitOn v b (s176_mem_left hv))) := by
      rw [h1, r176l_owner_S1_uc_ja hP q hac hj hu huq hρa,
        r176l_owner_S1_ja_vb hP q hab hac hbc hj hu hv hjT huq hρb]
    have hstep2 := r176l_owner_insert_or hP (r176l_S1 T u) hI_S1 (visitOn v b (s176_mem_left hv))
      (r176l_v_not_mem_S1 hP q hab hbc hu hv hvq) hcS1 m hm1
    rw [r176l_twin_vb hv hbc] at hstep2
    have hstep2' : geoOwner hP (r176l_Sf T u v) m = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) ∨
        geoOwner hP (r176l_Sf T u v) m = geoOwner hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv))) := hstep2
    rcases hstep2' with h2 | h2
    · right; right
      exact h2.trans (r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc).2
    · left; exact h2

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The children of the affected carrier** (case 1): `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`. -/
theorem r176l_children_case1 : r176l_Children hP T (r176l_Sf T u v) q (r176l_L1 hP T u hv) (r176l_L2 hP T v hu) where
  sub₁ m h := r176l_sub_L1 hP q hv hvq hSf m h
  sub₂ m h := r176l_sub_L2 hP q hu huq hSf m h
  ne := r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
  cover w hw hq := by
    rcases r176l_owner_Sf_cases hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf (Sum.inr w) hq with h | h | h
    · exact Or.inl h
    · exact Or.inr h
    · exfalso
      rcases r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc _ h with e | e | e
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_u_mem_Sf T u v)
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_subset_Sf T u v hjT)
      · exact hw (by rw [Sum.inr.inj e]; exact r176l_v_mem_Sf T u v)

end Children


/-! ### L3.5 Corner marks, corner sets and the turn/angle at a corner mark -/

section CornerMarks

variable {S : Finset (Crossing P)}

open scoped Classical in
/-- The corner marks of a carrier `r` of `S` as a finset: the marks it owns that are true corners. -/
def r176l_cornerSet (S : Finset (Crossing P)) (r : GeoComponent hP S) : Finset (Mark P) :=
  Finset.univ.filter fun m => geoOwner hP S m = r ∧ IsTrueCorner S m

theorem r176l_mem_cornerSet {r : GeoComponent hP S} {m : Mark P} :
    m ∈ r176l_cornerSet hP S r ↔ geoOwner hP S m = r ∧ IsTrueCorner S m := by
  classical
  simp only [r176l_cornerSet, Finset.mem_filter, Finset.mem_univ, true_and]

/-- **Summing over the corner indices = summing over the corner marks** (`geoCornerMark` is a bijection
`ZMod c(r) ≃ cornerSet r`). -/
theorem r176l_sum_cornerMark (r : GeoComponent hP S) (f : Mark P → ℝ) :
    ∑ k : ZMod (geoCornerCount hP S r), f (geoCornerMark hP S r k) = ∑ m ∈ r176l_cornerSet hP S r, f m := by
  refine Finset.sum_nbij (geoCornerMark hP S r) ?_ ?_ ?_ ?_
  · intro k _
    exact (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP S r k)
  · intro k _ k' _ h
    exact geoCornerMark_injective hP S r h
  · intro m hm
    obtain ⟨hown, hc⟩ := (r176l_mem_cornerSet hP).mp hm
    obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP S r m hown hc
    exact ⟨k, Finset.mem_univ _, hk⟩
  · intro k _
    rfl

/-- The number of corners is the size of the corner set. -/
theorem r176l_cornerCount_eq_card (r : GeoComponent hP S) :
    geoCornerCount hP S r = (r176l_cornerSet hP S r).card := by
  have h := r176l_sum_cornerMark hP r (fun _ => (1 : ℝ))
  simp only [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul, mul_one] at h
  exact_mod_cast h

/-- The angle at a corner mark `m` of a carrier of `S`: the principal angle from the incoming original
edge to the outgoing slot's edge. -/
def r176l_tau (S : Finset (Crossing P)) (m : Mark P) : ℝ :=
  principalAngle (edge P (geoInEdge hP m)) (edge P (geoOutSlot hP S m).1)

include hn in
/-- **The principal turn of the corner polygon at `k` is the angle at its corner mark**
(`geoCornerPolygon_edge_pred_smul`, `geoCornerPolygon_edge_smul`, scale invariance of the principal angle). -/
theorem r176l_principalTurn_eq_tau (hS : GeoIndependent hP S) (r : GeoComponent hP S)
    (k : ZMod (geoCornerCount hP S r)) :
    CV.principalTurn (geoCornerPolygon hP S r) k = r176l_tau hP S (geoCornerMark hP S r k) := by
  obtain ⟨c₁, hc₁, he₁⟩ := geoCornerPolygon_edge_pred_smul hn hP hS r k
  obtain ⟨c₂, hc₂, he₂⟩ := geoCornerPolygon_edge_smul hn hP hS r k
  show principalAngle (edge (geoCornerPolygon hP S r) (k - 1)) (edge (geoCornerPolygon hP S r) k) = _
  rw [he₁, he₂, principalAngle_smul hc₁ hc₂]
  rfl

include hn in
/-- the sum of the principal turns of a carrier's corner polygon, as a sum over its corner marks -/
theorem r176l_sum_principalTurn (hS : GeoIndependent hP S) (r : GeoComponent hP S) :
    ∑ k, CV.principalTurn (geoCornerPolygon hP S r) k = ∑ m ∈ r176l_cornerSet hP S r, r176l_tau hP S m := by
  rw [← r176l_sum_cornerMark hP r (r176l_tau hP S)]
  exact Finset.sum_congr rfl fun k _ => r176l_principalTurn_eq_tau hn hP hS r k

/-- `principalAngle (-u) (-v) = principalAngle u v` (copy of the accepted `SM.principalAngle_neg_neg`,
SM/ZeroRotationSeed.lean, not imported). -/
theorem r176l_principalAngle_neg_neg (u v : Plane) : principalAngle (-u) (-v) = principalAngle u v := by
  simp only [principalAngle, cornerRotor, planeComplex_neg, star_neg, neg_mul_neg]

omit [NeZero n] in
/-- antisymmetry of the principal angle on a regular pair -/
theorem r176l_principalAngle_swap {u v : Plane} (h : RegularPair u v) :
    principalAngle v u = -principalAngle u v := by
  rw [← r176l_principalAngle_neg_neg v u]
  exact principalAngle_reverse h

omit [NeZero n] in
/-- a transverse pair is regular -/
theorem r176l_regularPair_of_det {u v : Plane} (h : det u v ≠ 0) : RegularPair u v := by
  unfold RegularPair
  refine ⟨?_, ?_, ?_⟩
  · intro hu; apply h; rw [hu]; simp [det]
  · intro hv; apply h; rw [hv]; simp [det]
  · rintro ⟨r, -, hr⟩
    apply h
    rw [hr]
    exact det_smul_self u r

omit [NeZero n] in
theorem r176l_det_self (u : Plane) : det u u = 0 := by
  have := det_smul_self u 1
  rwa [one_smul] at this

omit [NeZero n] in
theorem r176l_det_neg_right (u w : Plane) : det u (-w) = -det u w := by
  have := det_smul_right u w (-1)
  rwa [neg_one_smul, neg_one_mul] at this

omit [NeZero n] in
theorem r176l_det_neg_left (u w : Plane) : det (-u) w = -det u w := by
  have := det_smul_left u w (-1)
  rwa [neg_one_smul, neg_one_mul] at this

omit [NeZero n] in
theorem r176l_det_sub_right (u v w : Plane) : det u (v - w) = det u v - det u w := by
  rw [sub_eq_add_neg, det_add_right, r176l_det_neg_right]
  ring

omit [NeZero n] in
theorem r176l_det_sub_left (u v w : Plane) : det (u - v) w = det u w - det v w := by
  rw [det_swap, r176l_det_sub_right, det_swap u w, det_swap v w]
  ring

/-! ### the out-slot edges at the local marks -/

theorem r176l_outSlot_visit_mem {w : Visit P} (hw : w.1 ∈ S) :
    (geoOutSlot hP S (Sum.inr w)).1 = (visitTwin w).2.val := geoOutSlot_selected hP S w hw

theorem r176l_outSlot_visit_not_mem {w : Visit P} (hw : w.1 ∉ S) :
    (geoOutSlot hP S (Sum.inr w)).1 = w.2.val := by
  rw [geoOutSlot_unselected hP S w hw]; rfl

/-- the out-slot edge of a mark whose crossing is not one of the inserted ones is unchanged by the
insertion -/
theorem r176l_outSlot_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) :
    (geoOutSlot hP S' m).1 = (geoOutSlot hP S m).1 := by
  cases m with
  | inl i => rfl
  | inr w =>
    by_cases hw : w.1 ∈ S
    · rw [r176l_outSlot_visit_mem hP hw, r176l_outSlot_visit_mem hP ((h w rfl).mpr hw)]
    · rw [r176l_outSlot_visit_not_mem hP hw, r176l_outSlot_visit_not_mem hP (fun h' => hw ((h w rfl).mp h'))]

theorem r176l_tau_eq_of_iff {S S' : Finset (Crossing P)} (m : Mark P)
    (h : ∀ w : Visit P, m = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ S)) : r176l_tau hP S' m = r176l_tau hP S m := by
  unfold r176l_tau
  rw [r176l_outSlot_eq_of_iff hP m h]

end CornerMarks

/-! ### L3.6 The corner signs of the local configuration (RA (3), (6), (12)) -/

section LocalSigns

variable (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))

omit [NeZero n] in
include hP in
/-- the crossing point of a visit is the edge point at its parameter -/
theorem r176l_edgePoint_visit (w : Visit P) : edgePoint P w.2.val (visitParameter w) = crossingPoint w.1 :=
  geometricVisitPosition_evaluation hP w

include hP hj hu hv hlt_a hlt_b hlt_c in
/-- **The vector identity of the corner** (the three crossing points are the pairwise intersections
of the three lines, in the orders of case 1): `γ e_c = -α e_a - β e_b` with `α, β, γ > 0`. -/
theorem r176l_vector_identity :
    ∃ α β γ : ℝ, 0 < α ∧ 0 < β ∧ 0 < γ ∧ γ • edge P c = -(α • edge P a) - β • edge P b := by
  refine ⟨visitParameter (visitOn j a (s176_mem_left hj)) - visitParameter (r176l_ua hu),
    visitParameter (visitOn v b (s176_mem_left hv)) - visitParameter (visitOn j b (s176_mem_right hj)),
    visitParameter (r176l_uc hu) - visitParameter (visitOn v c (s176_mem_right hv)),
    sub_pos.mpr hlt_a, sub_pos.mpr hlt_b, sub_pos.mpr hlt_c, ?_⟩
  have e1 : edgePoint P a (visitParameter (r176l_ua hu)) = crossingPoint u :=
    r176l_edgePoint_visit hP (r176l_ua hu)
  have e2 : edgePoint P c (visitParameter (r176l_uc hu)) = crossingPoint u :=
    r176l_edgePoint_visit hP (r176l_uc hu)
  have e3 : edgePoint P a (visitParameter (visitOn j a (s176_mem_left hj))) = crossingPoint j :=
    r176l_edgePoint_visit hP (visitOn j a (s176_mem_left hj))
  have e4 : edgePoint P b (visitParameter (visitOn j b (s176_mem_right hj))) = crossingPoint j :=
    r176l_edgePoint_visit hP (visitOn j b (s176_mem_right hj))
  have e5 : edgePoint P b (visitParameter (visitOn v b (s176_mem_left hv))) = crossingPoint v :=
    r176l_edgePoint_visit hP (visitOn v b (s176_mem_left hv))
  have e6 : edgePoint P c (visitParameter (visitOn v c (s176_mem_right hv))) = crossingPoint v :=
    r176l_edgePoint_visit hP (visitOn v c (s176_mem_right hv))
  have hc : (visitParameter (r176l_uc hu) - visitParameter (visitOn v c (s176_mem_right hv))) • edge P c =
      crossingPoint u - crossingPoint v := by
    rw [← edgePoint_sub_edgePoint, e2, e6]
  have ha : (visitParameter (r176l_ua hu) - visitParameter (visitOn j a (s176_mem_left hj))) • edge P a =
      crossingPoint u - crossingPoint j := by
    rw [← edgePoint_sub_edgePoint, e1, e3]
  have hb : (visitParameter (visitOn v b (s176_mem_left hv)) - visitParameter (visitOn j b (s176_mem_right hj))) •
      edge P b = crossingPoint v - crossingPoint j := by
    rw [← edgePoint_sub_edgePoint, e5, e4]
  rw [hc, hb, ← neg_smul, neg_sub, ha]
  abel

include hP hj hu hv hlt_a hlt_b hlt_c in
/-- **The corner-sign ledger** (RA (6)/(12)): with `σ = sgn det(e_a, e_b)` the turn of the corner,
`sgn det(e_a, e_c) = sgn det(e_c, e_b) = -σ` and `sgn det(e_c, e_a) = sgn det(e_b, e_c) = σ`. -/
theorem r176l_local_signs :
    SignType.sign (det (edge P a) (edge P c)) = -SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P c) (edge P b)) = -SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P c) (edge P a)) = SignType.sign (det (edge P a) (edge P b)) ∧
    SignType.sign (det (edge P b) (edge P c)) = SignType.sign (det (edge P a) (edge P b)) := by
  obtain ⟨α, β, γ, hα, hβ, hγ, hvec⟩ := r176l_vector_identity hP hj hu hv hlt_a hlt_b hlt_c
  have h1 : γ * det (edge P a) (edge P c) = -β * det (edge P a) (edge P b) := by
    rw [← det_smul_right, hvec, r176l_det_sub_right, r176l_det_neg_right, det_smul_right, det_smul_right,
      r176l_det_self]
    ring
  have h2 : γ * det (edge P c) (edge P b) = -α * det (edge P a) (edge P b) := by
    rw [← det_smul_left, hvec, r176l_det_sub_left, r176l_det_neg_left, det_smul_left, det_smul_left,
      r176l_det_self]
    ring
  have hs1 : SignType.sign (det (edge P a) (edge P c)) = -SignType.sign (det (edge P a) (edge P b)) := by
    have := congrArg SignType.sign h1
    rwa [sign_mul, sign_mul, sign_pos hγ, one_mul, Left.sign_neg, sign_pos hβ, neg_one_mul] at this
  have hs2 : SignType.sign (det (edge P c) (edge P b)) = -SignType.sign (det (edge P a) (edge P b)) := by
    have := congrArg SignType.sign h2
    rwa [sign_mul, sign_mul, sign_pos hγ, one_mul, Left.sign_neg, sign_pos hα, neg_one_mul] at this
  refine ⟨hs1, hs2, ?_, ?_⟩
  · rw [det_swap, Left.sign_neg, hs1, neg_neg]
  · rw [det_swap, Left.sign_neg, hs2, neg_neg]

end LocalSigns

/-! ### L3.7 The corner sets of the three children and the one-dissent shapes (12) -/

section Shapes

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))
  {σ : SignType} (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)

include hac hbc hu hv in
/-- a true corner of `Sf` is a true corner of `T` or one of the four local visits -/
theorem r176l_isTrueCorner_Sf_iff (m : Mark P) :
    IsTrueCorner (r176l_Sf T u v) m ↔ IsTrueCorner T m ∨ m = Sum.inr (r176l_ua hu) ∨ m = Sum.inr (r176l_uc hu) ∨
      m = Sum.inr (visitOn v b (s176_mem_left hv)) ∨ m = Sum.inr (visitOn v c (s176_mem_right hv)) := by
  cases m with
  | inl i => simp only [isTrueCorner_vertex, true_or]
  | inr w =>
    simp only [isTrueCorner_visit, Sum.inr.injEq]
    constructor
    · intro h
      rcases r176l_mem_ins.mp h with h | h
      · rcases visit_eq_or_twin (visitOn v b (s176_mem_left hv)) w h with rfl | rfl
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · rw [r176l_twin_vb hv hbc]; exact Or.inr (Or.inr (Or.inr (Or.inr rfl)))
      · rcases r176l_mem_ins.mp h with h | h
        · rcases visit_eq_or_twin (r176l_ua hu) w h with rfl | rfl
          · exact Or.inr (Or.inl rfl)
          · rw [r176l_twin_ua hu hac]; exact Or.inr (Or.inr (Or.inl rfl))
        · exact Or.inl h
    · rintro (h | rfl | rfl | rfl | rfl)
      · exact r176l_subset_Sf T u v h
      · exact r176l_u_mem_Sf T u v
      · exact r176l_u_mem_Sf T u v
      · exact r176l_v_mem_Sf T u v
      · exact r176l_v_mem_Sf T u v

omit [NeZero n] in
include hab hac hbc hj hu hv in
theorem r176l_visits_ne :
    Sum.inr (r176l_uc hu) ≠ (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∧
    Sum.inr (r176l_uc hu) ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) ∧
    Sum.inr (visitOn j a (s176_mem_left hj)) ≠ (Sum.inr (visitOn v b (s176_mem_left hv)) : Mark P) := by
  refine ⟨fun e => ?_, fun e => ?_, fun e => ?_⟩
  · exact r176l_j_ne_u hac hbc hj hu (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e)).symm
  · exact r176l_u_ne_v hab hbc hu hv (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))
  · exact r176l_j_ne_v hac hbc hj hv (congrArg (fun w : Visit P => w.1) (Sum.inr.inj e))

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `Λ₁`**: the inherited corners of `q` owned by `Λ₁`, and the new corner `(v, c)`. -/
theorem r176l_mem_cornerSet_L1 (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv) ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) ∨
        m = Sum.inr (visitOn v c (s176_mem_right hv)) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet, r176l_mem_cornerSet, r176l_isTrueCorner_Sf_iff hac hbc hu hv]
  constructor
  · rintro ⟨hown, h | rfl | rfl | rfl | rfl⟩
    · exact Or.inl ⟨⟨r176l_sub_L1 hP q hv hvq hSf m hown, h⟩, hown⟩
    · exact absurd hown.symm (r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf)
    · exact absurd (hZ.1.symm.trans hown) (r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd (hZ.2.symm.trans hown) (r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact Or.inr rfl
  · rintro (⟨⟨-, hc⟩, hown⟩ | rfl)
    · exact ⟨hown, Or.inl hc⟩
    · exact ⟨rfl, Or.inr (Or.inr (Or.inr (Or.inr rfl)))⟩

include hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `Λ₂`**: the inherited corners of `q` owned by `Λ₂`, and the new corner `(u, a)`. -/
theorem r176l_mem_cornerSet_L2 (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu) ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) ∨
        m = Sum.inr (r176l_ua hu) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet, r176l_mem_cornerSet, r176l_isTrueCorner_Sf_iff hac hbc hu hv]
  constructor
  · rintro ⟨hown, h | rfl | rfl | rfl | rfl⟩
    · exact Or.inl ⟨⟨r176l_sub_L2 hP q hu huq hSf m hown, h⟩, hown⟩
    · exact Or.inr rfl
    · exact absurd (hZ.1.symm.trans hown) (r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd (hZ.2.symm.trans hown) (r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf).symm
    · exact absurd hown (r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf)
  · rintro (⟨⟨-, hc⟩, hown⟩ | rfl)
    · exact ⟨hown, Or.inl hc⟩
    · exact ⟨rfl, Or.inr (Or.inl rfl)⟩

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- **The corner set of the central triangle** is its three marks. -/
theorem r176l_mem_cornerSet_Z (m : Mark P) :
    m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) ↔
      m = Sum.inr (r176l_uc hu) ∨ m = Sum.inr (visitOn j a (s176_mem_left hj)) ∨
        m = Sum.inr (visitOn v b (s176_mem_left hv)) := by
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  rw [r176l_mem_cornerSet]
  constructor
  · rintro ⟨hown, -⟩
    exact r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc m hown
  · rintro (rfl | rfl | rfl)
    · exact ⟨hZ.1, r176l_u_mem_Sf T u v⟩
    · exact ⟨rfl, r176l_subset_Sf T u v hjT⟩
    · exact ⟨hZ.2, r176l_v_mem_Sf T u v⟩

include hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the central triangle has three corners -/
theorem r176l_cornerCount_Z : geoCornerCount hP (r176l_Sf T u v) (r176l_Z hP T u v hj) = 3 := by
  classical
  rw [r176l_cornerCount_eq_card]
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) =
      {Sum.inr (r176l_uc hu), Sum.inr (visitOn j a (s176_mem_left hj)), Sum.inr (visitOn v b (s176_mem_left hv))} := by
    ext m
    rw [r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨h1, h2, h3⟩ := r176l_visits_ne hab hac hbc hj hu hv
  rw [hset, Finset.card_insert_of_notMem, Finset.card_pair h3]
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
  exact ⟨h1, h2⟩

include hjT huq hρa in
/-- `(j, a)` is a corner mark of `q` -/
theorem r176l_ja_mem_cornerSet_q :
    (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∈ r176l_cornerSet hP T q := by
  rw [r176l_mem_cornerSet]
  refine ⟨?_, hjT⟩
  rw [← r176l_succT_ua hP q hj hu huq hρa, geoOwner_successor]
  exact r176l_owner_ua hP q hu huq

include hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- **The corner set of `q`** splits into the inherited corners of `Λ₁`, those of `Λ₂`, and `(j, a)`. -/
theorem r176l_mem_cornerSet_q (m : Mark P) :
    m ∈ r176l_cornerSet hP T q ↔
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L1 hP T u hv) ∨
      (m ∈ r176l_cornerSet hP T q ∧ geoOwner hP (r176l_Sf T u v) m = r176l_L2 hP T v hu) ∨
      m = Sum.inr (visitOn j a (s176_mem_left hj)) := by
  constructor
  · intro hm
    have hown := ((r176l_mem_cornerSet hP).mp hm).1
    rcases r176l_owner_Sf_cases hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf m hown with h | h | h
    · exact Or.inl ⟨hm, h⟩
    · exact Or.inr (Or.inl ⟨hm, h⟩)
    · right; right
      rcases r176l_mem_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc m h with rfl | rfl | rfl
      · exact absurd ((r176l_mem_cornerSet hP).mp hm).2 (r176l_u_not_mem hP q huq)
      · rfl
      · exact absurd ((r176l_mem_cornerSet hP).mp hm).2 (r176l_v_not_mem hP q hvq)
  · rintro (⟨h, -⟩ | ⟨h, -⟩ | rfl)
    · exact h
    · exact h
    · exact r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa

/-! ### the turns at the corner marks -/

include hn hP hT q hab hj hu hjT huq hρa huni in
/-- `σ = sgn det(e_a, e_b)`: the uniform turn sign of `q` is its turn at the corner `(j, a)`. -/
theorem r176l_sigma_eq : SignType.sign (det (edge P a) (edge P b)) = σ := by
  obtain ⟨k, hk⟩ := geoCornerMark_exists_of_owner hP T q _
    ((r176l_mem_cornerSet hP).mp (r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa)).1 hjT
  have h := geoCornerPolygon_turn_eq_sign_of_independent hn hP hT q k
  rw [huni k, hk, geoInEdge_visit hn, r176l_outSlot_visit_mem hP hjT,
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)] at h
  exact h.symm

include hn hT huni in
/-- an inherited corner of a child has the turn of `q` there -/
theorem r176l_turn_inherited {S' : Finset (Crossing P)} (hS' : GeoIndependent hP S') (r : GeoComponent hP S')
    (k : ZMod (geoCornerCount hP S' r)) (hm : geoCornerMark hP S' r k ∈ r176l_cornerSet hP T q)
    (hiff : ∀ w : Visit P, geoCornerMark hP S' r k = Sum.inr w → (w.1 ∈ S' ↔ w.1 ∈ T)) :
    turn (geoCornerPolygon hP S' r) k = σ := by
  obtain ⟨hown, hc⟩ := (r176l_mem_cornerSet hP).mp hm
  obtain ⟨k', hk'⟩ := geoCornerMark_exists_of_owner hP T q _ hown hc
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hS' r k, r176l_outSlot_eq_of_iff hP _ hiff, ← huni k',
    geoCornerPolygon_turn_eq_sign_of_independent hn hP hT q k', hk']

/-- the crossing of an inherited corner is in `Sf` iff in `T` -/
theorem r176l_iff_of_cornerSet_q {m : Mark P} (hm : m ∈ r176l_cornerSet hP T q) (w : Visit P) (hw : m = Sum.inr w) :
    w.1 ∈ r176l_Sf T u v ↔ w.1 ∈ T := by
  have hc := ((r176l_mem_cornerSet hP).mp hm).2
  rw [hw] at hc
  exact ⟨fun _ => hc, fun h => r176l_subset_Sf T u v h⟩

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **(12) for `Λ₁`**: every turn is `σ` except the one at the new corner `(v, c)`, which is `-σ`. -/
theorem r176l_shape_L1 : r176l_OneDissentShape (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨-, hcb, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (r176l_Sf T u v) (r176l_L1 hP T u hv)
    (Sum.inr (visitOn v c (s176_mem_right hv))) rfl (r176l_v_mem_Sf T u v)
  refine ⟨k₀, ?_, fun k hk => ?_⟩
  · rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k₀, hk₀, geoInEdge_visit hn,
      r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vc hv hbc]
    show SignType.sign (det (edge P c) (edge P b)) = -σ
    rw [hcb, hσ]
  · have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_L1 hP T u hv) k)
    rcases (r176l_mem_cornerSet_L1 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf _).mp hmem with ⟨hq, -⟩ | he
    · exact r176l_turn_inherited hn hP hT q huni hSf _ k hq (r176l_iff_of_cornerSet_q hP q hq)
    · exact absurd (geoCornerMark_injective hP _ _ (he.trans hk₀.symm)) hk

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **(12) for `Λ₂`**: every turn is `σ` except the one at the new corner `(u, a)`, which is `-σ`. -/
theorem r176l_shape_L2 : r176l_OneDissentShape (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨hac', -, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  obtain ⟨k₀, hk₀⟩ := geoCornerMark_exists_of_owner hP (r176l_Sf T u v) (r176l_L2 hP T v hu)
    (Sum.inr (r176l_ua hu)) rfl (r176l_u_mem_Sf T u v)
  refine ⟨k₀, ?_, fun k hk => ?_⟩
  · rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k₀, hk₀, geoInEdge_visit hn,
      r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_ua hu hac]
    show SignType.sign (det (edge P a) (edge P c)) = -σ
    rw [hac', hσ]
  · have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_L2 hP T v hu) k)
    rcases (r176l_mem_cornerSet_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf _).mp hmem with ⟨hq, -⟩ | he
    · exact r176l_turn_inherited hn hP hT q huni hSf _ k hq (r176l_iff_of_cornerSet_q hP q hq)
    · exact absurd (geoCornerMark_injective hP _ _ (he.trans hk₀.symm)) hk

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni in
/-- **The central triangle is uniform with sign `σ`.** -/
theorem r176l_turn_Z (k : ZMod (geoCornerCount hP (r176l_Sf T u v) (r176l_Z hP T u v hj))) :
    turn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) k = σ := by
  have hσ := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨-, -, hca, hbc'⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  have hmem := (r176l_mem_cornerSet hP).mpr (geoCornerMark_mem hP (r176l_Sf T u v) (r176l_Z hP T u v hj) k)
  rw [geoCornerPolygon_turn_eq_sign_of_independent hn hP hSf _ k]
  rcases (r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc _).mp hmem with h | h | h
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_uc hu hac]
    exact hca.trans hσ
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_subset_Sf T u v hjT),
      s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
    exact hσ
  · rw [h, geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vb hv hbc]
    exact hbc'.trans hσ

end Shapes

/-! ### L3.8 The rotation ledger (13): signed additivity through the corner angles -/

section RotAdd

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hρc : geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu))
  {σ : SignType} (hσ : σ ≠ 0) (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)
  (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
    CV.Regular (geoCornerPolygon hP S r))

open scoped Classical in
/-- the inherited corners of `q` lying on a child `r` of the full support -/
def r176l_inherited (S : Finset (Crossing P)) (r : GeoComponent hP S) : Finset (Mark P) :=
  (r176l_cornerSet hP T q).filter fun m => geoOwner hP S m = r

theorem r176l_mem_inherited {S : Finset (Crossing P)} {r : GeoComponent hP S} {m : Mark P} :
    m ∈ r176l_inherited hP q S r ↔ m ∈ r176l_cornerSet hP T q ∧ geoOwner hP S m = r := by
  classical
  simp only [r176l_inherited, Finset.mem_filter]

/-- on inherited corners the angle in `Sf` is the angle in `T` -/
theorem r176l_sum_inherited_tau {r : GeoComponent hP (r176l_Sf T u v)} :
    ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) r, r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) r, r176l_tau hP T m := by
  refine Finset.sum_congr rfl fun m hm => ?_
  exact r176l_tau_eq_of_iff hP m (r176l_iff_of_cornerSet_q hP q ((r176l_mem_inherited hP q).mp hm).1)

/-! the five local angles -/

include hn hbc in
theorem r176l_tau_vc : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn v c (s176_mem_right hv))) =
    principalAngle (edge P c) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vc hv hbc]
  rfl
include hn hbc in
theorem r176l_tau_vb : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn v b (s176_mem_left hv))) =
    principalAngle (edge P b) (edge P c) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_v_mem_Sf T u v), r176l_twin_vb hv hbc]
  rfl
include hn hac in
theorem r176l_tau_ua : r176l_tau hP (r176l_Sf T u v) (Sum.inr (r176l_ua hu)) =
    principalAngle (edge P a) (edge P c) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_ua hu hac]
  rfl
include hn hac in
theorem r176l_tau_uc : r176l_tau hP (r176l_Sf T u v) (Sum.inr (r176l_uc hu)) =
    principalAngle (edge P c) (edge P a) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_u_mem_Sf T u v), r176l_twin_uc hu hac]
  rfl
include hn hab hjT in
theorem r176l_tau_ja_Sf : r176l_tau hP (r176l_Sf T u v) (Sum.inr (visitOn j a (s176_mem_left hj))) =
    principalAngle (edge P a) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP (r176l_subset_Sf T u v hjT),
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
  rfl
include hn hab hjT in
theorem r176l_tau_ja_T : r176l_tau hP T (Sum.inr (visitOn j a (s176_mem_left hj))) =
    principalAngle (edge P a) (edge P b) := by
  unfold r176l_tau
  rw [geoInEdge_visit hn, r176l_outSlot_visit_mem hP hjT,
    s176_visitTwin_eq hj hab (s176_mem_left hj) (s176_mem_right hj)]
  rfl

include hn hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `Λ₁` -/
theorem r176l_sum_tau_L1 :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP T m +
        principalAngle (edge P c) (edge P b) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_L1 hP T u hv) =
      insert (Sum.inr (visitOn v c (s176_mem_right hv)) : Mark P)
        (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv)) := by
    ext m
    rw [r176l_mem_cornerSet_L1 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, Finset.mem_insert,
      r176l_mem_inherited]
    tauto
  have hnot : (Sum.inr (visitOn v c (s176_mem_right hv)) : Mark P) ∉
      r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) := by
    intro h
    exact r176l_v_not_mem hP q hvq ((r176l_mem_cornerSet hP).mp ((r176l_mem_inherited hP q).mp h).1).2
  rw [hset, Finset.sum_insert hnot, r176l_sum_inherited_tau hP q, r176l_tau_vc hn hP hbc hv, add_comm]

include hn hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `Λ₂` -/
theorem r176l_sum_tau_L2 :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP (r176l_Sf T u v) m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP T m +
        principalAngle (edge P a) (edge P c) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_L2 hP T v hu) =
      insert (Sum.inr (r176l_ua hu) : Mark P) (r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    ext m
    rw [r176l_mem_cornerSet_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, Finset.mem_insert,
      r176l_mem_inherited]
    tauto
  have hnot : (Sum.inr (r176l_ua hu) : Mark P) ∉ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu) := by
    intro h
    exact r176l_u_not_mem hP q huq ((r176l_mem_cornerSet hP).mp ((r176l_mem_inherited hP q).mp h).1).2
  rw [hset, Finset.sum_insert hnot, r176l_sum_inherited_tau hP q, r176l_tau_ua hn hP hac hu, add_comm]

include hn hab hac hbc hjT huq hvq hρa hρb hρc in
/-- the angle sum of the central triangle -/
theorem r176l_sum_tau_Z :
    ∑ m ∈ r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj), r176l_tau hP (r176l_Sf T u v) m =
      principalAngle (edge P c) (edge P a) + principalAngle (edge P a) (edge P b) +
        principalAngle (edge P b) (edge P c) := by
  classical
  have hset : r176l_cornerSet hP (r176l_Sf T u v) (r176l_Z hP T u v hj) =
      {Sum.inr (r176l_uc hu), Sum.inr (visitOn j a (s176_mem_left hj)), Sum.inr (visitOn v b (s176_mem_left hv))} := by
    ext m
    rw [r176l_mem_cornerSet_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc]
    simp only [Finset.mem_insert, Finset.mem_singleton]
  obtain ⟨h1, h2, h3⟩ := r176l_visits_ne hab hac hbc hj hu hv
  rw [hset, Finset.sum_insert (by simp only [Finset.mem_insert, Finset.mem_singleton, not_or]; exact ⟨h1, h2⟩),
    Finset.sum_insert (by simp only [Finset.mem_singleton]; exact h3), Finset.sum_singleton,
    r176l_tau_uc hn hP hac hu, r176l_tau_ja_Sf hn hP hab hj hjT, r176l_tau_vb hn hP hbc hv]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf in
/-- the angle sum of `q` -/
theorem r176l_sum_tau_q :
    ∑ m ∈ r176l_cornerSet hP T q, r176l_tau hP T m =
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv), r176l_tau hP T m +
      ∑ m ∈ r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu), r176l_tau hP T m +
        principalAngle (edge P a) (edge P b) := by
  classical
  have hZ := r176l_Z_eq hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc
  have hset : r176l_cornerSet hP T q =
      insert (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P)
        (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) ∪
          r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    ext m
    rw [Finset.mem_insert, Finset.mem_union, r176l_mem_inherited, r176l_mem_inherited]
    constructor
    · intro hm
      rcases (r176l_mem_cornerSet_q hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf m).mp hm with h | h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
      · exact Or.inl h
    · rintro (rfl | ⟨h, -⟩ | ⟨h, -⟩)
      · exact r176l_ja_mem_cornerSet_q hP q hj hu hjT huq hρa
      · exact h
      · exact h
  have hnot : (Sum.inr (visitOn j a (s176_mem_left hj)) : Mark P) ∉
      r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv) ∪
        r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu) := by
    intro h
    rcases Finset.mem_union.mp h with h | h
    · exact r176l_L1_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
        ((r176l_mem_inherited hP q).mp h).2.symm
    · exact r176l_L2_ne_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
        ((r176l_mem_inherited hP q).mp h).2.symm
  have hdisj : Disjoint (r176l_inherited hP q (r176l_Sf T u v) (r176l_L1 hP T u hv))
      (r176l_inherited hP q (r176l_Sf T u v) (r176l_L2 hP T v hu)) := by
    rw [Finset.disjoint_left]
    intro m h1 h2
    exact r176l_L1_ne_L2 hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf
      (((r176l_mem_inherited hP q).mp h1).2.symm.trans ((r176l_mem_inherited hP q).mp h2).2)
  rw [hset, Finset.sum_insert hnot, Finset.sum_union hdisj, r176l_tau_ja_T hn hP hab hj hjT]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ huni in
/-- **Signed additivity of the principal-turn sums**: the two new turns at each smoothing site are
opposite (`principalAngle` antisymmetry on the transverse pairs), every inherited turn is unchanged. -/
theorem r176l_sum_principalTurn_add :
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) k +
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) k +
    ∑ k, CV.principalTurn (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) k =
    ∑ k, CV.principalTurn (geoCornerPolygon hP T q) k := by
  have hσab := r176l_sigma_eq hn hP hT q hab hj hu hjT huq hρa huni
  obtain ⟨hac', hcb, -, -⟩ := r176l_local_signs hP hj hu hv hlt_a hlt_b hlt_c
  have hne_cb : det (edge P c) (edge P b) ≠ 0 := by
    intro h0
    rw [h0, sign_zero, hσab] at hcb
    cases σ with
    | zero => exact hσ rfl
    | pos => exact absurd hcb (by decide)
    | neg => exact absurd hcb (by decide)
  have hne_ac : det (edge P a) (edge P c) ≠ 0 := by
    intro h0
    rw [h0, sign_zero, hσab] at hac'
    cases σ with
    | zero => exact hσ rfl
    | pos => exact absurd hac' (by decide)
    | neg => exact absurd hac' (by decide)
  have hswap1 : principalAngle (edge P b) (edge P c) = -principalAngle (edge P c) (edge P b) :=
    r176l_principalAngle_swap (r176l_regularPair_of_det hne_cb)
  have hswap2 : principalAngle (edge P c) (edge P a) = -principalAngle (edge P a) (edge P c) :=
    r176l_principalAngle_swap (r176l_regularPair_of_det hne_ac)
  rw [r176l_sum_principalTurn hn hP hSf, r176l_sum_principalTurn hn hP hSf, r176l_sum_principalTurn hn hP hSf,
    r176l_sum_principalTurn hn hP hT, r176l_sum_tau_L1 hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
    r176l_sum_tau_L2 hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf,
    r176l_sum_tau_Z hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc,
    r176l_sum_tau_q hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf, hswap1, hswap2]
  ring

include hn hT hab hac hbc hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ huni hreg in
/-- **(13), signed form (case 1)**: `rot(q) = rot(Λ₁) + rot(Λ₂) + σ` (turnlift (ii) on the four
polygons, the central triangle having rotation `σ`). -/
theorem r176l_rot_add_case1 :
    CV.rot (geoCornerPolygon hP T q) (hreg T q hT) =
      CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) (hreg _ _ hSf) +
      CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) (hreg _ _ hSf) + (σ : ℤ) := by
  have hZ : CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_Z hP T u v hj)) (hreg _ _ hSf) = (σ : ℤ) :=
    r176l_rot_uniform_three (hreg _ _ hSf) (r176l_cornerCount_Z hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc) hσ
      (r176l_turn_Z hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni)
  have hsum := r176l_sum_principalTurn_add hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b
    hlt_c hσ huni
  rw [← CV.two_pi_mul_rot _ (hreg _ _ hSf), ← CV.two_pi_mul_rot _ (hreg _ _ hSf), ← CV.two_pi_mul_rot _ (hreg _ _ hSf),
    ← CV.two_pi_mul_rot _ (hreg T q hT), hZ] at hsum
  have hpi : (2 * Real.pi) ≠ 0 := by positivity
  have h : ((CV.rot (geoCornerPolygon hP T q) (hreg T q hT) : ℤ) : ℝ) =
      ((CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L1 hP T u hv)) (hreg _ _ hSf) : ℤ) : ℝ) +
        ((CV.rot (geoCornerPolygon hP (r176l_Sf T u v) (r176l_L2 hP T v hu)) (hreg _ _ hSf) : ℤ) : ℝ) +
        (((σ : ℤ) : ℤ) : ℝ) := by
    apply mul_left_cancel₀ hpi
    linarith
  rw [← Int.cast_add, ← Int.cast_add] at h
  exact Int.cast_injective h

end RotAdd

/-! ### L3.9 The forced orientation on `c`, the selected part, and the case-1 ledger bundle -/

section Case1Bundle

omit [NeZero n] in
include hP in
/-- distinct crossings on one edge have distinct visit parameters (injectivity of the geometric visit
position) -/
theorem r176l_param_ne {x y : Crossing P} (hxy : x ≠ y) {ℓ : ZMod n} (hx : ℓ ∈ x.val) (hy : ℓ ∈ y.val) :
    visitParameter (visitOn x ℓ hx) ≠ visitParameter (visitOn y ℓ hy) := by
  intro h
  have hpos : geometricVisitPosition hP (visitOn x ℓ hx) = geometricVisitPosition hP (visitOn y ℓ hy) :=
    Prod.ext rfl (Subtype.ext h)
  exact hxy (congrArg (fun w : Visit P => w.1) (geometricVisitPosition_injective hP hpos))

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hnb_c : ∀ w : Visit P, w.2.val = c →
    ¬ (visitParameter (r176l_uc hu) < visitParameter w ∧ visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧ visitParameter w < visitParameter (r176l_uc hu)))

include hn hab hac hbc hjT huq hvq hρa hρb hSf hnb_c in
/-- **The orientation of `c` is forced by the independence of `S_full`**: with `u` before `j` on `a` and
`j` before `v` on `b`, the order `u` before `v` on `c` would make the two visits of `v` lie on the two
different `S₁`-children of `q` (against `geoIndependent_remaining_pair_owners`); hence `v` is before
`u` on `c`, and the two `c`-visits are `ρ`-adjacent in that order. -/
theorem r176l_lt_c_of_indep :
    visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu) ∧
    geoMarkSuccessor hP (Sum.inr (visitOn v c (s176_mem_right hv))) = Sum.inr (r176l_uc hu) := by
  have huv : u ≠ v := r176l_u_ne_v hab hbc hu hv
  have hne := r176l_param_ne hP huv (s176_mem_right hu) (s176_mem_right hv)
  have hlt_c : visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter (r176l_uc hu) := by
    by_contra hnot
    have hlt : visitParameter (r176l_uc hu) < visitParameter (visitOn v c (s176_mem_right hv)) :=
      lt_of_le_of_ne (not_lt.mp hnot) hne
    have hρc' : geoMarkSuccessor hP (Sum.inr (r176l_uc hu)) = Sum.inr (visitOn v c (s176_mem_right hv)) :=
      gu1_markSuccessor_eq_of_adjacent hn hP rfl hlt (fun w hw => (hnb_c w hw).1)
    -- in `S₁`: `(u, a) → (v, c)` and `(u, c) → (j, a) → (v, b)`
    have h1 : geoSmoothingSuccessor hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)) =
        Sum.inr (visitOn v c (s176_mem_right hv)) := by
      have h := geoSmoothingSuccessor_insert_visit hP T (r176l_ua hu) (r176l_u_not_mem hP q huq)
      rw [r176l_twin_ua hu hac, geoSmoothingSuccessor_visit_of_not_mem hP T _ (r176l_u_not_mem hP q huq), hρc'] at h
      exact h
    have h2 := r176l_succS1_uc hP q hac hj hu huq hρa
    have h3 := r176l_succS1_ja hP q hab hac hbc hj hu hv hjT huq hρb
    have hcS1 := r176l_owner_S1_vb_vc hP q hab hbc hu hv hvq hSf
    have hsep := r176l_owner_S1_ua_ne_uc hP hac hu hSf
    apply hsep
    rw [← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_ua hu)), h1, ← hcS1,
      ← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (r176l_uc hu)), h2,
      ← geoOwner_successor hP (r176l_S1 T u) (Sum.inr (visitOn j a (s176_mem_left hj))), h3]
  exact ⟨hlt_c, gu1_markSuccessor_eq_of_adjacent hn hP rfl hlt_c (fun w hw => (hnb_c w hw).2)⟩

include hv huq hvq in
/-- the retained crossings of `q` selected in `Sf` are exactly `u, v` -/
theorem r176l_selectedPart_eq :
    r176l_selectedPart hP T (r176l_Sf T u v) q = {u, v} := by
  classical
  ext x
  simp only [r176l_selectedPart, Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · rintro ⟨hx, hxSf⟩
    rcases hxSf with h | h | h
    · exact Or.inr h
    · exact Or.inl h
    · exact absurd h ((mem_geoCarrierCrossings hP T q x).mp hx).1
  · rintro (h | h)
    · rw [h]; exact ⟨huq, Or.inr (Or.inl rfl)⟩
    · rw [h]; exact ⟨hvq, Or.inl rfl⟩

include hab hbc hu hv huq hvq in
theorem r176l_selectedPart_card : (r176l_selectedPart hP T (r176l_Sf T u v) q).card = 2 := by
  rw [r176l_selectedPart_eq hP q hv huq hvq, Finset.card_pair (r176l_u_ne_v hab hbc hu hv)]

end Case1Bundle

/-- **The geometric ledger of the affected carrier** on a full support `Sf ⊇ S'` with its two clean
outer children `Λ₁, Λ₂` and the uniform sign `σ` (the content of (14), (13), (12) that this unit owes
beyond the smoothing black box): the children property, the retained-set count, the two one-dissent
shapes and the signed rotation additivity. -/
structure r176l_LedgerData (hP : CrossingGeometry P) (S' Sf : Finset (Crossing P)) (hS' : GeoIndependent hP S')
    (hSf : GeoIndependent hP Sf) (q' : GeoComponent hP S') (Λ₁ Λ₂ : GeoComponent hP Sf) (σ : SignType)
    (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
      CV.Regular (geoCornerPolygon hP S r)) : Prop where
  subset : S' ⊆ Sf
  children : r176l_Children hP S' Sf q' Λ₁ Λ₂
  card : (geoCarrierCrossings hP S' q').card =
    (geoCarrierCrossings hP Sf Λ₁).card + (geoCarrierCrossings hP Sf Λ₂).card +
      (r176l_mixedSet hP S' Sf q' Λ₁ Λ₂).card + 2
  shape₁ : r176l_OneDissentShape (geoCornerPolygon hP Sf Λ₁) σ
  shape₂ : r176l_OneDissentShape (geoCornerPolygon hP Sf Λ₂) σ
  rot_add : CV.rot (geoCornerPolygon hP S' q') (hreg S' q' hS') =
    CV.rot (geoCornerPolygon hP Sf Λ₁) (hreg Sf Λ₁ hSf) + CV.rot (geoCornerPolygon hP Sf Λ₂) (hreg Sf Λ₂ hSf) + (σ : ℤ)

section Case1Ledger

variable (hρa : geoMarkSuccessor hP (Sum.inr (r176l_ua hu)) = Sum.inr (visitOn j a (s176_mem_left hj)))
  (hρb : geoMarkSuccessor hP (Sum.inr (visitOn j b (s176_mem_right hj))) = Sum.inr (visitOn v b (s176_mem_left hv)))
  (hSf : GeoIndependent hP (r176l_Sf T u v))
  (hlt_a : visitParameter (r176l_ua hu) < visitParameter (visitOn j a (s176_mem_left hj)))
  (hlt_b : visitParameter (visitOn j b (s176_mem_right hj)) < visitParameter (visitOn v b (s176_mem_left hv)))
  (hnb_c : ∀ w : Visit P, w.2.val = c →
    ¬ (visitParameter (r176l_uc hu) < visitParameter w ∧ visitParameter w < visitParameter (visitOn v c (s176_mem_right hv))) ∧
    ¬ (visitParameter (visitOn v c (s176_mem_right hv)) < visitParameter w ∧ visitParameter w < visitParameter (r176l_uc hu)))
  {σ : SignType} (hσ : σ ≠ 0) (huni : ∀ k, turn (geoCornerPolygon hP T q) k = σ)
  (hreg : ∀ (S : Finset (Crossing P)) (r : GeoComponent hP S), GeoIndependent hP S →
    CV.Regular (geoCornerPolygon hP S r))

include hn hT hab hac hbc hjT huq hvq hρa hρb hSf hlt_a hlt_b hnb_c hσ huni hreg in
/-- **The ledger of case 1**: `Sf = T ∪ {u, v}`, `Λ₁ = owner (v, c)`, `Λ₂ = owner (u, a)`. -/
theorem r176l_ledgerData_case1 :
    r176l_LedgerData hP T (r176l_Sf T u v) hT hSf q (r176l_L1 hP T u hv) (r176l_L2 hP T v hu) σ hreg := by
  obtain ⟨hlt_c, hρc⟩ := r176l_lt_c_of_indep hn hP q hab hac hbc hj hu hv hjT huq hvq hρa hρb hSf hnb_c
  have hC := r176l_children_case1 hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf
  exact
    { subset := r176l_subset_Sf T u v
      children := hC
      card := by
        rw [r176l_card_retained hP (r176l_subset_Sf T u v) hC, r176l_selectedPart_card hP q hab hbc hu hv huq hvq]
      shape₁ := r176l_shape_L1 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni
      shape₂ := r176l_shape_L2 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c huni
      rot_add := r176l_rot_add_case1 hn hP hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf hlt_a hlt_b hlt_c hσ
        huni hreg }

end Case1Ledger

end L3

/-! ## §L4. The event level -/

section L4

variable {E : CV.Event n} {e f g : ZMod n} {δ : ℝ}

/-- **`S_full = Q' ∪ {j', u', v'}` is independent on `L`** (R-LOC-2 (4) full availability, R-LOC-2
corollary: the local graph is empty on `L`): `u', v'` interlace no member of `S'` (`est_mem_U_L`) and
not each other (`complement_on_triangle` against the `K3` side). -/
theorem r176l_Sf_indep_event (hL : LocalizationData E e f g δ) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {hef' : IsCrossing (E.curve t) {e, f}} {heg' : IsCrossing (E.curve t) {e, g}}
    {hfg' : IsCrossing (E.curve t) {f, g}} (hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j u v : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (hu : u.val ∈ triangleSupports e f g)
    (hv : v.val ∈ triangleSupports e f g) (hju : j ≠ u) (hjv : j ≠ v) (huv : u ≠ v) :
    GeoIndependent (geomAt E t' ht'.1)
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) := by
  have hT : GeoIndependent (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) :=
    CV.geoIndependent_of_mem_Ind _ (est_S'_ind hL ht ht' hop hs hQ hfull hj)
  have hU := (CV.mem_U_iff _ _ _).mp (est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hu hju)
  have hV := (CV.mem_U_iff _ _ _).mp (est_mem_U_L hL ht ht' hop hs hcomp hQ hfull hj hv hjv)
  have huv' : ¬ GeometricInterlaces (geomAt E t' ht'.1) (crossingTransport hs u) (crossingTransport hs v) := by
    rw [hL.complement_on_triangle t t' ht ht' hop hs u v hu hv huv]
    exact fun h => h (est_interlaces_of_complete ht.1 hcomp hu hv huv)
  intro x hx y hy hxy
  rcases r176l_mem_ins.mp hx with rfl | hx <;> rcases r176l_mem_ins.mp hy with rfl | hy
  · exact absurd rfl hxy
  · rcases r176l_mem_ins.mp hy with rfl | hy
    · exact fun h => huv' (geometricInterlaces_symm _ h)
    · exact hV.2 y hy
  · rcases r176l_mem_ins.mp hx with rfl | hx
    · exact huv'
    · exact fun h => hV.2 x hx (geometricInterlaces_symm _ h)
  · rcases r176l_mem_ins.mp hx with rfl | hx <;> rcases r176l_mem_ins.mp hy with rfl | hy
    · exact absurd rfl hxy
    · exact hU.2 y hy
    · exact fun h => hU.2 x hx (geometricInterlaces_symm _ h)
    · exact hT x hx y hy hxy

/-- **Uniformity is carried across the wall**: the copy of a uniform carrier is uniform with the same
sign (corner turns are carried, `GT_turn_tcp`). -/
theorem r176l_uniform_transport (hn : 3 ≤ n) (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ)
    (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g) {t t' : E.Parameter} (ht : Punctured E δ t)
    (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    {Q : Finset (Crossing (E.curve t))} (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) {j : Crossing (E.curve t)}
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    {σ : SignType} (huni : ∀ k, turn (geoCornerPolygon (geomAt E t ht.1) (Q ∪ {j}) q) k = σ) :
    ∀ k, turn (geoCornerPolygon (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) k = σ := by
  intro k
  set W := est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj
  rw [GT_cornerPolygon_eq W q, turn_geoRecast, GT_turn_tcp W hn q]
  exact huni _

/-- **The SMOOTH unit's black box at the event level** (Prop, never mapped here): for every labelled
case-1 configuration of the affected carrier `q₀' = GT_carrierEquiv W q` on `L` — labels `a, b, c`, the
selected corner `j' = {a, b}`, the two retained local crossings `u' = {a, c}`, `v' = {b, c}`, the
orientation `u' <_a j'`, `j' <_b v'`, and the full support `Sf = S' ∪ {u', v'}` — and for the lift `y`
of either local crossing, the smoothing data `r176l_SmoothData` at `Sf` with the two clean outer carriers
`Λ₁ = owner_{Sf} (v', c)`, `Λ₂ = owner_{Sf} (u', a)` of this unit. -/
def r176l_smooth_black_box : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j}))
    (a b c : ZMod n) (_hab : a ≠ b) (_hac : a ≠ c) (_hbc : b ≠ c) (u v : Crossing (E.curve t))
    (_hjab : j.val = {a, b}) (huac : u.val = {a, c}) (hvbc : v.val = {b, c})
    (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (hv' : crossingTransport hs v ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q))
    (_hlt_a : visitParameter (visitOn (crossingTransport hs u) a (s176_mem_left huac)) <
      visitParameter (visitOn (crossingTransport hs j) a (s176_mem_left _hjab)))
    (hSf : r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v) ∈
      CV.Ind (geomAt E t' ht'.1))
    (y : (CV.carrierDiagram hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)).Γ.Crossing)
    (_hy : y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu' ∨
      y = est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hv'),
    Nonempty (r176l_SmoothData hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj)
      (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q) y
      (r176l_Sf (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (crossingTransport hs v)) hSf
      (r176l_L1 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs u) (v := crossingTransport hs v) hvbc)
      (r176l_L2 (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j})) (crossingTransport hs v) (u := crossingTransport hs u) huac))

/-- **The non-move port data at a labelled case-1 configuration** (event level): the geometric ledger
of §L3 on the `L` side, the writhe shift (7) across the wall, `R(D₊) = R(D₀)`, the SMOOTH black box. -/
theorem r176l_portDataRest_case1 (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
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
  -- the smoothing black box
  obtain ⟨D⟩ := hsmooth n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q a b c hab hac hbc u v
    hjab huac hvbc hu' hv' hlt_a hSf' y hy
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

/-- **The non-move port data at a labelled configuration, either orientation**: case 1 directly, case 2
as case 1 on the relabelled data `(b, a, c), (j, v, u)` (`s176_cyclic` forces `v' <_b j'`). -/
theorem r176l_portDataRest_labelled (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
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
  · exact r176l_portDataRest_case1 hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hab hac hbc
      habc hjab huac hvbc hu hv hju hjv huv hu' hv' hlt _ (Or.inl rfl)
  · -- case 2: relabel `(b, a, c), (j, v, u)`
    have hnlt : ¬ visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) <
        visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) :=
      fun h => lt_asymm hgt (hcyc.mpr h)
    have hlt_b : visitParameter (visitOn (crossingTransport hs v) b (s176_mem_left hvbc)) <
        visitParameter (visitOn (crossingTransport hs j) b (s176_mem_right hjab)) :=
      lt_of_le_of_ne (not_lt.mp hnlt) (r176l_param_ne (geomAt E t' ht'.1) hjv' (s176_mem_left hvbc) (s176_mem_right hjab))
    have habc' : ({b, a, c} : Finset (ZMod n)) = {e, f, g} := (Finset.insert_comm b a {c}).trans habc
    exact r176l_portDataRest_case1 hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind
      (a := b) (b := a) (c := c) hab.symm hbc hac habc' (u := v) (v := u) (s176_pair_comm' hjab) hvbc huac hv hu hjv hju
      huv.symm hv' hu' hlt_b _ (Or.inr rfl)

/-- **The `hrest` obligation of `s176_est_port_relation_weak_of'` under `wind(S) ≠ 0`** (the non-move
port data of row 176, from the SMOOTH black box): six relabellings of `r176l_portDataRest_labelled`. -/
theorem r176l_portDataRest_of_uniform (hsmooth : r176l_smooth_black_box) (hn : 3 ≤ n)
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
      r176l_portDataRest_labelled hsmooth hn hL hR hef heg hfg ht ht' hop hs hcomp hQ hfull hj q hwind hu hju hu'
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

end L4

/-! ## §L5. The corrected interface: the port data under `wind(S) ≠ 0`

The fields `rot` (13) and `alt₁ alt₂` (12) of `est_PortData` need the affected carrier to be UNIFORM (RA
§3: "Assume [the common singleton selector] is nonzero. Then the affected singleton carrier is uniform;
by (6), all its corners have sign `σ`"): on a mixed affected carrier the inherited corners of an outer
carrier carry both signs, so `UniformOrOneDissentCV` and `R = R₁ + R₂ + 1` can fail.  The printed proof
does not need the port data there — for `wind(S) = 0` both row terms in (2) are `0` (`wind` is carried
across the wall, `GT_wind_eq`).  So the interface Props are restated with the hypothesis
`CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0`; the consumer (`est_row_H` / `s176_est_row_H_weak`) must split on
`wind(S) = 0` — a RALedgers change, reported, not made here. -/

/-- `RProof.est_port_relation` with the additional hypothesis `wind(S) ≠ 0` (otherwise byte-identical). -/
def r176l_est_port_relation_uniform : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
    (∃ u : Crossing (E.curve t), u.val ∈ triangleSupports e f g ∧ u ≠ j ∧
      crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)) →
    ∃ (u : Crossing (E.curve t)) (_ : u.val ∈ triangleSupports e f g) (_ : u ≠ j)
      (hu' : crossingTransport hs u ∈ geoCarrierCrossings (geomAt E t' ht'.1) (transportSupport hs (Q ∪ {j}))
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)),
      Nonempty (est_PortData hn (genericAt E t ht.1) (genericAt E t' ht'.1) (est_S_ind ht.1 hQ hfull hj)
        (est_S'_ind hL ht ht' hop hs hQ hfull hj) q
        (GT_carrierEquiv (est_wall hL hR hef heg hfg ht ht' hop hs hQ hfull hj) q)
        (est_liftCrossing hn (genericAt E t' ht'.1) (est_S'_ind hL ht ht' hop hs hQ hfull hj) _ hu'))

/-- `s176_est_port_relation_weak` with the additional hypothesis `wind(S) ≠ 0` (otherwise byte-identical). -/
def r176l_est_port_relation_weak_uniform : Prop :=
  ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (E : CV.Event n) (e f g : ZMod n) (δ : ℝ)
    (hL : LocalizationData E e f g δ) (hR : AV_EventRadius E δ) (hef : e ≠ f) (heg : e ≠ g) (hfg : f ≠ g)
    (t t' : E.Parameter) (ht : Punctured E δ t) (ht' : Punctured E δ t') (hop : OppositeSides E t t')
    (hs : ∀ s, IsCrossing (E.curve t) s ↔ IsCrossing (E.curve t') s)
    (hef' : IsCrossing (E.curve t) {e, f}) (heg' : IsCrossing (E.curve t) {e, g})
    (hfg' : IsCrossing (E.curve t) {f, g}) (_hcomp : CompleteLocal (geomAt E t ht.1) hef' heg' hfg')
    (Q : Finset (Crossing (E.curve t))) (hQ : Q ∈ outsideSupports (geomAt E t ht.1) e f g)
    (hfull : FullAvail (geomAt E t ht.1) e f g Q) (j : Crossing (E.curve t))
    (hj : j.val ∈ triangleSupports e f g) (q : GeoComponent (geomAt E t ht.1) (Q ∪ {j})),
    CV.wind (geomAt E t ht.1) (Q ∪ {j}) ≠ 0 →
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

/-- The weak port relation with the uniformity hypothesis follows from the one without. -/
theorem r176l_est_port_relation_weak_uniform_of_weak (h : s176_est_port_relation_weak) :
    r176l_est_port_relation_weak_uniform :=
  fun n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q _ hex =>
    h n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hex

/-- **The weak interface of row 176 under `wind(S) ≠ 0`, from the site, `hrec` and the SMOOTH black
box**: `s176_est_port_relation_weak_of'` with its `hrest` discharged by `r176l_portDataRest_of_uniform`. -/
theorem r176l_est_port_relation_weak_uniform_of (hsmooth : r176l_smooth_black_box)
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
      s176_hrec_wall hn hL hR hef heg hfg ht ht' hop hs hQ hfull hj q hu') :
    r176l_est_port_relation_weak_uniform := by
  intro n _ hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs hef' heg' hfg' hcomp Q hQ hfull j hj q hwind hex
  obtain ⟨u, hu, hju, hu'⟩ := hex
  obtain ⟨R⟩ := r176l_portDataRest_of_uniform hsmooth hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ
    hfull hj q hwind hu hju.symm hu'
  refine ⟨u, hu, hju, hu', ⟨s176_PortDataWeak.mk' _ _ _ _ _ _ _ _ ?_ R⟩⟩
  exact s176_port_weak_of_event' hn hL hR hef heg hfg ht ht' hop hs hef' heg' hfg' hcomp hQ hfull hj q hu hju.symm
    hu' (hrec n hn E e f g δ hL hR hef heg hfg t t' ht ht' hop hs Q hQ hfull j hj q u hu')

end

end RProof
