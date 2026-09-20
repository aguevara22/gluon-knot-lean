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

/-! #### U-M4 helpers (prefix `um4_`): traversal betweenness across the run, the points of the four arcs -/

/-- (U-M4 helper) with the cut at `0`, the points strictly between `(0, θ₁)` and `(j, θ₂)` (`1 ≤ j < n`) are
the points of the labels `0 … j`, past `θ₁` on label `0` and before `θ₂` on label `j` -/
theorem um4_between_zero_nat {n : ℕ} [NeZero n] {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (0, θ₁) r ((j : ZMod n), θ₂) ↔
      r.1.val ≤ j ∧ (r.1.val = 0 → θ₁.val < r.2.val) ∧ (r.1.val = j → r.2.val < θ₂.val) := by
  have hjv : ((j : ZMod n)).val = j := ZMod.val_natCast_of_lt hjn
  have hθ1 := θ₁.2.1
  have hθ1' := θ₁.2.2
  have hθ2 := θ₂.2.1
  have hθ2' := θ₂.2.2
  have hr0 := r.2.2.1
  have hr1 := r.2.2.2
  have hj1' : (1:ℝ) ≤ j := by exact_mod_cast hj1
  simp only [traversalBetween, traversalKey, ZMod.val_zero, Nat.cast_zero, zero_add, hjv]
  constructor
  · rintro (⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩)
    · have hle : r.1.val ≤ j := by
        have h3 : (r.1.val : ℝ) < j + 1 := by linarith
        have h4 : r.1.val < j + 1 := by exact_mod_cast h3
        omega
      refine ⟨hle, fun h0 => ?_, fun hj => ?_⟩
      · rw [h0] at h1; simpa using h1
      · rw [hj] at h2; linarith
    · exfalso; linarith
    · exfalso; linarith
  · rintro ⟨hle, h0, hj⟩
    left
    constructor
    · rcases Nat.eq_zero_or_pos r.1.val with h | h
      · have := h0 h; rw [h]; simpa using this
      · have : (1:ℝ) ≤ r.1.val := by exact_mod_cast h
        linarith
    · rcases hle.lt_or_eq with h | h
      · have : (r.1.val : ℝ) + 1 ≤ j := by exact_mod_cast h
        linarith
      · have := hj h; rw [h]; linarith

/-- (U-M4 helper) the same, shifted to start at an arbitrary label `a` (`traversalBetween_shift`) -/
theorem um4_between_shift {n : ℕ} [NeZero n] (a : ZMod n) {j : ℕ} (hj1 : 1 ≤ j) (hjn : j < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (a, θ₁) r (a + (j : ZMod n), θ₂) ↔
      (r.1 - a).val ≤ j ∧ ((r.1 - a).val = 0 → θ₁.val < r.2.val) ∧
        ((r.1 - a).val = j → r.2.val < θ₂.val) := by
  rw [← traversalBetween_shift a]
  have h1 : traversalShift a (a, θ₁) = (0, θ₁) := by simp [traversalShift]
  have h2 : traversalShift a (a + (j : ZMod n), θ₂) = ((j : ZMod n), θ₂) := by simp [traversalShift]
  rw [h1, h2, um4_between_zero_nat hj1 hjn]
  exact Iff.rfl

variable (B) in
/-- (U-M4 helper) every traversal point of component `i` is `⟨i, (a + m, θ)⟩` for a label `m < k` -/
theorem um4_pt_i (p : D.Γ.Pt) (hp : p.1 = B.i) :
    ∃ (m : ℕ) (θ : Set.Ico (0:ℝ) 1), m < B.k ∧ p = ⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ := by
  obtain ⟨i', b, θ⟩ := p
  dsimp only at hp
  subst hp
  refine ⟨(b - B.a).val, θ, ZMod.val_lt _, ?_⟩
  rw [ZMod.natCast_zmod_val, add_sub_cancel]

variable (B) in
/-- (U-M4 helper) a non-foreign strand is `s` or a local strand -/
theorem um4_of_not_foreign {u : D.Γ.Strand} (h : ¬ B.Foreign u) :
    u = B.s ∨ ∃ m : ℕ, m ≤ B.j ∧ u = B.strand m := by
  by_cases hs : u = B.s
  · exact Or.inl hs
  · right
    by_contra hm
    exact h ⟨hs, fun m hm' heq => hm ⟨m, hm', heq⟩⟩

variable (B) in
/-- (U-M4 helper) `s` is not a local strand -/
theorem um4_s_ne_strand (m : ℕ) (hm : m ≤ B.j) : B.s ≠ B.strand m := by
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [strand_zero]; exact B.s_ne_eIn
  · rcases hm.lt_or_eq with hlt | rfl
    · intro heq
      have hs := B.s_mem_y
      rw [heq] at hs
      exact B.run_free m hpos hlt B.y hs
    · exact B.s_ne_eOut

variable (B) in
theorem um4_strand_eq_eIn_iff (m : ℕ) (hm : m < B.k) : B.strand m = B.eIn ↔ m = 0 := by
  constructor
  · intro h
    exact B.strand_inj hm (by have := B.three_le_k; omega) (h.trans B.strand_zero.symm)
  · rintro rfl; exact B.strand_zero

variable (B) in
theorem um4_strand_eq_eOut_iff (m : ℕ) (hm : m < B.k) : B.strand m = B.eOut ↔ m = B.j := by
  constructor
  · intro h
    exact B.strand_inj hm (by have := B.hk'; omega) h
  · rintro rfl; rfl

variable (B) in
/-- (U-M4 helper) the direction of a local strand -/
theorem um4_dir_strand (m : ℕ) : D.Γ.dir (B.strand m) = B.M (m + 1) - B.M m := by
  have h := D.Γ.head_eq_tail_add_dir (B.strand m)
  rw [head_strand, tail_strand] at h
  exact eq_sub_of_add_eq' h.symm

theorem um4_clampIco_eq_iff (θ : Set.Ico (0:ℝ) 1) {t : ℝ} (ht : 0 ≤ t ∧ t < 1) :
    θ = clampIco t ↔ θ.val = t := by
  constructor
  · intro h; rw [h, clampIco_val_of_mem ht]
  · intro h; exact Subtype.ext (h.trans (clampIco_val_of_mem ht).symm)

theorem um4_tin_mem : 0 ≤ C.tin ∧ C.tin < 1 := ⟨C.tin_pos.le, C.tin_lt_tout.trans C.tout_lt_one⟩
theorem um4_tout_mem : 0 ≤ C.tout ∧ C.tout < 1 := ⟨(C.tin_pos.trans C.tin_lt_tout).le, C.tout_lt_one⟩

/-- (U-M4 helper) the inner points of `arcIn` on component `i`: labels `a + m`, `m ≤ j`, past `t_p` on `e_in`
and before `t_q` on `e_out` -/
theorem um4_arcIn_inner_iff (m : ℕ) (hm : m < B.k) (θ : Set.Ico (0:ℝ) 1) :
    (arcIn C).Inner ⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ ↔
      m ≤ B.j ∧ (m = 0 → C.tp < θ.val) ∧ (m = B.j → θ.val < C.tq) := by
  refine (Shadow.Arc.inner_mk_iff (arcIn C) (B.a + (m : ZMod B.k), θ)).trans ?_
  show traversalBetween (B.a, clampIco C.tp) (B.a + (m : ZMod B.k), θ)
    (B.a + (B.j : ZMod B.k), clampIco C.tq) ↔ _
  rw [um4_between_shift B.a B.hj (by show B.j < B.k; have := B.hk'; omega), add_sub_cancel_left,
    ZMod.val_natCast_of_lt hm, clampIco_val_of_mem ⟨C.tp_pos.le, C.tp_lt_one⟩,
    clampIco_val_of_mem ⟨C.tq_pos.le, C.tq_lt_one⟩]

/-- (U-M4 helper) the points of the closed arc `arcIn` on component `i` -/
theorem um4_arcIn_mem_iff (m : ℕ) (hm : m < B.k) (θ : Set.Ico (0:ℝ) 1) :
    (arcIn C).Mem ⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ ↔
      m ≤ B.j ∧ (m = 0 → C.tp ≤ θ.val) ∧ (m = B.j → θ.val ≤ C.tq) := by
  have hstart : (⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ : D.Γ.Pt) = (arcIn C).startPt ↔
      m = 0 ∧ θ.val = C.tp :=
    (Shadow.mk_eq_mk_iff (B.strand m) B.eIn θ (clampIco C.tp)).trans
      (and_congr (B.um4_strand_eq_eIn_iff m hm) (um4_clampIco_eq_iff θ ⟨C.tp_pos.le, C.tp_lt_one⟩))
  have hstop : (⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ : D.Γ.Pt) = (arcIn C).stopPt ↔
      m = B.j ∧ θ.val = C.tq :=
    (Shadow.mk_eq_mk_iff (B.strand m) B.eOut θ (clampIco C.tq)).trans
      (and_congr (B.um4_strand_eq_eOut_iff m hm) (um4_clampIco_eq_iff θ ⟨C.tq_pos.le, C.tq_lt_one⟩))
  unfold Shadow.Arc.Mem
  rw [hstart, hstop, um4_arcIn_inner_iff C m hm θ]
  have hj := B.hj
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨h1, h2, h3⟩)
    · exact ⟨by omega, fun _ => h.ge, fun h' => absurd h' (by omega)⟩
    · exact ⟨le_rfl, fun h' => absurd h' (by omega), fun _ => h.le⟩
    · exact ⟨h1, fun h => (h2 h).le, fun h => (h3 h).le⟩
  · rintro ⟨h1, h2, h3⟩
    by_cases h0 : m = 0
    · rcases (h2 h0).lt_or_eq with hlt | heq
      · exact Or.inr (Or.inr ⟨h1, fun _ => hlt, fun h => absurd h (by omega)⟩)
      · exact Or.inl ⟨h0, heq.symm⟩
    · by_cases hjm : m = B.j
      · rcases (h3 hjm).lt_or_eq with hlt | heq
        · exact Or.inr (Or.inr ⟨h1, fun h => absurd h h0, fun _ => hlt⟩)
        · exact Or.inr (Or.inl ⟨hjm, heq⟩)
      · exact Or.inr (Or.inr ⟨h1, fun h => absurd h h0, fun h => absurd h hjm⟩)

/-- (U-M4 helper) the strand of a point of `arcIn` is one of the `j + 1` local strands -/
theorem um4_arcIn_mem_strand {p : D.Γ.Pt} (h : (arcIn C).Mem p) :
    ∃ m : ℕ, m ≤ B.j ∧ (⟨p.1, p.2.1⟩ : D.Γ.Strand) = B.strand m := by
  obtain ⟨m, θ, hm, rfl⟩ := B.um4_pt_i p h.fst
  exact ⟨m, ((um4_arcIn_mem_iff C m hm θ).mp h).1, rfl⟩

/-- (U-M4 helper) the points of `arcS`: on `s`, parameter in `[t_in, t_out]` -/
theorem um4_arcS_mem_iff (p : D.Γ.Pt) :
    (arcS C).Mem p ↔ (⟨p.1, p.2.1⟩ : D.Γ.Strand) = B.s ∧ C.tin ≤ p.2.2.val ∧ p.2.2.val ≤ C.tout := by
  have h := Smoothing.arc_mem_iff_of_same_edge (arcS C) B.s.2 (clampIco C.tin) (clampIco C.tout) rfl rfl
    (by rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)]
        exact C.tin_lt_tout) p
  rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h
  exact h

/-- (U-M4 helper) the inner points of `arcS` -/
theorem um4_arcS_inner_iff (p : D.Γ.Pt) :
    (arcS C).Inner p ↔ (⟨p.1, p.2.1⟩ : D.Γ.Strand) = B.s ∧ C.tin < p.2.2.val ∧ p.2.2.val < C.tout := by
  have h := Smoothing.arc_inner_iff_of_same_edge (arcS C) B.s.2 (clampIco C.tin) (clampIco C.tout) rfl rfl
    (by rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)]
        exact C.tin_lt_tout) p
  rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h
  exact h

/-- (U-M4 helper) the points of `arcS'`: on the reduced strand of `s`, parameter in `[t_in, t_out]` -/
theorem um4_arcS'_mem_iff (p : C.shadow.Pt) :
    (arcS' C).Mem p ↔
      (⟨p.1, p.2.1⟩ : C.shadow.Strand) = sStrand C ∧ C.tin ≤ p.2.2.val ∧ p.2.2.val ≤ C.tout := by
  have h := Smoothing.arc_mem_iff_of_same_edge (arcS' C) (sStrand C).2 (clampIco C.tin) (clampIco C.tout)
    rfl rfl
    (by rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)]
        exact C.tin_lt_tout) p
  rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h
  exact h

/-- (U-M4 helper) the inner points of `arcS'` -/
theorem um4_arcS'_inner_iff (p : C.shadow.Pt) :
    (arcS' C).Inner p ↔
      (⟨p.1, p.2.1⟩ : C.shadow.Strand) = sStrand C ∧ C.tin < p.2.2.val ∧ p.2.2.val < C.tout := by
  have h := Smoothing.arc_inner_iff_of_same_edge (arcS' C) (sStrand C).2 (clampIco C.tin)
    (clampIco C.tout) rfl rfl
    (by rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)]
        exact C.tin_lt_tout) p
  rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h
  exact h

/-- (U-M4 helper) the points of a run edge lie in `interior U` (both ends do, `Cut.run_mem_interior`;
`interior U` is convex) -/
theorem um4_run_edge_mem_interior (m : ℕ) (h1 : 1 ≤ m) (hj : m < B.j) (t : ℝ) (h0 : 0 ≤ t)
    (ht : t ≤ 1) : D.Γ.edgePt (B.strand m) t ∈ interior C.U := by
  rw [Shadow.edgePt_eq, tail_strand, B.um4_dir_strand]
  exact C.disc.convex.interior.add_smul_sub_mem (C.run_mem_interior m h1 hj.le)
    (C.run_mem_interior (m + 1) (by omega) hj) ⟨h0, ht⟩

/-- (U-M4 helper) the point at parameter `θ` of the local strand `m` lies in `U` iff it lies on `arcIn` -/
theorem um4_eval_local_mem_iff (m : ℕ) (hm : m ≤ B.j) (θ : Set.Ico (0:ℝ) 1) :
    D.Γ.edgePt (B.strand m) θ.val ∈ C.U ↔ (arcIn C).Mem ⟨B.i, (B.a + (m : ZMod B.k), θ)⟩ := by
  have hmk : m < B.k := by have := B.hk'; omega
  rw [um4_arcIn_mem_iff C m hmk θ]
  have hθ0 := θ.2.1
  have hθ1 := θ.2.2
  have hj := B.hj
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · rw [strand_zero, C.in_iff _ hθ0 hθ1.le]
    exact ⟨fun h => ⟨hm, fun _ => h, fun h' => absurd h' (by omega)⟩, fun h => h.2.1 rfl⟩
  · rcases hm.lt_or_eq with hlt | rfl
    · exact iff_of_true (interior_subset (um4_run_edge_mem_interior C m hpos hlt _ hθ0 hθ1.le))
        ⟨hm, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩
    · rw [strand_j, C.out_iff _ hθ0 hθ1.le]
      exact ⟨fun h => ⟨le_rfl, fun h' => absurd h' (by omega), fun _ => h⟩, fun h => h.2.2 rfl⟩

/-- (U-M4 helper) `arcIn` is an arc of `U` -/
theorem um4_isArc_arcIn : D.Γ.IsArc C.U (arcIn C) where
  start_ne_stop := by
    intro h
    have h1 : B.a = B.a + (B.j : ZMod B.k) := congrArg Prod.fst h
    exact Smoothing.zcast_ne_zero_of_lt B.hj (by show B.j < B.k; have := B.hk'; omega)
      (left_eq_add.mp h1)
  start_frontier := by rw [eval_arcIn_start]; exact C.p_frontier
  stop_frontier := by rw [eval_arcIn_stop]; exact C.q_frontier
  inner_interior := by
    intro p hp
    obtain ⟨m, θ, hm, rfl⟩ := B.um4_pt_i p hp.fst
    obtain ⟨hmj, h0, hj⟩ := (um4_arcIn_inner_iff C m hm θ).mp hp
    have hθ0 := θ.2.1
    have hθ1 := θ.2.2
    show D.Γ.edgePt (B.strand m) θ.val ∈ interior C.U
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · rw [strand_zero, C.in_int_iff _ hθ0 hθ1.le]; exact h0 rfl
    · rcases hmj.lt_or_eq with hlt | rfl
      · exact um4_run_edge_mem_interior C m hpos hlt _ hθ0 hθ1.le
      · rw [strand_j, C.out_int_iff _ hθ0 hθ1.le]; exact hj rfl

/-- (U-M4 helper) `arcS` is an arc of `U` -/
theorem um4_isArc_arcS : D.Γ.IsArc C.U (arcS C) where
  start_ne_stop := by
    intro h
    have h1 : (clampIco C.tin).val = (clampIco C.tout).val := congrArg (fun r => r.2.val) h
    rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h1
    exact C.tin_lt_tout.ne h1
  start_frontier := by rw [eval_arcS_start]; exact C.sIn_frontier
  stop_frontier := by rw [eval_arcS_stop]; exact C.sOut_frontier
  inner_interior := by
    intro p hp
    obtain ⟨hs, h1, h2⟩ := (um4_arcS_inner_iff C p).mp hp
    rw [Smoothing.eval_eq_edgePt, hs]
    exact (C.s_int_iff _ p.2.2.2.1 p.2.2.2.2.le).mpr ⟨h1, h2⟩

/-- **Sub-leaf (U-M4).**  The two arcs of `D` are distinct (different strands at the entering end:
`e_in ≠ s`). -/
theorem m4_arcIn_ne_arcS : arcIn C ≠ arcS C := by
  intro h
  have h1 : (arcS C).Mem (arcIn C).startPt := by rw [← h]; exact Shadow.Arc.startPt_mem _
  have h2 := ((um4_arcS_mem_iff C _).mp h1).1
  exact B.s_ne_eIn h2.symm

/-- **Sub-leaf (U-M4).**  The two arcs of the reduced diagram are distinct. -/
theorem m4_arcIn'_ne_arcS' : arcIn' C ≠ arcS' C := by
  intro h
  have h1 : (arcS' C).Mem (arcIn' C).startPt := by rw [← h]; exact Shadow.Arc.startPt_mem _
  have h2 := ((um4_arcS'_mem_iff C _).mp h1).1
  have h3 : B.kind C.tM C.tq ⟨B.i, ((0:ℕ) : ZMod _)⟩ = Kind.old B.s := by
    have h4 := congrArg (B.kind C.tM C.tq) h2
    rw [kind_sStrand] at h4
    exact h4
  rw [B.kind_mk_i _ _ 0 (by have := B.five_le_k'; omega), kindIdx_zero] at h3
  cases h3

/-- **Sub-leaf (U-M4, the `mem_iff` classification).**  `D ∩ U` is exactly the two arcs: a traversal point of
`D` evaluates into `U` iff it lies on `[p → M₁ → … → M_j → q]` or on `[b_in, b_out]` (`Cut.in_iff`,
`Cut.out_iff`, `Cut.s_iff`, `Cut.clear`, `Cut.run_mem_interior` + convexity for the run edges;
`traversalBetween` arithmetic on the labels `a, a+1, …, a+j`), the arcs are arcs of `U` (`IsArc`: ends on the
frontier by `Cut.p_frontier` etc., inner points in `interior U` by the interior laws) and disjoint. -/
theorem m4_arcCover : D.Γ.ArcCover C.U {arcIn C, arcS C} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases ha with rfl | rfl
    · exact um4_isArc_arcIn C
    · exact um4_isArc_arcS C
  · intro p
    constructor
    · intro hp
      by_cases hF : B.Foreign ⟨p.1, p.2.1⟩
      · exfalso
        exact Set.disjoint_left.mp (C.clear _ hF) (Smoothing.eval_mem_seg p) hp
      · rcases B.um4_of_not_foreign hF with hs | ⟨m, hm, hu⟩
        · refine ⟨arcS C, Or.inr rfl, ?_⟩
          rw [um4_arcS_mem_iff]
          refine ⟨hs, ?_⟩
          rw [Smoothing.eval_eq_edgePt, hs] at hp
          exact (C.s_iff _ p.2.2.2.1 p.2.2.2.2.le).mp hp
        · obtain ⟨m', θ, hm', rfl⟩ := B.um4_pt_i p (congrArg Sigma.fst hu)
          have hmm : m' = m := B.strand_inj hm' (by have := B.hk'; omega) hu
          subst hmm
          exact ⟨arcIn C, Or.inl rfl, (um4_eval_local_mem_iff C m' hm θ).mp hp⟩
    · rintro ⟨a, ha, hm⟩
      rcases ha with rfl | rfl
      · exact Smoothing.isArc_eval_mem_of_mem (um4_isArc_arcIn C) C.isClosed_U hm
      · exact Smoothing.isArc_eval_mem_of_mem (um4_isArc_arcS C) C.isClosed_U hm
  · intro a ha b hb hab p hpa hpb
    have key : ∀ p, (arcIn C).Mem p → (arcS C).Mem p → False := by
      intro p h1 h2
      obtain ⟨m, hm, hu⟩ := um4_arcIn_mem_strand C h1
      exact B.um4_s_ne_strand m hm (((um4_arcS_mem_iff C p).mp h2).1.symm.trans hu)
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · exact key p hpa hpb
    · exact key p hpb hpa
    · exact hab rfl

/-- (U-M4 helper) the vertex count of the reduced component, read on the shadow -/
theorem um4_k'_eq : (C.shadow.comp B.i).k = B.k' := B.reducedShadow_k_self C.tM C.tq

/-- (U-M4 helper) every traversal point of component `i` of the reduced shadow is `⟨i, (m, θ)⟩` for a label
`m < k'` -/
theorem um4_pt_i' (p : C.shadow.Pt) (hp : p.1 = B.i) :
    ∃ (m : ℕ) (θ : Set.Ico (0:ℝ) 1), m < B.k' ∧ p = ⟨B.i, ((m : ZMod _), θ)⟩ := by
  obtain ⟨i', b, θ⟩ := p
  dsimp only at hp
  subst hp
  refine ⟨b.val, θ, lt_of_lt_of_eq (ZMod.val_lt b) (um4_k'_eq C), ?_⟩
  rw [ZMod.natCast_zmod_val]

/-- (U-M4 helper) the evaluation of a point on an old strand of the reduced shadow -/
theorem um4_eval_old (u : C.shadow.Strand) (e : D.Γ.Strand) (hu : B.kind C.tM C.tq u = Kind.old e)
    (θ : Set.Ico (0:ℝ) 1) : C.shadow.eval ⟨u.1, (u.2, θ)⟩ = D.Γ.edgePt e θ.val := by
  refine (B.eval_eq C.tM C.tq _).trans ?_
  show (B.kind C.tM C.tq u).tail C.tM C.tq + θ.val • (B.kind C.tM C.tq u).dir C.tM C.tq = _
  rw [hu, Kind.tail, Kind.dir]
  rfl

/-- (U-M4 helper) the evaluation of a point of the cut piece `cutIn` (label `0`) -/
theorem um4_eval_cutIn (θ : Set.Ico (0:ℝ) 1) :
    C.shadow.eval ⟨B.i, (((0:ℕ) : ZMod _), θ)⟩ = D.Γ.edgePt B.eIn (θ.val * C.tM) := by
  refine (B.eval_eq C.tM C.tq _).trans ?_
  show (B.kind C.tM C.tq ⟨B.i, ((0:ℕ) : ZMod _)⟩).tail C.tM C.tq +
    θ.val • (B.kind C.tM C.tq ⟨B.i, ((0:ℕ) : ZMod _)⟩).dir C.tM C.tq = _
  rw [B.kind_mk_i _ _ 0 (by have := B.five_le_k'; omega), kindIdx_zero]
  exact Kind.tail_add_smul_dir C.tM C.tq Kind.cutIn (by nofun) θ.val

/-- (U-M4 helper) the evaluation of a point of the middle edge (label `1`) -/
theorem um4_eval_mid (θ : Set.Ico (0:ℝ) 1) :
    C.shadow.eval ⟨B.i, (((1:ℕ) : ZMod _), θ)⟩ = C.M' + θ.val • (C.q - C.M') := by
  refine (B.eval_eq C.tM C.tq _).trans ?_
  show (B.kind C.tM C.tq ⟨B.i, ((1:ℕ) : ZMod _)⟩).tail C.tM C.tq +
    θ.val • (B.kind C.tM C.tq ⟨B.i, ((1:ℕ) : ZMod _)⟩).dir C.tM C.tq = _
  rw [B.kind_mk_i _ _ 1 (by have := B.five_le_k'; omega), kindIdx_one, Kind.tail, Kind.dir]
  rfl

/-- (U-M4 helper) the evaluation of a point of the cut piece `cutOut` (label `2`) -/
theorem um4_eval_cutOut (θ : Set.Ico (0:ℝ) 1) :
    C.shadow.eval ⟨B.i, (((2:ℕ) : ZMod _), θ)⟩ = D.Γ.edgePt B.eOut (C.tq + θ.val * (1 - C.tq)) := by
  refine (B.eval_eq C.tM C.tq _).trans ?_
  show (B.kind C.tM C.tq ⟨B.i, ((2:ℕ) : ZMod _)⟩).tail C.tM C.tq +
    θ.val • (B.kind C.tM C.tq ⟨B.i, ((2:ℕ) : ZMod _)⟩).dir C.tM C.tq = _
  rw [B.kind_mk_i _ _ 2 (by have := B.five_le_k'; omega), kindIdx_two]
  exact Kind.tail_add_smul_dir C.tM C.tq Kind.cutOut (by nofun) θ.val

/-- (U-M4 helper) the middle edge `[M', q)` lies in `interior U` (`M' ∈ interior U`, `q ∈ U`, convexity) -/
theorem um4_mid_mem_interior (θ : ℝ) (h0 : 0 ≤ θ) (h1 : θ < 1) :
    C.M' + θ • (C.q - C.M') ∈ interior C.U := by
  have h : C.M' + θ • (C.q - C.M') = C.q + (1 - θ) • (C.M' - C.q) := by module
  rw [h]
  exact C.disc.convex.add_smul_sub_mem_interior C.q_mem C.M'_mem_interior ⟨by linarith, by linarith⟩

/-- (U-M4 helper) an occurring old strand is `s` or foreign -/
theorem um4_old_cases (u : C.shadow.Strand) (e : D.Γ.Strand) (hu : B.kind C.tM C.tq u = Kind.old e) :
    e = B.s ∨ B.Foreign e := by
  by_cases hs : e = B.s
  · exact Or.inl hs
  · right
    refine ⟨hs, fun m hm heq => ?_⟩
    have hocc := B.kind_occurs C.tM C.tq u
    rw [hu] at hocc
    exact hocc m hm (by rw [heq])

/-- (U-M4 helper) a strand of the reduced shadow is the reduced strand of `s` iff its kind is `old s` -/
theorem um4_eq_sStrand_iff (u : C.shadow.Strand) :
    u = sStrand C ↔ B.kind C.tM C.tq u = Kind.old B.s := by
  constructor
  · rintro rfl; exact kind_sStrand C
  · intro h; exact B.kind_injective C.tM C.tq (h.trans (kind_sStrand C).symm)

/-- (U-M4 helper) the inner points of `arcIn'`: the cut piece past `t_p / t_M`, and the middle edge -/
theorem um4_arcIn'_inner_iff (m : ℕ) (hm : m < B.k') (θ : Set.Ico (0:ℝ) 1) :
    (arcIn' C).Inner ⟨B.i, ((m : ZMod _), θ)⟩ ↔ (m = 0 ∧ C.tp / C.tM < θ.val) ∨ m = 1 := by
  have hN := um4_k'_eq C
  have hmN : m < (C.shadow.comp B.i).k := hN ▸ hm
  have h2N : 2 < (C.shadow.comp B.i).k := by rw [hN]; have := B.five_le_k'; omega
  have hθ := θ.2.1
  refine (Shadow.Arc.inner_mk_iff (arcIn' C) ((m : ZMod _), θ)).trans ?_
  show traversalBetween (((0:ℕ) : ZMod (C.shadow.comp B.i).k), clampIco (C.tp / C.tM))
    ((m : ZMod (C.shadow.comp B.i).k), θ)
    (((2:ℕ) : ZMod (C.shadow.comp B.i).k), ⟨0, le_rfl, zero_lt_one⟩) ↔ _
  rw [Nat.cast_zero, um4_between_zero_nat (by norm_num) h2N, ZMod.val_natCast_of_lt hmN,
    clampIco_val_of_mem ⟨(div_pos C.tp_pos C.tM_pos).le, (div_lt_one C.tM_pos).mpr C.tp_lt_tM⟩]
  constructor
  · rintro ⟨hle, h0, h2⟩
    rcases (by omega : m = 0 ∨ m = 1 ∨ m = 2) with rfl | rfl | rfl
    · exact Or.inl ⟨rfl, h0 rfl⟩
    · exact Or.inr rfl
    · exact absurd (h2 rfl) (not_lt.mpr hθ)
  · rintro (⟨rfl, h⟩ | rfl)
    · exact ⟨by omega, fun _ => h, fun h => absurd h (by omega)⟩
    · exact ⟨by omega, fun h => absurd h (by omega), fun h => absurd h (by omega)⟩

/-- (U-M4 helper) two strands `⟨i, c⟩`, `⟨i, c'⟩` of the reduced shadow are equal iff their labels are
(`Fin C.shadow.c` and `Fin D.Γ.c` agree only up to unfolding, so `Strand_mk_eq_mk_iff` does not rewrite) -/
theorem um4_mk_i_eq_iff (c c' : ZMod (C.shadow.comp B.i).k) :
    (⟨B.i, c⟩ : C.shadow.Strand) = ⟨B.i, c'⟩ ↔ c = c' := by
  constructor
  · intro h
    exact eq_of_heq (Sigma.mk.inj h).2
  · rintro rfl; rfl

/-- (U-M4 helper) the points of the closed arc `arcIn'` -/
theorem um4_arcIn'_mem_iff (m : ℕ) (hm : m < B.k') (θ : Set.Ico (0:ℝ) 1) :
    (arcIn' C).Mem ⟨B.i, ((m : ZMod _), θ)⟩ ↔
      (m = 0 ∧ C.tp / C.tM ≤ θ.val) ∨ m = 1 ∨ (m = 2 ∧ θ.val = 0) := by
  have hN := um4_k'_eq C
  have hmN : m < (C.shadow.comp B.i).k := hN ▸ hm
  have h0N : 0 < (C.shadow.comp B.i).k := by rw [hN]; have := B.five_le_k'; omega
  have h2N : 2 < (C.shadow.comp B.i).k := by rw [hN]; have := B.five_le_k'; omega
  have hcast : ∀ m' : ℕ, m' < (C.shadow.comp B.i).k →
      ((m : ZMod (C.shadow.comp B.i).k) = (m' : ZMod _) ↔ m = m') := by
    intro m' hm'
    exact ⟨fun h => Smoothing.nat_eq_of_zcast_eq hmN hm' h, fun h => by rw [h]⟩
  have hstart : (⟨B.i, ((m : ZMod _), θ)⟩ : C.shadow.Pt) = (arcIn' C).startPt ↔
      m = 0 ∧ θ.val = C.tp / C.tM := by
    exact (Shadow.mk_eq_mk_iff (⟨B.i, (m : ZMod _)⟩ : C.shadow.Strand) ⟨B.i, ((0:ℕ) : ZMod _)⟩ θ
      (clampIco (C.tp / C.tM))).trans
      (and_congr ((um4_mk_i_eq_iff C _ _).trans (hcast 0 h0N)) (um4_clampIco_eq_iff θ
        ⟨(div_pos C.tp_pos C.tM_pos).le, (div_lt_one C.tM_pos).mpr C.tp_lt_tM⟩))
  have hstop : (⟨B.i, ((m : ZMod _), θ)⟩ : C.shadow.Pt) = (arcIn' C).stopPt ↔ m = 2 ∧ θ.val = 0 := by
    exact (Shadow.mk_eq_mk_iff (⟨B.i, (m : ZMod _)⟩ : C.shadow.Strand) ⟨B.i, ((2:ℕ) : ZMod _)⟩ θ
      ⟨0, le_rfl, zero_lt_one⟩).trans
      (and_congr ((um4_mk_i_eq_iff C _ _).trans (hcast 2 h2N))
        ⟨fun h => by rw [h], fun h => Subtype.ext h⟩)
  unfold Shadow.Arc.Mem
  rw [hstart, hstop, um4_arcIn'_inner_iff C m hm θ]
  constructor
  · rintro (⟨rfl, h⟩ | ⟨rfl, h⟩ | ⟨rfl, h⟩ | rfl)
    · exact Or.inl ⟨rfl, h.ge⟩
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inl ⟨rfl, h.le⟩
    · exact Or.inr (Or.inl rfl)
  · rintro (⟨rfl, h⟩ | rfl | ⟨rfl, h⟩)
    · rcases h.lt_or_eq with hlt | heq
      · exact Or.inr (Or.inr (Or.inl ⟨rfl, hlt⟩))
      · exact Or.inl ⟨rfl, heq.symm⟩
    · exact Or.inr (Or.inr (Or.inr rfl))
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- (U-M4 helper) `arcIn'` is an arc of `U` -/
theorem um4_isArc_arcIn' : C.shadow.IsArc C.U (arcIn' C) where
  start_ne_stop := by
    intro h
    have h1 : ((0:ℕ) : ZMod (C.shadow.comp B.i).k) = ((2:ℕ) : ZMod _) := congrArg Prod.fst h
    have hN := um4_k'_eq C
    have h5 := B.five_le_k'
    have := Smoothing.nat_eq_of_zcast_eq (by rw [hN]; omega) (by rw [hN]; omega) h1
    omega
  start_frontier := by rw [eval_arcIn'_start]; exact C.p_frontier
  stop_frontier := by rw [eval_arcIn'_stop]; exact C.q_frontier
  inner_interior := by
    intro p hp
    obtain ⟨m, θ, hm, rfl⟩ := um4_pt_i' C p hp.fst
    have hθ0 := θ.2.1
    have hθ1 := θ.2.2
    rcases (um4_arcIn'_inner_iff C m hm θ).mp hp with ⟨rfl, h⟩ | rfl
    · rw [um4_eval_cutIn, C.in_int_iff _ (mul_nonneg hθ0 C.tM_pos.le)
        (mul_le_one₀ hθ1.le C.tM_pos.le C.tM_lt_one.le)]
      rwa [div_lt_iff₀ C.tM_pos] at h
    · rw [um4_eval_mid]
      exact um4_mid_mem_interior C θ.val hθ0 hθ1

/-- (U-M4 helper) `arcS'` is an arc of `U` -/
theorem um4_isArc_arcS' : C.shadow.IsArc C.U (arcS' C) where
  start_ne_stop := by
    intro h
    have h1 : (clampIco C.tin).val = (clampIco C.tout).val := congrArg (fun r => r.2.val) h
    rw [clampIco_val_of_mem (um4_tin_mem C), clampIco_val_of_mem (um4_tout_mem C)] at h1
    exact C.tin_lt_tout.ne h1
  start_frontier := by rw [eval_arcS'_start]; exact C.sIn_frontier
  stop_frontier := by rw [eval_arcS'_stop]; exact C.sOut_frontier
  inner_interior := by
    intro p hp
    obtain ⟨hs, h1, h2⟩ := (um4_arcS'_inner_iff C p).mp hp
    have he : C.shadow.eval p = D.Γ.edgePt B.s p.2.2.val :=
      um4_eval_old C ⟨p.1, p.2.1⟩ B.s ((um4_eq_sStrand_iff C _).mp hs) p.2.2
    rw [he]
    exact (C.s_int_iff _ p.2.2.2.1 p.2.2.2.2.le).mpr ⟨h1, h2⟩

/-- (U-M4 helper) a point on an old strand of the reduced shadow lies in `U` iff it lies on `arcS'`
(`s` by `Cut.s_iff`; a foreign strand by `Cut.clear`) -/
theorem um4_mem_iff_old (u : C.shadow.Strand) (e : D.Γ.Strand) (hu : B.kind C.tM C.tq u = Kind.old e)
    (θ : Set.Ico (0:ℝ) 1) :
    C.shadow.eval ⟨u.1, (u.2, θ)⟩ ∈ C.U ↔ (arcS' C).Mem ⟨u.1, (u.2, θ)⟩ := by
  rw [um4_eval_old C u e hu, um4_arcS'_mem_iff]
  show _ ↔ u = sStrand C ∧ C.tin ≤ θ.val ∧ θ.val ≤ C.tout
  rw [um4_eq_sStrand_iff, hu]
  rcases um4_old_cases C u e hu with rfl | hF
  · rw [C.s_iff _ θ.2.1 θ.2.2.le]
    simp
  · refine iff_of_false ?_ ?_
    · exact Set.disjoint_left.mp (C.clear e hF) ⟨θ.val, θ.2.1, θ.2.2.le, rfl⟩
    · rintro ⟨h, -⟩
      exact hF.1 (Kind.old.inj h)

/-- (U-M4 helper) a point on an old strand is not on `arcIn'` -/
theorem um4_not_arcIn'_mem_old (u : C.shadow.Strand) (e : D.Γ.Strand)
    (hu : B.kind C.tM C.tq u = Kind.old e) (θ : Set.Ico (0:ℝ) 1) :
    ¬ (arcIn' C).Mem ⟨u.1, (u.2, θ)⟩ := by
  intro h
  have hi : u.1 = B.i := h.fst
  obtain ⟨m, θ', hm, hp⟩ := um4_pt_i' C ⟨u.1, (u.2, θ)⟩ hi
  obtain ⟨hu', -⟩ := (Shadow.mk_eq_mk_iff u ⟨B.i, (m : ZMod _)⟩ θ θ').mp hp
  rw [hp] at h
  rw [hu', B.kind_mk_i _ _ m hm] at hu
  rcases (um4_arcIn'_mem_iff C m hm θ').mp h with ⟨rfl, -⟩ | rfl | ⟨rfl, -⟩
  · rw [kindIdx_zero] at hu; cases hu
  · rw [kindIdx_one] at hu; cases hu
  · rw [kindIdx_two] at hu; cases hu

/-- (U-M4 helper) the classification of the points of the reduced shadow inside `U`: on component `i` by
the label `0 / 1 / 2 / ≥ 3`, on the other components every strand is old -/
theorem um4_mem_U_iff' (u : C.shadow.Strand) (θ : Set.Ico (0:ℝ) 1) (hu : C.shadow.eval ⟨u.1, (u.2, θ)⟩ ∈ C.U) :
    (arcIn' C).Mem ⟨u.1, (u.2, θ)⟩ ∨ (arcS' C).Mem ⟨u.1, (u.2, θ)⟩ := by
  revert hu
  refine B.strand_cases C.tM C.tq ?_ ?_ u
  · intro m hm
    show C.shadow.eval ⟨B.i, ((m : ZMod _), θ)⟩ ∈ C.U →
      (arcIn' C).Mem ⟨B.i, ((m : ZMod _), θ)⟩ ∨ (arcS' C).Mem ⟨B.i, ((m : ZMod _), θ)⟩
    intro hu
    have hθ0 := θ.2.1
    have hθ1 := θ.2.2
    rcases Nat.lt_or_ge m 3 with h3 | h3
    · interval_cases m
      · left
        rw [um4_arcIn'_mem_iff C 0 hm θ]
        rw [um4_eval_cutIn, C.in_iff _ (mul_nonneg hθ0 C.tM_pos.le)
          (mul_le_one₀ hθ1.le C.tM_pos.le C.tM_lt_one.le)] at hu
        exact Or.inl ⟨rfl, (div_le_iff₀ C.tM_pos).mpr hu⟩
      · left
        rw [um4_arcIn'_mem_iff C 1 hm θ]
        exact Or.inr (Or.inl rfl)
      · left
        rw [um4_arcIn'_mem_iff C 2 hm θ]
        have hq1 : 0 ≤ 1 - C.tq := sub_nonneg.mpr C.tq_lt_one.le
        have hm0 : 0 ≤ θ.val * (1 - C.tq) := mul_nonneg hθ0 hq1
        have hm1 : θ.val * (1 - C.tq) ≤ 1 - C.tq := mul_le_of_le_one_left hq1 hθ1.le
        rw [um4_eval_cutOut, C.out_iff _ (by linarith [C.tq_pos]) (by linarith)] at hu
        refine Or.inr (Or.inr ⟨rfl, ?_⟩)
        have h3 : θ.val * (1 - C.tq) = 0 := le_antisymm (by linarith) hm0
        rcases mul_eq_zero.mp h3 with h | h
        · exact h
        · exact absurd h (by linarith [C.tq_lt_one])
    · right
      exact (um4_mem_iff_old C ⟨B.i, (m : ZMod _)⟩ (B.strand (B.j + m - 2))
        (by rw [B.kind_mk_i _ _ m hm, kindIdx_of_ge _ h3]) θ).mp hu
  · intro i' hi m hm
    show C.shadow.eval ⟨i', ((m : ZMod _), θ)⟩ ∈ C.U →
      (arcIn' C).Mem ⟨i', ((m : ZMod _), θ)⟩ ∨ (arcS' C).Mem ⟨i', ((m : ZMod _), θ)⟩
    intro hu
    right
    exact (um4_mem_iff_old C ⟨i', (m : ZMod _)⟩ ⟨i', (m : ZMod _)⟩ (B.kind_mk_of_ne _ _ hi m hm) θ).mp hu

/-- **Sub-leaf (U-M4).**  `D' ∩ U` is exactly the two arcs `[p → M' → q]` (kinds `cutIn` from `t_p / t_M`,
`mid`, the vertex `q`) and `s ∩ U`. -/
theorem m4_arcCover' : C.shadow.ArcCover C.U {arcIn' C, arcS' C} := by
  refine ⟨?_, ?_, ?_⟩
  · intro a ha
    rcases ha with rfl | rfl
    · exact um4_isArc_arcIn' C
    · exact um4_isArc_arcS' C
  · intro p
    constructor
    · intro hp
      rcases um4_mem_U_iff' C ⟨p.1, p.2.1⟩ p.2.2 hp with h | h
      · exact ⟨arcIn' C, Or.inl rfl, h⟩
      · exact ⟨arcS' C, Or.inr rfl, h⟩
    · rintro ⟨a, ha, hm⟩
      rcases ha with rfl | rfl
      · exact Smoothing.isArc_eval_mem_of_mem (um4_isArc_arcIn' C) C.isClosed_U hm
      · exact Smoothing.isArc_eval_mem_of_mem (um4_isArc_arcS' C) C.isClosed_U hm
  · intro a ha b hb hab p hpa hpb
    have key : ∀ p : C.shadow.Pt, (arcIn' C).Mem p → (arcS' C).Mem p → False := by
      intro p h1 h2
      have hs := ((um4_arcS'_mem_iff C p).mp h2).1
      exact um4_not_arcIn'_mem_old C ⟨p.1, p.2.1⟩ B.s ((um4_eq_sStrand_iff C _).mp hs) p.2.2 h1
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · exact key p hpa hpb
    · exact key p hpb hpa
    · exact hab rfl

variable (B) in
/-- (U-M4 helper) the entering and exiting edges meet at most at `M₁` (`j = 1`: consecutive edges,
`Generic.seg_inter_succ`; `j ≥ 2`: non-adjacent, so a common point would make `{e_in, e_out}` a crossing,
excluded by `no_io`) -/
theorem um4_seg_eIn_inter_eOut : D.Γ.seg B.eIn ∩ D.Γ.seg B.eOut ⊆ {D.Γ.head B.eIn} := by
  rcases Nat.lt_or_ge B.j 2 with hj | hj
  · have hj1 : B.j = 1 := by have := B.hj; omega
    have he : B.eOut = ⟨B.eIn.1, B.eIn.2 + 1⟩ := by
      show (⟨B.i, B.a + (B.j : ZMod B.k)⟩ : D.Γ.Strand) = ⟨B.i, B.a + 1⟩
      rw [hj1, Nat.cast_one]
    rw [he, D.generic.seg_inter_succ B.eIn]
  · intro x hx
    exfalso
    have hjk : B.j < B.k := by have := B.hk'; omega
    have hna : ¬ D.Γ.Adjacent B.eIn B.eOut := by
      rw [D.Γ.adjacent_mk_iff]
      rintro (h | h | h)
      · rw [add_sub_cancel_left] at h
        have h2 : ((B.j + 1 : ℕ) : ZMod B.k) = 0 := by push_cast; rw [h]; simp
        rw [ZMod.natCast_eq_zero_iff] at h2
        have := Nat.le_of_dvd (by omega) h2
        have := B.hk'; omega
      · rw [add_sub_cancel_left] at h
        exact Smoothing.zcast_ne_zero_of_lt B.hj hjk h
      · rw [add_sub_cancel_left] at h
        have := Smoothing.nat_eq_of_zcast_eq hjk (by show 1 < B.k; have := B.three_le_k; omega)
          (h.trans Nat.cast_one.symm)
        omega
    have hx' : (D.Γ.seg B.eIn ∩ D.Γ.seg B.eOut).Nonempty := ⟨x, hx⟩
    let xc : D.Γ.Crossing := ⟨{B.eIn, B.eOut}, B.eIn, B.eOut, rfl, hna, hx'⟩
    exact B.no_io xc ⟨Finset.mem_insert_self _ _, Finset.mem_insert_of_mem (Finset.mem_singleton_self _)⟩

/-- (U-M4 helper) the four arc ends are pairwise distinct plane points -/
theorem um4_p_ne_q : C.p ≠ C.q := by
  intro h
  have h1 : C.p ∈ D.Γ.seg B.eIn ∩ D.Γ.seg B.eOut :=
    ⟨⟨C.tp, C.tp_pos.le, C.tp_lt_one.le, rfl⟩, by rw [h]; exact ⟨C.tq, C.tq_pos.le, C.tq_lt_one.le, rfl⟩⟩
  have h2 := B.um4_seg_eIn_inter_eOut h1
  rw [Set.mem_singleton_iff, ← D.Γ.edgePt_one] at h2
  exact C.tp_lt_one.ne (D.generic.edgePt_injective B.eIn h2)

theorem um4_p_ne_sIn : C.p ≠ C.sIn := by
  intro h
  have h1 : C.p ∈ D.Γ.seg B.eIn ∩ D.Γ.seg B.s :=
    ⟨⟨C.tp, C.tp_pos.le, C.tp_lt_one.le, rfl⟩,
      by rw [h]; exact ⟨C.tin, C.tin_pos.le, (um4_tin_mem C).2.le, rfl⟩⟩
  rw [D.generic.seg_inter_seg_eq B.y B.eIn_mem_y B.s_mem_y B.s_ne_eIn.symm, Set.mem_singleton_iff,
    ← B.hty] at h1
  have := D.generic.edgePt_injective B.eIn h1
  linarith [C.tp_lt_tM, C.tM_lt_ty]

theorem um4_p_ne_sOut : C.p ≠ C.sOut := by
  intro h
  have h1 : C.p ∈ D.Γ.seg B.eIn ∩ D.Γ.seg B.s :=
    ⟨⟨C.tp, C.tp_pos.le, C.tp_lt_one.le, rfl⟩,
      by rw [h]; exact ⟨C.tout, (um4_tout_mem C).1, C.tout_lt_one.le, rfl⟩⟩
  rw [D.generic.seg_inter_seg_eq B.y B.eIn_mem_y B.s_mem_y B.s_ne_eIn.symm, Set.mem_singleton_iff,
    ← B.hty] at h1
  have := D.generic.edgePt_injective B.eIn h1
  linarith [C.tp_lt_tM, C.tM_lt_ty]

theorem um4_q_ne_sIn : C.q ≠ C.sIn := by
  intro h
  have h1 : C.q ∈ D.Γ.seg B.eOut ∩ D.Γ.seg B.s :=
    ⟨⟨C.tq, C.tq_pos.le, C.tq_lt_one.le, rfl⟩,
      by rw [h]; exact ⟨C.tin, C.tin_pos.le, (um4_tin_mem C).2.le, rfl⟩⟩
  rw [D.generic.seg_inter_seg_eq B.z B.eOut_mem_z B.s_mem_z B.s_ne_eOut.symm, Set.mem_singleton_iff,
    ← B.htz] at h1
  have := D.generic.edgePt_injective B.eOut h1
  linarith [C.tz_lt_tq]

theorem um4_q_ne_sOut : C.q ≠ C.sOut := by
  intro h
  have h1 : C.q ∈ D.Γ.seg B.eOut ∩ D.Γ.seg B.s :=
    ⟨⟨C.tq, C.tq_pos.le, C.tq_lt_one.le, rfl⟩,
      by rw [h]; exact ⟨C.tout, (um4_tout_mem C).1, C.tout_lt_one.le, rfl⟩⟩
  rw [D.generic.seg_inter_seg_eq B.z B.eOut_mem_z B.s_mem_z B.s_ne_eOut.symm, Set.mem_singleton_iff,
    ← B.htz] at h1
  have := D.generic.edgePt_injective B.eOut h1
  linarith [C.tz_lt_tq]

theorem um4_sIn_ne_sOut : C.sIn ≠ C.sOut := fun h =>
  C.tin_lt_tout.ne (D.generic.edgePt_injective B.s h)

/-- (U-M4 helper) a frontier point of the trace of `D` is one of the four arc ends -/
theorem um4_frontier_pt (p : D.Γ.Pt) (hp : D.Γ.eval p ∈ frontier C.U) :
    p = (arcIn C).startPt ∨ p = (arcIn C).stopPt ∨ p = (arcS C).startPt ∨ p = (arcS C).stopPt := by
  have hU : D.Γ.eval p ∈ C.U := C.isClosed_U.frontier_subset hp
  have hnot : D.Γ.eval p ∉ interior C.U := hp.2
  obtain ⟨a, ha, hm⟩ := ((m4_arcCover C).mem_iff p).mp hU
  rcases ha with rfl | rfl
  · rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd ((um4_isArc_arcIn C).inner_interior p h) hnot
  · rcases hm with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd ((um4_isArc_arcS C).inner_interior p h) hnot

/-- (U-M4 helper) `eval` is injective on the four arc ends of `D` -/
theorem um4_eval_end_injOn (e e' : D.Γ.Pt)
    (he : e = (arcIn C).startPt ∨ e = (arcIn C).stopPt ∨ e = (arcS C).startPt ∨ e = (arcS C).stopPt)
    (he' : e' = (arcIn C).startPt ∨ e' = (arcIn C).stopPt ∨ e' = (arcS C).startPt ∨ e' = (arcS C).stopPt)
    (heq : D.Γ.eval e = D.Γ.eval e') : e = e' := by
  have h1 := eval_arcIn_start C
  have h2 := eval_arcIn_stop C
  have h3 := eval_arcS_start C
  have h4 := eval_arcS_stop C
  have hpq := um4_p_ne_q C
  have hpi := um4_p_ne_sIn C
  have hpo := um4_p_ne_sOut C
  have hqi := um4_q_ne_sIn C
  have hqo := um4_q_ne_sOut C
  have hio := um4_sIn_ne_sOut C
  rcases he with rfl | rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (rw [h1, h2] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h1, h3] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h1, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h2, h3] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h2, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h3, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)

/-- (U-M4 helper) the tail of a strand of another component lies outside `U` (`s` or foreign) -/
theorem um4_tail_not_mem_of_ne (u : D.Γ.Strand) (hu : u.1 ≠ B.i) : D.Γ.tail u ∉ C.U := by
  by_cases hs : u = B.s
  · rw [hs]; exact C.tail_s_not_mem
  · have hF : B.Foreign u := ⟨hs, fun m _ heq => hu (congrArg Sigma.fst heq)⟩
    exact Set.disjoint_left.mp (C.clear u hF) (D.Γ.tail_mem_seg u)

/-- **Sub-leaf (U-M4).**  `D` meets `U` cleanly: the frontier points of the trace are the four ends, each
traversed once (none is a vertex or a double point); every component has a point outside `U` (`M₀`, or the
tail of a foreign strand, or `tail s`). -/
theorem m4_clean : Clean C.U D := by
  refine ⟨?_, ?_⟩
  · intro p hp p' hp' heq
    exact um4_eval_end_injOn C p p' (um4_frontier_pt C p hp) (um4_frontier_pt C p' hp') heq
  · intro i'
    by_cases hi : i' = B.i
    · subst hi
      refine ⟨(B.a, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
      show D.Γ.edgePt B.eIn 0 ∉ C.U
      rw [D.Γ.edgePt_zero, ← B.M_zero]
      exact C.M_zero_not_mem
    · refine ⟨(0, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
      show D.Γ.edgePt ⟨i', 0⟩ 0 ∉ C.U
      rw [D.Γ.edgePt_zero]
      exact um4_tail_not_mem_of_ne C ⟨i', 0⟩ hi

/-- (U-M4 helper) a frontier point of the trace of the reduced diagram is one of the four arc ends -/
theorem um4_frontier_pt' (p : C.shadow.Pt) (hp : C.shadow.eval p ∈ frontier C.U) :
    p = (arcIn' C).startPt ∨ p = (arcIn' C).stopPt ∨ p = (arcS' C).startPt ∨ p = (arcS' C).stopPt := by
  have hU : C.shadow.eval p ∈ C.U := C.isClosed_U.frontier_subset hp
  have hnot : C.shadow.eval p ∉ interior C.U := hp.2
  obtain ⟨a, ha, hm⟩ := ((m4_arcCover' C).mem_iff p).mp hU
  rcases ha with rfl | rfl
  · rcases hm with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact absurd ((um4_isArc_arcIn' C).inner_interior p h) hnot
  · rcases hm with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inr (Or.inr h))
    · exact absurd ((um4_isArc_arcS' C).inner_interior p h) hnot

/-- (U-M4 helper) `eval` is injective on the four arc ends of the reduced diagram (the same four plane
points `p, q, b_in, b_out`) -/
theorem um4_eval_end_injOn' (e e' : C.shadow.Pt)
    (he : e = (arcIn' C).startPt ∨ e = (arcIn' C).stopPt ∨ e = (arcS' C).startPt ∨ e = (arcS' C).stopPt)
    (he' : e' = (arcIn' C).startPt ∨ e' = (arcIn' C).stopPt ∨ e' = (arcS' C).startPt ∨
      e' = (arcS' C).stopPt)
    (heq : C.shadow.eval e = C.shadow.eval e') : e = e' := by
  have h1 := eval_arcIn'_start C
  have h2 := eval_arcIn'_stop C
  have h3 := eval_arcS'_start C
  have h4 := eval_arcS'_stop C
  have hpq := um4_p_ne_q C
  have hpi := um4_p_ne_sIn C
  have hpo := um4_p_ne_sOut C
  have hqi := um4_q_ne_sIn C
  have hqo := um4_q_ne_sOut C
  have hio := um4_sIn_ne_sOut C
  rcases he with rfl | rfl | rfl | rfl <;> rcases he' with rfl | rfl | rfl | rfl <;>
    first
    | rfl
    | (rw [h1, h2] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h1, h3] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h1, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h2, h3] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h2, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)
    | (rw [h3, h4] at heq; first | exact absurd heq ‹_› | exact absurd heq.symm ‹_›)

/-- **Sub-leaf (U-M4).**  The reduced diagram meets `U` cleanly. -/
theorem m4_clean' : Clean C.U (B.reducedDiagram C) := by
  refine ⟨?_, ?_⟩
  · intro p hp p' hp' heq
    exact um4_eval_end_injOn' C p p' (um4_frontier_pt' C p hp) (um4_frontier_pt' C p' hp') heq
  · intro i'
    by_cases hi : i' = B.i
    · subst hi
      refine ⟨(((0:ℕ) : ZMod _), ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
      show C.shadow.edgePt ⟨B.i, ((0:ℕ) : ZMod _)⟩ 0 ∉ C.U
      rw [C.shadow.edgePt_zero, B.tail_mk_i, reducedTuple_zero]
      exact C.M_zero_not_mem
    · refine ⟨(((0:ℕ) : ZMod _), ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
      show C.shadow.edgePt ⟨i', ((0:ℕ) : ZMod _)⟩ 0 ∉ C.U
      rw [C.shadow.edgePt_zero, B.tail_mk_of_ne _ _ hi]
      exact um4_tail_not_mem_of_ne C _ hi

/-- (U-M4 helper) the strands of a crossing whose double point lies in `U` are among `s, e_in, e_out`
(a foreign strand misses `U`, `Cut.clear`; a run strand carries no crossing, `run_free`) -/
theorem um4_crossing_strand_mem_U (x : D.Γ.Crossing) (hx : D.Γ.crossingPoint x ∈ C.U) {u : D.Γ.Strand}
    (hu : u ∈ x.val) : u = B.s ∨ u = B.eIn ∨ u = B.eOut := by
  have hnF : ¬ B.Foreign u := fun hF =>
    Set.disjoint_left.mp (C.clear u hF) (D.Γ.crossingPoint_mem x hu) hx
  rcases B.um4_of_not_foreign hnF with hs | ⟨m, hm, rfl⟩
  · exact Or.inl hs
  · right
    rcases Nat.eq_zero_or_pos m with rfl | hpos
    · left; exact B.strand_zero
    · rcases hm.lt_or_eq with hlt | rfl
      · exact absurd hu (B.run_free m hpos hlt x)
      · right; rfl

/-- (U-M4 helper) a crossing on `s` and `e_in` is `y`; on `s` and `e_out` it is `z` -/
theorem um4_crossing_eq (x : D.Γ.Crossing) (u v : D.Γ.Strand) (hx : x.val = {u, v}) (hs : u = B.s)
    (hv : v = B.eIn ∨ v = B.eOut) : x = B.y ∨ x = B.z := by
  rcases hv with rfl | rfl
  · left; apply Subtype.ext; rw [hx, hs, B.hy, Finset.pair_comm]
  · right; apply Subtype.ext; rw [hx, hs, B.hz, Finset.pair_comm]

/-- **Sub-leaf (U-M4).**  The crossings of `D` inside `U` are exactly `y` and `z` (every other crossing has a
foreign strand, `Cut.clear`; `y, z ∈ K ⊆ interior U`). -/
theorem m4_inner_iff' (x : D.Γ.Crossing) : D.Γ.crossingPoint x ∈ interior C.U ↔ x = B.y ∨ x = B.z := by
  constructor
  · intro h
    have hU : D.Γ.crossingPoint x ∈ C.U := interior_subset h
    obtain ⟨u, v, hx, hna, -⟩ := x.2
    have hu : u ∈ x.val := by rw [hx]; exact Finset.mem_insert_self _ _
    have hv : v ∈ x.val := by rw [hx]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)
    have huv : u ≠ v := D.Γ.ne_of_not_adjacent hna
    have hx' : x.val = {v, u} := by rw [hx, Finset.pair_comm]
    rcases um4_crossing_strand_mem_U C x hU hu with hus | hus | hus <;>
      rcases um4_crossing_strand_mem_U C x hU hv with hvs | hvs | hvs
    · exact absurd (hus.trans hvs.symm) huv
    · exact um4_crossing_eq x u v hx hus (Or.inl hvs)
    · exact um4_crossing_eq x u v hx hus (Or.inr hvs)
    · exact um4_crossing_eq x v u hx' hvs (Or.inl hus)
    · exact absurd (hus.trans hvs.symm) huv
    · have h1 : B.eIn ∈ x.val := by rw [← hus]; exact hu
      have h2 : B.eOut ∈ x.val := by rw [← hvs]; exact hv
      exact absurd ⟨h1, h2⟩ (B.no_io x)
    · exact um4_crossing_eq x v u hx' hvs (Or.inr hus)
    · have h1 : B.eIn ∈ x.val := by rw [← hvs]; exact hv
      have h2 : B.eOut ∈ x.val := by rw [← hus]; exact hu
      exact absurd ⟨h1, h2⟩ (B.no_io x)
    · exact absurd (hus.trans hvs.symm) huv
  · rintro (rfl | rfl)
    · rw [← B.hty]; exact C.K_sub ((B.in_iff _ B.ty_pos.le B.ty_lt_one.le).mpr le_rfl)
    · rw [← B.htz]; exact C.K_sub ((B.out_iff _ B.tz_pos.le B.tz_lt_one.le).mpr le_rfl)

/-- **Sub-leaf (U-M4).**  The reduced diagram has no crossing inside `U` (`m3_crossingPoint_origCrossing` +
`m4_inner_iff'` + `m3_origCrossing_ne_y/z`). -/
theorem m4_no_inner (x' : C.shadow.Crossing) : C.shadow.crossingPoint x' ∉ interior C.U := by
  intro h
  rw [m3_crossingPoint_origCrossing] at h
  rcases (m4_inner_iff' C _).mp h with h | h
  · exact m3_origCrossing_ne_y C x' h
  · exact m3_origCrossing_ne_z C x' h

/-- (U-M4 helper) the crossing parameter is determined by any `edgePt` equation (`Generic.edgePt_injective`) -/
theorem um4_crossingParam_eq (x : D.Γ.Crossing) {e : D.Γ.Strand} (he : e ∈ x.val) {t : ℝ}
    (ht : D.Γ.edgePt e t = D.Γ.crossingPoint x) : D.crossingParam x he = t :=
  D.generic.edgePt_injective e ((D.crossingParam_spec x he).2.2.symm.trans ht.symm)

/-- (U-M4 helper) the traversal point of an occurrence, given its strand and its parameter -/
theorem um4_visitPt_eq (v : D.Γ.Visit) (e : D.Γ.Strand) (he : v.2.val = e) (t : ℝ)
    (ht : D.Γ.edgePt e t = D.Γ.crossingPoint v.1) (h0 : 0 ≤ t) (h1 : t < 1) :
    D.visitPt v = ⟨e.1, (e.2, ⟨t, h0, h1⟩)⟩ := by
  refine (Shadow.mk_eq_mk_iff v.2.val e ⟨D.crossingParam v.1 v.2.2, (D.crossingParam_pos v.1 v.2.2).le,
    D.crossingParam_lt_one v.1 v.2.2⟩ ⟨t, h0, h1⟩).mpr ⟨he, Subtype.ext ?_⟩
  exact um4_crossingParam_eq v.1 v.2.2 (by rw [he]; exact ht)

/-- (U-M4 helper) an occurrence of `y` or `z` on `s` lies on `arcS` -/
theorem um4_arcS_mem_visit_s (v : D.Γ.Visit) (hv : v.2.val = B.s) (hx : v.1 = B.y ∨ v.1 = B.z) :
    (arcS C).Mem (D.visitPt v) := by
  rcases hx with hx | hx
  · rw [um4_visitPt_eq v B.s hv B.tsy (by rw [hx]; exact B.htsy) B.tsy_pos.le B.tsy_lt_one,
      um4_arcS_mem_iff]
    exact ⟨rfl, C.tin_lt_tsy.le, C.tsy_lt_tout.le⟩
  · rw [um4_visitPt_eq v B.s hv B.tsz (by rw [hx]; exact B.htsz) B.tsz_pos.le B.tsz_lt_one,
      um4_arcS_mem_iff]
    exact ⟨rfl, C.tin_lt_tsz.le, C.tsz_lt_tout.le⟩

/-- (U-M4 helper) the occurrence of `y` on `e_in` lies on `arcIn` (`t_p < t_y`) -/
theorem um4_arcIn_mem_visit_eIn (v : D.Γ.Visit) (hv : v.2.val = B.eIn) (hx : v.1 = B.y) :
    (arcIn C).Mem (D.visitPt v) := by
  rw [um4_visitPt_eq v ⟨B.i, B.a + ((0:ℕ) : ZMod B.k)⟩ (by rw [hv]; exact B.strand_zero.symm) B.ty
    (by rw [hx, Nat.cast_zero, add_zero]; exact B.hty) B.ty_pos.le B.ty_lt_one]
  show (arcIn C).Mem ⟨B.i, (B.a + ((0:ℕ) : ZMod B.k), ⟨B.ty, B.ty_pos.le, B.ty_lt_one⟩)⟩
  rw [um4_arcIn_mem_iff C 0 (by have := B.three_le_k; omega)]
  exact ⟨Nat.zero_le _, fun _ => (C.tp_lt_tM.trans C.tM_lt_ty).le,
    fun h => absurd h.symm (by have := B.hj; omega)⟩

/-- (U-M4 helper) the occurrence of `z` on `e_out` lies on `arcIn` (`t_z < t_q`) -/
theorem um4_arcIn_mem_visit_eOut (v : D.Γ.Visit) (hv : v.2.val = B.eOut) (hx : v.1 = B.z) :
    (arcIn C).Mem (D.visitPt v) := by
  rw [um4_visitPt_eq v ⟨B.i, B.a + (B.j : ZMod B.k)⟩ hv B.tz (by rw [hx]; exact B.htz) B.tz_pos.le
    B.tz_lt_one]
  show (arcIn C).Mem ⟨B.i, (B.a + (B.j : ZMod B.k), ⟨B.tz, B.tz_pos.le, B.tz_lt_one⟩)⟩
  rw [um4_arcIn_mem_iff C B.j (by have := B.hk'; omega)]
  exact ⟨le_rfl, fun h => absurd h (by have := B.hj; omega), fun _ => C.tz_lt_tq.le⟩

variable (B) in
/-- (U-M4 helper) the over strand of `y` is `e_in` or `s` -/
theorem um4_overStrand_y : D.overStrand B.y = B.eIn ∨ D.overStrand B.y = B.s := by
  have h := D.over_mem B.y
  rw [B.hy, Finset.mem_insert, Finset.mem_singleton] at h
  exact h

variable (B) in
/-- (U-M4 helper) the over strand of `z` is `e_out` or `s` -/
theorem um4_overStrand_z : D.overStrand B.z = B.eOut ∨ D.overStrand B.z = B.s := by
  have h := D.over_mem B.z
  rw [B.hz, Finset.mem_insert, Finset.mem_singleton] at h
  exact h

/-- **Sub-leaf (U-M4).**  `y` is a crossing between the two arcs (its `e_in`-occurrence at `t_y ∈ (t_p, 1)`
is an inner point of `arcIn`, its `s`-occurrence at `t_sy ∈ (t_in, t_out)` an inner point of `arcS`). -/
theorem m4_sep_y : D.Separates (arcIn C) (arcS C) B.y := by
  rcases B.um4_overStrand_y with h | h
  · left
    have hs : B.s = D.underStrand B.y :=
      D.eq_under_of_mem_of_ne B.y B.s_mem_y (by rw [h]; exact B.s_ne_eIn)
    exact ⟨um4_arcIn_mem_visit_eIn C (D.overVisit B.y) h rfl,
      um4_arcS_mem_visit_s C (D.underVisit B.y) hs.symm (Or.inl rfl)⟩
  · right
    have he : B.eIn = D.underStrand B.y :=
      D.eq_under_of_mem_of_ne B.y B.eIn_mem_y (by rw [h]; exact B.s_ne_eIn.symm)
    exact ⟨um4_arcS_mem_visit_s C (D.overVisit B.y) h (Or.inl rfl),
      um4_arcIn_mem_visit_eIn C (D.underVisit B.y) he.symm rfl⟩

theorem m4_sep_z : D.Separates (arcIn C) (arcS C) B.z := by
  rcases B.um4_overStrand_z with h | h
  · left
    have hs : B.s = D.underStrand B.z :=
      D.eq_under_of_mem_of_ne B.z B.s_mem_z (by rw [h]; exact B.s_ne_eOut)
    exact ⟨um4_arcIn_mem_visit_eOut C (D.overVisit B.z) h rfl,
      um4_arcS_mem_visit_s C (D.underVisit B.z) hs.symm (Or.inr rfl)⟩
  · right
    have he : B.eOut = D.underStrand B.z :=
      D.eq_under_of_mem_of_ne B.z B.eOut_mem_z (by rw [h]; exact B.s_ne_eOut.symm)
    exact ⟨um4_arcS_mem_visit_s C (D.overVisit B.z) h (Or.inr rfl),
      um4_arcIn_mem_visit_eOut C (D.underVisit B.z) he.symm rfl⟩

/-- **Sub-leaf (U-M4).**  The common over strand: `B.same_over` read on the arcs. -/
theorem m4_same_over :
    (D.OverOn (arcIn C) B.y ∧ D.OverOn (arcIn C) B.z) ∨ (D.OverOn (arcS C) B.y ∧ D.OverOn (arcS C) B.z) := by
  rcases B.same_over with ⟨hy, hz⟩ | ⟨hy, hz⟩
  · right
    exact ⟨um4_arcS_mem_visit_s C (D.overVisit B.y) hy (Or.inl rfl),
      um4_arcS_mem_visit_s C (D.overVisit B.z) hz (Or.inr rfl)⟩
  · left
    have hy' : D.overStrand B.y = B.eIn := B.um4_overStrand_y.resolve_right hy
    have hz' : D.overStrand B.z = B.eOut := B.um4_overStrand_z.resolve_right hz
    exact ⟨um4_arcIn_mem_visit_eIn C (D.overVisit B.y) hy' rfl,
      um4_arcIn_mem_visit_eOut C (D.overVisit B.z) hz' rfl⟩

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
