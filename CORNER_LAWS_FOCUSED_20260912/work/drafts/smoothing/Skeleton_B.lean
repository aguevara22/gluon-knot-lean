import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.LinkDiagramExtras
import SM.LinkRecordExtras
import SM.LinkRecordExtension

/-! # Oriented smoothing of a polygonal link diagram — skeleton B

Construction (sm-3:1084-1103, design file section skein_and_moves): at the crossing `x` of `D` with
over strand `o`, under strand `u`, double point `P₀` and edge parameters `τo`, `τu`, cut both
strands at parameter distance `ε` before and after the double point (`om = o(τo-ε)`,
`op = o(τo+ε)`, `um`, `up`) and join crosswise by the straight segments `om → up` and `um → op`.

Design of tag B ("proofs easy, definitions long"):
* The new vertex tuples are described by *vertex descriptors* (`SmVert`: an old vertex, or one of
  the four cut points), one explicit descriptor sequence per new component (`smB_descrA/B` for the
  self-crossing case, `smB_descrM` for the mixed case, `smB_descrOld` for untouched components),
  evaluated to plane points by `smB_evalVert`.  Every fact about an edge of the new shadow is a
  fact about a consecutive descriptor pair, and there are only seven kinds of such pairs
  (`SmKind`): an old edge, the four half-edges `hOm hOp hUm hUp`, the two smoothing segments
  `n1 n2`.
* The components of the new shadow are indexed by the components of the smoothed record
  `(D.record.smooth (D.overVisit x)).comps` (the cycles of the reconnected successor plus the
  crossing-free circles), through `Fintype.equivFin`.  So the component bijection `e` of the
  record isomorphism is literally `(Fintype.equivFin _).symm`, and the smoothing segment
  combinatorics (`(x A y B) ↦ (x B), (y A)` / `(x A), (y B) ↦ (x B y A)`) is read off the record.
* The over data of the smoothed diagram is *defined* from the over data of `D` through the
  underlying-strand map `smB_toD`, so the bit and sign clauses of the record isomorphism are
  definitional up to the crossing correspondence.
* All geometry inside the clean disc `U = closedBall P₀ r` is expressed in the basis `(do, du)`
  of the two edge vectors (`intersection_parameters_unique`), and all geometry outside `U` is
  inherited from `D` because the two shadows have the same trace there.

Every `sorry` below is a lemma of the chain listed in `PLAN_B.md`; the definitions are real.
Helper names carry the prefix `smB_`. -/

namespace SM.Link

open SM Equiv

noncomputable section

/-! ## §0 Preliminaries on generic shadows (reusable lemmas) -/

namespace Shadow

variable (Γ : Shadow)

/-- The plane point at an arbitrary real edge parameter of a strand (extends `eval`). -/
def edgePt (s : Γ.Strand) (t : ℝ) : Plane := edgePoint (Γ.comp s.1).P s.2 t

theorem edgePt_zero (s : Γ.Strand) : Γ.edgePt s 0 = Γ.tail s := by
  unfold edgePt tail; rw [edgePoint_zero]

theorem edgePt_one (s : Γ.Strand) : Γ.edgePt s 1 = Γ.head s := by
  unfold edgePt head; rw [edgePoint_one]

theorem edgePt_eq (s : Γ.Strand) (t : ℝ) : Γ.edgePt s t = Γ.tail s + t • Γ.dir s := rfl

theorem mem_seg_iff (s : Γ.Strand) (q : Plane) :
    q ∈ Γ.seg s ↔ ∃ t, 0 ≤ t ∧ t ≤ 1 ∧ q = Γ.edgePt s t := Iff.rfl

theorem mem_interior_iff (s : Γ.Strand) (q : Plane) :
    q ∈ Γ.interior s ↔ ∃ t, 0 < t ∧ t < 1 ∧ q = Γ.edgePt s t := Iff.rfl

/-- L0.4: distances along an edge scale with the edge vector (sup norm of `Plane`). -/
theorem dist_edgePt (s : Γ.Strand) (t t' : ℝ) :
    dist (Γ.edgePt s t) (Γ.edgePt s t') = |t - t'| * ‖Γ.dir s‖ := by
  sorry

/-- L0.1: two consecutive edges of a generic shadow meet only at their common vertex. -/
theorem Generic.adjacent_seg_inter {Γ : Shadow} (hΓ : Γ.Generic) (i : Fin Γ.c)
    (a : ZMod (Γ.comp i).k) :
    Γ.seg ⟨i, a⟩ ∩ Γ.seg ⟨i, a + 1⟩ = {Γ.tail ⟨i, a + 1⟩} := by
  sorry

/-- L0.2: the double point of `x` lies on no edge other than the two edges of `x`. -/
theorem Generic.crossingPoint_not_mem_seg {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    {t : Γ.Strand} (ht : t ∉ x.val) : Γ.crossingPoint x ∉ Γ.seg t := by
  sorry

/-- L0.3: the double point is not a vertex. -/
theorem Generic.crossingPoint_ne_tail {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    (s : Γ.Strand) : Γ.crossingPoint x ≠ Γ.tail s := by
  sorry

/-- L0.7: the two edges of a crossing meet exactly in the double point (generic shadow). -/
theorem Generic.seg_inter_seg_eq {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hs : s ∈ x.val) (ht : t ∈ x.val) (hst : s ≠ t) :
    Γ.seg s ∩ Γ.seg t = {Γ.crossingPoint x} := by
  sorry

/-- The edge parameter of a point of an edge is unique (nonzero edge vector). -/
theorem Generic.edgePt_injective {Γ : Shadow} (hΓ : Γ.Generic) (s : Γ.Strand) :
    Function.Injective (Γ.edgePt s) := by
  sorry

/-- A crossing has a nonempty strand set (used to pick a strand of a crossing). -/
theorem crossing_val_nonempty (y : Γ.Crossing) : y.val.Nonempty :=
  Finset.card_pos.mp (by rw [Γ.crossing_card_two y]; norm_num)

/-- One of the two strands of a crossing (chosen). -/
def someStrand (y : Γ.Crossing) : Γ.Strand := Classical.choose (Γ.crossing_val_nonempty y)

theorem someStrand_mem (y : Γ.Crossing) : Γ.someStrand y ∈ y.val :=
  Classical.choose_spec (Γ.crossing_val_nonempty y)

end Shadow

/-- L0.5: the labels of two non-adjacent edges of a `k`-gon differ by at least `2` in both
cyclic directions. -/
theorem two_le_val_sub_of_not_adjacent {k : ℕ} [NeZero k] {a b : ZMod k} (h : ¬ adjacent a b) :
    2 ≤ (b - a).val ∧ (b - a).val + 2 ≤ k := by
  sorry

/-- L0.6: coordinates in the basis `(do, du)` are unique (`det do du ≠ 0`); the form used
throughout the local geometry. -/
theorem coords_unique {u v : Plane} (hd : det u v ≠ 0) {α β α' β' : ℝ}
    (h : α • u + β • v = α' • u + β' • v) : α = α' ∧ β = β' := by
  sorry

/-- A positive rescaling keeps a regular pair regular (for the half-edges). -/
theorem regularPair_smul_pos {u v : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h : RegularPair u v) : RegularPair (l • u) (m • v) := by
  sorry

/-- Two independent vectors form a regular pair, and so do `u` and `u + v`, `u + v` and `v`
(the corners at the cut points). -/
theorem regularPair_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v := by
  sorry

theorem regularPair_add_right_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (l • u) (u + v) := by
  sorry

theorem regularPair_add_left_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (u + v) (l • v) := by
  sorry

/-! ## §1 The local data at the crossing and the smallness hypotheses -/

namespace Diagram

variable (D : Diagram) (x : D.Γ.Crossing)

/-- The over strand `o`, under strand `u`, their edge parameters at the double point, the double
point and the two edge vectors. -/
abbrev smB_o : D.Γ.Strand := D.overStrand x
abbrev smB_u : D.Γ.Strand := D.underStrand x
def smB_τo : ℝ := D.crossingParam x (D.over_mem x)
def smB_τu : ℝ := D.crossingParam x (D.under_mem x)
abbrev smB_P₀ : Plane := D.Γ.crossingPoint x
abbrev smB_do : Plane := D.Γ.dir (D.overStrand x)
abbrev smB_du : Plane := D.Γ.dir (D.underStrand x)
abbrev smB_vo : D.Γ.Visit := D.overVisit x
abbrev smB_vu : D.Γ.Visit := D.underVisit x

theorem smB_P₀_eq_o : D.smB_P₀ x = D.Γ.edgePt (D.smB_o x) (D.smB_τo x) :=
  (D.crossingParam_spec x (D.over_mem x)).2.2

theorem smB_P₀_eq_u : D.smB_P₀ x = D.Γ.edgePt (D.smB_u x) (D.smB_τu x) :=
  (D.crossingParam_spec x (D.under_mem x)).2.2

theorem smB_τo_pos : 0 < D.smB_τo x := D.crossingParam_pos x _
theorem smB_τo_lt_one : D.smB_τo x < 1 := D.crossingParam_lt_one x _
theorem smB_τu_pos : 0 < D.smB_τu x := D.crossingParam_pos x _
theorem smB_τu_lt_one : D.smB_τu x < 1 := D.crossingParam_lt_one x _
theorem smB_det_ne_zero : det (D.smB_do x) (D.smB_du x) ≠ 0 := D.det_over_under_ne_zero x
theorem smB_o_ne_u : D.smB_o x ≠ D.smB_u x := D.over_ne_under x
theorem smB_do_ne_zero : D.smB_do x ≠ 0 := D.Γ.edge_ne_zero D.generic _
theorem smB_du_ne_zero : D.smB_du x ≠ 0 := D.Γ.edge_ne_zero D.generic _

/-- The four cut points: `om, op` on the over strand, `um, up` on the under strand, at parameter
distance `ε` before (`m`) and after (`p`) the double point. -/
def smB_om (ε : ℝ) : Plane := D.Γ.edgePt (D.smB_o x) (D.smB_τo x - ε)
def smB_op (ε : ℝ) : Plane := D.Γ.edgePt (D.smB_o x) (D.smB_τo x + ε)
def smB_um (ε : ℝ) : Plane := D.Γ.edgePt (D.smB_u x) (D.smB_τu x - ε)
def smB_up (ε : ℝ) : Plane := D.Γ.edgePt (D.smB_u x) (D.smB_τu x + ε)

/-- The cut points in the basis `(do, du)` centred at `P₀`. -/
theorem smB_om_eq (ε : ℝ) : D.smB_om x ε = D.smB_P₀ x + (-ε) • D.smB_do x := by
  sorry
theorem smB_op_eq (ε : ℝ) : D.smB_op x ε = D.smB_P₀ x + ε • D.smB_do x := by
  sorry
theorem smB_um_eq (ε : ℝ) : D.smB_um x ε = D.smB_P₀ x + (-ε) • D.smB_du x := by
  sorry
theorem smB_up_eq (ε : ℝ) : D.smB_up x ε = D.smB_P₀ x + ε • D.smB_du x := by
  sorry

/-- The smallness hypotheses on the cut distance `ε` and the disc radius `r` (design note: "choose
ε small enough that the disc `U = closedBall P₀ r` meets `D` only in the two strand pieces through
`x` and no other crossing/vertex").  Finite sets avoided: the two edge ends of `o` and `u`, the
other occurrences on `o` and `u` (`ε`), all vertices and all edges other than `o`, `u` (`r`). -/
structure Small (ε r : ℝ) : Prop where
  ε_pos : 0 < ε
  ε_lt_τo : ε < D.smB_τo x
  ε_lt_τo' : ε < 1 - D.smB_τo x
  ε_lt_τu : ε < D.smB_τu x
  ε_lt_τu' : ε < 1 - D.smB_τu x
  /-- no other occurrence on the over strand within `ε` of the double point -/
  ε_vis_o : ∀ w : D.Γ.Visit, w.2.val = D.smB_o x → w.1 ≠ x →
    ε < |D.crossingParam w.1 w.2.2 - D.smB_τo x|
  ε_vis_u : ∀ w : D.Γ.Visit, w.2.val = D.smB_u x → w.1 ≠ x →
    ε < |D.crossingParam w.1 w.2.2 - D.smB_τu x|
  r_pos : 0 < r
  /-- the cut points lie strictly inside the disc -/
  εdo_lt_r : ε * ‖D.smB_do x‖ < r
  εdu_lt_r : ε * ‖D.smB_du x‖ < r
  /-- the disc does not reach the ends of `o` and `u` -/
  r_lt_o : r < D.smB_τo x * ‖D.smB_do x‖
  r_lt_o' : r < (1 - D.smB_τo x) * ‖D.smB_do x‖
  r_lt_u : r < D.smB_τu x * ‖D.smB_du x‖
  r_lt_u' : r < (1 - D.smB_τu x) * ‖D.smB_du x‖
  /-- the closed disc misses every other edge -/
  r_seg : ∀ t : D.Γ.Strand, t ≠ D.smB_o x → t ≠ D.smB_u x → ∀ q ∈ D.Γ.seg t, r < dist q (D.smB_P₀ x)

/-- The clean disc of the smoothing. -/
abbrev smB_U (r : ℝ) : Set Plane := Metric.closedBall (D.smB_P₀ x) r

/-- L1.1a: a compact set not containing `P₀` stays at positive distance from it. -/
theorem smB_exists_pos_dist_seg (t : D.Γ.Strand) (ht : D.smB_P₀ x ∉ D.Γ.seg t) :
    ∃ δ > 0, ∀ q ∈ D.Γ.seg t, δ < dist q (D.smB_P₀ x) := by
  sorry

/-- L1.1: small `ε` and `r` exist (finitely many positive constraints). -/
theorem exists_small : ∃ ε r, D.Small x ε r := by
  sorry

variable {ε r : ℝ} (h : D.Small x ε r)

/-- L1.2: consequences of `Small` used everywhere: cut points inside their edges and inside the
open disc, distinct from `P₀`, off the other strand; the two new segments lie in the open disc and
are disjoint from each other and from the half-edges except at their ends. -/
theorem Small.om_mem_interior : D.smB_om x ε ∈ D.Γ.interior (D.smB_o x) := by
  sorry
theorem Small.op_mem_interior : D.smB_op x ε ∈ D.Γ.interior (D.smB_o x) := by
  sorry
theorem Small.um_mem_interior : D.smB_um x ε ∈ D.Γ.interior (D.smB_u x) := by
  sorry
theorem Small.up_mem_interior : D.smB_up x ε ∈ D.Γ.interior (D.smB_u x) := by
  sorry
theorem Small.dist_om : dist (D.smB_om x ε) (D.smB_P₀ x) = ε * ‖D.smB_do x‖ := by
  sorry
theorem Small.om_mem_ball : D.smB_om x ε ∈ Metric.ball (D.smB_P₀ x) r := by
  sorry
theorem Small.op_mem_ball : D.smB_op x ε ∈ Metric.ball (D.smB_P₀ x) r := by
  sorry
theorem Small.um_mem_ball : D.smB_um x ε ∈ Metric.ball (D.smB_P₀ x) r := by
  sorry
theorem Small.up_mem_ball : D.smB_up x ε ∈ Metric.ball (D.smB_P₀ x) r := by
  sorry
theorem Small.om_ne_P₀ : D.smB_om x ε ≠ D.smB_P₀ x := by
  sorry
theorem Small.om_not_mem_seg_u : D.smB_om x ε ∉ D.Γ.seg (D.smB_u x) := by
  sorry

/-- L1.3: the closed disc misses every other edge, every vertex and every other double point. -/
theorem Small.seg_disjoint_ball {t : D.Γ.Strand} (ht : t ≠ D.smB_o x) (ht' : t ≠ D.smB_u x) :
    Disjoint (D.Γ.seg t) (D.smB_U x r) := by
  sorry
theorem Small.tail_not_mem_ball (s : D.Γ.Strand) : D.Γ.tail s ∉ D.smB_U x r := by
  sorry
theorem Small.crossingPoint_not_mem_ball {y : D.Γ.Crossing} (hy : y ≠ x) :
    D.Γ.crossingPoint y ∉ D.smB_U x r := by
  sorry
/-- The disc meets the over strand exactly in the parameters `|t - τo| ≤ r/‖do‖`. -/
theorem Small.edgePt_o_mem_ball_iff (t : ℝ) :
    D.Γ.edgePt (D.smB_o x) t ∈ D.smB_U x r ↔ |t - D.smB_τo x| * ‖D.smB_do x‖ ≤ r := by
  sorry
theorem Small.edgePt_u_mem_ball_iff (t : ℝ) :
    D.Γ.edgePt (D.smB_u x) t ∈ D.smB_U x r ↔ |t - D.smB_τu x| * ‖D.smB_du x‖ ≤ r := by
  sorry

/-- L1.4: the two smoothing segments are disjoint (coefficient comparison in the basis
`(do, du)`: `-(1-t) do + t du = s do - (1-s) du` forces `t - s = 1` and `t - s = -1`). -/
theorem Small.newSeg_disjoint :
    Disjoint (segment ℝ (D.smB_om x ε) (D.smB_up x ε)) (segment ℝ (D.smB_um x ε) (D.smB_op x ε)) := by
  sorry
/-- The segment `om → up` meets the over strand only at `om` and the under strand only at `up`. -/
theorem Small.newSeg₁_inter_o {q : Plane} (hq : q ∈ segment ℝ (D.smB_om x ε) (D.smB_up x ε))
    (ho : q ∈ D.Γ.seg (D.smB_o x)) : q = D.smB_om x ε := by
  sorry
theorem Small.newSeg₁_inter_u {q : Plane} (hq : q ∈ segment ℝ (D.smB_om x ε) (D.smB_up x ε))
    (hu : q ∈ D.Γ.seg (D.smB_u x)) : q = D.smB_up x ε := by
  sorry
theorem Small.newSeg₂_inter_o {q : Plane} (hq : q ∈ segment ℝ (D.smB_um x ε) (D.smB_op x ε))
    (ho : q ∈ D.Γ.seg (D.smB_o x)) : q = D.smB_op x ε := by
  sorry
theorem Small.newSeg₂_inter_u {q : Plane} (hq : q ∈ segment ℝ (D.smB_um x ε) (D.smB_op x ε))
    (hu : q ∈ D.Γ.seg (D.smB_u x)) : q = D.smB_um x ε := by
  sorry
/-- L1.5: the smoothing segments lie in the open disc (convexity). -/
theorem Small.newSeg₁_subset_ball :
    segment ℝ (D.smB_om x ε) (D.smB_up x ε) ⊆ Metric.ball (D.smB_P₀ x) r := by
  sorry
theorem Small.newSeg₂_subset_ball :
    segment ℝ (D.smB_um x ε) (D.smB_op x ε) ⊆ Metric.ball (D.smB_P₀ x) r := by
  sorry

end Diagram

/-! ## §2 Vertex descriptors, the new components, the smoothed shadow -/

/-- A vertex of the smoothed shadow, described symbolically: an old vertex (the tail of a strand
of `Γ`) or one of the four cut points. -/
inductive SmVert (Γ : Shadow)
  | old (s : Γ.Strand)
  | om | op | um | up
  deriving DecidableEq

/-- A component of the smoothed shadow described by a vertex-descriptor sequence. -/
structure DescrComp (Γ : Shadow) where
  k : ℕ
  hk : 3 ≤ k
  d : ZMod k → SmVert Γ

/-- The polygon of a descriptor sequence under a vertex evaluation. -/
def DescrComp.toPoly {Γ : Shadow} (ev : SmVert Γ → Plane) (C : DescrComp Γ) : PolyComp :=
  ⟨C.k, C.hk, ev ∘ C.d⟩

@[simp] theorem DescrComp.toPoly_k {Γ : Shadow} (ev : SmVert Γ → Plane) (C : DescrComp Γ) :
    (C.toPoly ev).k = C.k := rfl

@[simp] theorem DescrComp.toPoly_P {Γ : Shadow} (ev : SmVert Γ → Plane) (C : DescrComp Γ)
    (j : ZMod C.k) : (C.toPoly ev).P j = ev (C.d j) := rfl

/-- The kind of an edge of the smoothed shadow, read off its consecutive descriptor pair. -/
inductive SmKind (Γ : Shadow)
  | old (s : Γ.Strand)
  | hOm | hOp | hUm | hUp | n1 | n2
  deriving DecidableEq

/-- The seven admissible consecutive descriptor pairs (anything else is junk, never produced by
the descriptor sequences below — `smB_shape`). -/
def smB_classify {Γ : Shadow} : SmVert Γ → SmVert Γ → SmKind Γ
  | .old s, .old _ => .old s
  | .old _, .om => .hOm
  | .op, .old _ => .hOp
  | .old _, .um => .hUm
  | .up, .old _ => .hUp
  | .om, .up => .n1
  | .um, .op => .n2
  | _, _ => .n1

namespace Diagram

variable (D : Diagram) (x : D.Γ.Crossing)

/-- Evaluation of vertex descriptors. -/
def smB_evalVert (ε : ℝ) : SmVert D.Γ → Plane
  | .old s => D.Γ.tail s
  | .om => D.smB_om x ε
  | .op => D.smB_op x ε
  | .um => D.smB_um x ε
  | .up => D.smB_up x ε

/-- The label of the under strand on the over strand's component (self-crossing case). -/
def smB_au (h : (D.smB_o x).1 = (D.smB_u x).1) : ZMod (D.Γ.comp (D.smB_o x).1).k :=
  cast (congrArg (fun i => ZMod (D.Γ.comp i).k) h.symm) (D.smB_u x).2

theorem smB_u_eq (h : (D.smB_o x).1 = (D.smB_u x).1) :
    D.smB_u x = ⟨(D.smB_o x).1, D.smB_au x h⟩ := by
  sorry

/-- Self case: `nA` = number of old vertices `P(ao+1), …, P(au)` on the new component `A`,
`nB` = number of old vertices `P(au+1), …, P(ao)` on the new component `B`. -/
def smB_nA (h : (D.smB_o x).1 = (D.smB_u x).1) : ℕ := (D.smB_au x h - (D.smB_o x).2).val
def smB_nB (h : (D.smB_o x).1 = (D.smB_u x).1) : ℕ := ((D.smB_o x).2 - D.smB_au x h).val

theorem smB_two_le_nA (h : (D.smB_o x).1 = (D.smB_u x).1) : 2 ≤ D.smB_nA x h := by
  sorry
theorem smB_two_le_nB (h : (D.smB_o x).1 = (D.smB_u x).1) : 2 ≤ D.smB_nB x h := by
  sorry
theorem smB_nA_add_nB (h : (D.smB_o x).1 = (D.smB_u x).1) :
    D.smB_nA x h + D.smB_nB x h = (D.Γ.comp (D.smB_o x).1).k := by
  sorry

/-- Self case, component `A` (the SM's `(y A)`): `op, P(ao+1), …, P(au), um`; its edges are
`hOp`, the old edges `ao+1 … au-1`, `hUm`, `n2`. -/
def smB_descrA (h : (D.smB_o x).1 = (D.smB_u x).1) : DescrComp D.Γ where
  k := D.smB_nA x h + 2
  hk := by have := D.smB_two_le_nA x h; omega
  d j := if j.val = 0 then .op
    else if j.val = D.smB_nA x h + 1 then .um
    else .old ⟨(D.smB_o x).1, (D.smB_o x).2 + (j.val : ZMod _)⟩

/-- Self case, component `B` (the SM's `(x B)`): `up, P(au+1), …, P(ao), om`; its edges are
`hUp`, the old edges `au+1 … ao-1`, `hOm`, `n1`. -/
def smB_descrB (h : (D.smB_o x).1 = (D.smB_u x).1) : DescrComp D.Γ where
  k := D.smB_nB x h + 2
  hk := by have := D.smB_two_le_nB x h; omega
  d j := if j.val = 0 then .up
    else if j.val = D.smB_nB x h + 1 then .om
    else .old ⟨(D.smB_o x).1, D.smB_au x h + (j.val : ZMod _)⟩

/-- Mixed case, the merged component (the SM's `(x B y A)`): `op, P_o(ao+1), …, P_o(ao), om, up,
P_u(au+1), …, P_u(au), um`; edges `hOp`, old edges of `o`'s component, `hOm`, `n1`, `hUp`, old
edges of `u`'s component, `hUm`, `n2`. -/
def smB_descrM : DescrComp D.Γ where
  k := (D.Γ.comp (D.smB_o x).1).k + (D.Γ.comp (D.smB_u x).1).k + 4
  hk := by omega
  d j :=
    let ko := (D.Γ.comp (D.smB_o x).1).k
    let ku := (D.Γ.comp (D.smB_u x).1).k
    if j.val = 0 then .op
    else if j.val ≤ ko then .old ⟨(D.smB_o x).1, (D.smB_o x).2 + (j.val : ZMod _)⟩
    else if j.val = ko + 1 then .om
    else if j.val = ko + 2 then .up
    else if j.val ≤ ko + ku + 2 then .old ⟨(D.smB_u x).1, (D.smB_u x).2 + ((j.val - ko - 2 : ℕ) : ZMod _)⟩
    else .um

/-- An untouched component, described by its own vertices. -/
def smB_descrOld (i : Fin D.Γ.c) : DescrComp D.Γ where
  k := (D.Γ.comp i).k
  hk := (D.Γ.comp i).hk
  d j := .old ⟨i, j⟩

/-- The reconnected successor `s₁ = s ∘ swap(x, τx)` of the record at the over occurrence. -/
abbrev smB_rec : Perm D.Γ.Visit := D.record.reconnect (D.smB_vo x)

theorem smB_rec_eq : D.smB_rec x = D.visitSucc * swap (D.smB_vo x) (D.smB_vu x) := rfl

/-- The components of the smoothed record: the cycles of `s₁` and the crossing-free circles. -/
abbrev smB_Comps : Type := (D.record.smooth (D.smB_vo x)).comps

/-- The descriptor sequence of a cycle of `s₁`: the cycle through the over occurrence gives `B`
(self) or the merged component (mixed); the cycle through the under occurrence gives `A` (self);
any other cycle is an untouched component. -/
def smB_cycleDescr (q : Quotient (Perm.SameCycle.setoid (D.smB_rec x))) : DescrComp D.Γ :=
  if (D.smB_rec x).SameCycle q.out (D.smB_vo x) then
    (if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_descrB x h else D.smB_descrM x)
  else if (D.smB_rec x).SameCycle q.out (D.smB_vu x) then
    (if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_descrA x h else D.smB_descrM x)
  else D.smB_descrOld (D.compOf q.out)

/-- The descriptor sequence of a component of the smoothed record. -/
def smB_compDescr : D.smB_Comps x → DescrComp D.Γ
  | Sum.inl q => D.smB_cycleDescr x q
  | Sum.inr f => D.smB_descrOld f.1

/-- The number of components of the smoothing and the index bijection. -/
abbrev smB_c : ℕ := Fintype.card (D.smB_Comps x)
def smB_idx : D.smB_Comps x ≃ Fin (D.smB_c x) := Fintype.equivFin _

theorem smB_c_pos : 0 < D.smB_c x := Record.one_le_componentCount_smooth _ _

/-- The descriptor sequence of the `j`-th component. -/
def smB_descrOf (j : Fin (D.smB_c x)) : DescrComp D.Γ := D.smB_compDescr x ((D.smB_idx x).symm j)

/-- **The smoothed shadow.** -/
def smoothShadow (ε : ℝ) : Shadow where
  c := D.smB_c x
  hc := D.smB_c_pos x
  comp j := (D.smB_descrOf x j).toPoly (D.smB_evalVert x ε)

@[simp] theorem smoothShadow_c (ε : ℝ) : (D.smoothShadow x ε).c = D.smB_c x := rfl
@[simp] theorem smoothShadow_comp_k (ε : ℝ) (j : Fin (D.smB_c x)) :
    ((D.smoothShadow x ε).comp j).k = (D.smB_descrOf x j).k := rfl
theorem smoothShadow_P (ε : ℝ) (j : Fin (D.smB_c x)) (m : ZMod (D.smB_descrOf x j).k) :
    ((D.smoothShadow x ε).comp j).P m = D.smB_evalVert x ε ((D.smB_descrOf x j).d m) := rfl

/-- The kind of a strand of the smoothed shadow. -/
def smB_kind (ε : ℝ) (s : (D.smoothShadow x ε).Strand) : SmKind D.Γ :=
  let m : ZMod (D.smB_descrOf x s.1).k := s.2
  smB_classify ((D.smB_descrOf x s.1).d m) ((D.smB_descrOf x s.1).d (m + 1))

/-- The underlying strand of `D` (junk `o` for the two smoothing segments). -/
def smB_toD (ε : ℝ) (s : (D.smoothShadow x ε).Strand) : D.Γ.Strand :=
  match D.smB_kind x ε s with
  | .old d => d
  | .hOm => D.smB_o x
  | .hOp => D.smB_o x
  | .hUm => D.smB_u x
  | .hUp => D.smB_u x
  | .n1 => D.smB_o x
  | .n2 => D.smB_o x

/-- The edge parameter on the underlying strand of `D` of the point at parameter `t` of a strand
of the smoothed shadow (affine rescaling on the half-edges; junk on the smoothing segments). -/
def smB_toParam (ε : ℝ) (s : (D.smoothShadow x ε).Strand) (t : ℝ) : ℝ :=
  match D.smB_kind x ε s with
  | .old _ => t
  | .hOm => t * (D.smB_τo x - ε)
  | .hOp => D.smB_τo x + ε + t * (1 - D.smB_τo x - ε)
  | .hUm => t * (D.smB_τu x - ε)
  | .hUp => D.smB_τu x + ε + t * (1 - D.smB_τu x - ε)
  | .n1 => D.smB_τo x
  | .n2 => D.smB_τo x

/-- The positive factor relating the direction of a strand of the smoothed shadow to the
direction of its underlying strand (`1` on old edges, the parameter lengths on half-edges). -/
def smB_dirScale (ε : ℝ) (s : (D.smoothShadow x ε).Strand) : ℝ :=
  match D.smB_kind x ε s with
  | .old _ => 1
  | .hOm => D.smB_τo x - ε
  | .hOp => 1 - D.smB_τo x - ε
  | .hUm => D.smB_τu x - ε
  | .hUp => 1 - D.smB_τu x - ε
  | .n1 => 1
  | .n2 => 1

/-! ### Positions of the special strands and of the old strands in the new shadow -/

/-- The component of the smoothing carrying the over occurrence's cycle (`B` or the merged
component) and the one carrying the under occurrence's cycle (`A`, or again the merged one). -/
def smB_jO : Fin (D.smB_c x) := D.smB_idx x (Sum.inl (Quotient.mk _ (D.smB_vo x)))
def smB_jU : Fin (D.smB_c x) := D.smB_idx x (Sum.inl (Quotient.mk _ (D.smB_vu x)))

/-- The component index of an untouched component `i` of `D` (a cycle of `s₁` if it carries an
occurrence, a crossing-free circle otherwise). -/
def smB_compIdxOld (i : Fin D.Γ.c) : D.smB_Comps x :=
  if h : ∃ v : D.Γ.Visit, D.compOf v = i then Sum.inl (Quotient.mk _ h.choose)
  else Sum.inr ⟨i, fun v hv => h ⟨v, hv⟩⟩

/-- The strand `⟨j, m⟩` of the smoothed shadow with a natural-number label (cast into the right
`ZMod`, so that no dependent-type transport is needed). -/
def smB_mk (ε : ℝ) (j : Fin (D.smB_c x)) (m : ℕ) : (D.smoothShadow x ε).Strand :=
  ⟨j, (m : ZMod ((D.smoothShadow x ε).comp j).k)⟩

/-- The labels (natural numbers, cast into the component's `ZMod`) of the six special strands:
in the component `jO` (`B`, or the merged one) the half-edge `hUp` (label `lUp`), the half-edge
`hOm` (`lOm`) and the smoothing segment `n1 = om → up` (`lN1`); in the component `jU` (`A`, or
again the merged one) `hOp` (`lOp = 0`), `hUm` (`lUm`) and `n2 = um → op` (`lN2`). -/
def smB_lUp : ℕ := if (D.smB_o x).1 = (D.smB_u x).1 then 0 else (D.Γ.comp (D.smB_o x).1).k + 2
def smB_lOm : ℕ :=
  if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_nB x h else (D.Γ.comp (D.smB_o x).1).k
def smB_lN1 : ℕ :=
  if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_nB x h + 1 else (D.Γ.comp (D.smB_o x).1).k + 1
def smB_lUm : ℕ :=
  if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_nA x h
  else (D.Γ.comp (D.smB_o x).1).k + (D.Γ.comp (D.smB_u x).1).k + 2
def smB_lN2 : ℕ :=
  if h : (D.smB_o x).1 = (D.smB_u x).1 then D.smB_nA x h + 1
  else (D.Γ.comp (D.smB_o x).1).k + (D.Γ.comp (D.smB_u x).1).k + 3

/-- The four half-edges and the two smoothing segments, as strands of the smoothed shadow. -/
def smB_hOp (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jU x) 0
def smB_hUm (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jU x) (D.smB_lUm x)
def smB_n2 (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jU x) (D.smB_lN2 x)
def smB_hUp (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jO x) (D.smB_lUp x)
def smB_hOm (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jO x) (D.smB_lOm x)
def smB_n1 (ε : ℝ) : (D.smoothShadow x ε).Strand := D.smB_mk x ε (D.smB_jO x) (D.smB_lN1 x)

/-- The strand of the smoothed shadow carrying an old strand `d ∉ {o, u}` of `D` (junk on `o`,
`u`): on an untouched component the same label; on the components of `o`, `u` the position in the
descriptor sequences `A`, `B` (self) or `M` (mixed). -/
def smB_ofD (ε : ℝ) (d : D.Γ.Strand) : (D.smoothShadow x ε).Strand :=
  if d.1 = (D.smB_o x).1 then
    (if h : (D.smB_o x).1 = (D.smB_u x).1 then
      -- self case: `d` is `⟨i, ao + m⟩`; on `A` if `1 ≤ m ≤ nA - 1`, on `B` otherwise
      (let m := ((d.2.val : ZMod (D.Γ.comp (D.smB_o x).1).k) - (D.smB_o x).2).val
       if m < D.smB_nA x h then D.smB_mk x ε (D.smB_jU x) m
       else D.smB_mk x ε (D.smB_jO x) ((d.2.val : ZMod (D.Γ.comp (D.smB_o x).1).k) - D.smB_au x h).val)
    else D.smB_mk x ε (D.smB_jO x) ((d.2.val : ZMod (D.Γ.comp (D.smB_o x).1).k) - (D.smB_o x).2).val)
  else if d.1 = (D.smB_u x).1 then
    D.smB_mk x ε (D.smB_jO x)
      ((D.Γ.comp (D.smB_o x).1).k + 2 + ((d.2.val : ZMod (D.Γ.comp (D.smB_u x).1).k) - (D.smB_u x).2).val)
  else D.smB_mk x ε (D.smB_idx x (D.smB_compIdxOld x d.1)) d.2.val

/-! ### §2b Shape of the descriptor sequences: kinds, neighbours, positions -/

variable (ε : ℝ)

/-- The strand following `s` on its component. -/
def smB_next (s : (D.smoothShadow x ε).Strand) : (D.smoothShadow x ε).Strand := ⟨s.1, s.2 + 1⟩

/-- Adjacency in any shadow is "equal or consecutive" (the accepted `adjacent`). -/
theorem smB_adjacent_iff (s t : (D.smoothShadow x ε).Strand) :
    (D.smoothShadow x ε).Adjacent s t ↔ s = t ∨ D.smB_next x ε s = t ∨ D.smB_next x ε t = s := by
  sorry

/-- The kind of the strand following a strand of each kind (the cyclic structure of the descriptor
sequences `A`, `B`, `M`, `Old`). -/
def smB_nextKind : SmKind D.Γ → SmKind D.Γ
  | .old d => if (⟨d.1, d.2 + 1⟩ : D.Γ.Strand) = D.smB_o x then .hOm
      else if (⟨d.1, d.2 + 1⟩ : D.Γ.Strand) = D.smB_u x then .hUm
      else .old ⟨d.1, d.2 + 1⟩
  | .hOm => .n1
  | .n1 => .hUp
  | .hUp => .old ⟨(D.smB_u x).1, (D.smB_u x).2 + 1⟩
  | .hUm => .n2
  | .n2 => .hOp
  | .hOp => .old ⟨(D.smB_o x).1, (D.smB_o x).2 + 1⟩

/-- L2.1 (shape, successor form): the kind of the next strand is determined by the kind. -/
theorem smB_kind_next (s : (D.smoothShadow x ε).Strand) :
    D.smB_kind x ε (D.smB_next x ε s) = D.smB_nextKind x (D.smB_kind x ε s) := by
  sorry

/-- L2.1 (shape, old kinds are genuine): an old kind is never `o` or `u`. -/
theorem smB_kind_old_ne {s : (D.smoothShadow x ε).Strand} {d : D.Γ.Strand}
    (h : D.smB_kind x ε s = .old d) : d ≠ D.smB_o x ∧ d ≠ D.smB_u x := by
  sorry

/-- L2.3: each kind occurs at most once (the kind map is injective). -/
theorem smB_kind_injective : Function.Injective (D.smB_kind x ε) := by
  sorry

/-- L2.3/L2.4: the kinds of the special strands and of the images of old strands. -/
theorem smB_kind_hOm : D.smB_kind x ε (D.smB_hOm x ε) = .hOm := by sorry
theorem smB_kind_hOp : D.smB_kind x ε (D.smB_hOp x ε) = .hOp := by sorry
theorem smB_kind_hUm : D.smB_kind x ε (D.smB_hUm x ε) = .hUm := by sorry
theorem smB_kind_hUp : D.smB_kind x ε (D.smB_hUp x ε) = .hUp := by sorry
theorem smB_kind_n1 : D.smB_kind x ε (D.smB_n1 x ε) = .n1 := by sorry
theorem smB_kind_n2 : D.smB_kind x ε (D.smB_n2 x ε) = .n2 := by sorry
theorem smB_kind_ofD {d : D.Γ.Strand} (hdo : d ≠ D.smB_o x) (hdu : d ≠ D.smB_u x) :
    D.smB_kind x ε (D.smB_ofD x ε d) = .old d := by
  sorry

/-- Every strand is an old image or one of the six special strands. -/
theorem smB_strand_cases (s : (D.smoothShadow x ε).Strand) :
    (∃ d, d ≠ D.smB_o x ∧ d ≠ D.smB_u x ∧ s = D.smB_ofD x ε d) ∨ s = D.smB_hOm x ε ∨
      s = D.smB_hOp x ε ∨ s = D.smB_hUm x ε ∨ s = D.smB_hUp x ε ∨ s = D.smB_n1 x ε ∨
      s = D.smB_n2 x ε := by
  sorry

theorem smB_toD_ofD {d : D.Γ.Strand} (hdo : d ≠ D.smB_o x) (hdu : d ≠ D.smB_u x) :
    D.smB_toD x ε (D.smB_ofD x ε d) = d := by
  sorry

/-! ### §2c Geometry of the strands by kind -/

/-- The edge segment of each kind. -/
def smB_segOfKind : SmKind D.Γ → Set Plane
  | .old d => D.Γ.seg d
  | .hOm => D.Γ.edgePt (D.smB_o x) '' Set.Icc 0 (D.smB_τo x - ε)
  | .hOp => D.Γ.edgePt (D.smB_o x) '' Set.Icc (D.smB_τo x + ε) 1
  | .hUm => D.Γ.edgePt (D.smB_u x) '' Set.Icc 0 (D.smB_τu x - ε)
  | .hUp => D.Γ.edgePt (D.smB_u x) '' Set.Icc (D.smB_τu x + ε) 1
  | .n1 => segment ℝ (D.smB_om x ε) (D.smB_up x ε)
  | .n2 => segment ℝ (D.smB_um x ε) (D.smB_op x ε)

/-- The direction of each kind. -/
def smB_dirOfKind : SmKind D.Γ → Plane
  | .old d => D.Γ.dir d
  | .hOm => (D.smB_τo x - ε) • D.smB_do x
  | .hOp => (1 - D.smB_τo x - ε) • D.smB_do x
  | .hUm => (D.smB_τu x - ε) • D.smB_du x
  | .hUp => (1 - D.smB_τu x - ε) • D.smB_du x
  | .n1 => ε • (D.smB_do x + D.smB_du x)
  | .n2 => ε • (D.smB_do x + D.smB_du x)

/-- L2.2: segment, interior, direction and tail of a strand of the smoothed shadow, by kind. -/
theorem smB_seg_eq (s : (D.smoothShadow x ε).Strand) :
    (D.smoothShadow x ε).seg s = D.smB_segOfKind x ε (D.smB_kind x ε s) := by
  sorry
theorem smB_dir_eq (s : (D.smoothShadow x ε).Strand) :
    (D.smoothShadow x ε).dir s = D.smB_dirOfKind x ε (D.smB_kind x ε s) := by
  sorry
theorem smB_tail_eq (s : (D.smoothShadow x ε).Strand) :
    (D.smoothShadow x ε).tail s = D.smB_evalVert x ε ((D.smB_descrOf x s.1).d s.2) := rfl
/-- The point at parameter `t` of a non-segment strand is the point of the underlying strand at
the rescaled parameter. -/
theorem smB_edgePt_eq (s : (D.smoothShadow x ε).Strand) (hs : D.smB_kind x ε s ≠ .n1)
    (hs' : D.smB_kind x ε s ≠ .n2) (t : ℝ) :
    (D.smoothShadow x ε).edgePt s t = D.Γ.edgePt (D.smB_toD x ε s) (D.smB_toParam x ε s t) := by
  sorry
theorem smB_dir_eq_scale (s : (D.smoothShadow x ε).Strand) (hs : D.smB_kind x ε s ≠ .n1)
    (hs' : D.smB_kind x ε s ≠ .n2) :
    (D.smoothShadow x ε).dir s = D.smB_dirScale x ε s • D.Γ.dir (D.smB_toD x ε s) := by
  sorry
theorem smB_dirScale_pos {r : ℝ} (h : D.Small x ε r) (s : (D.smoothShadow x ε).Strand) :
    0 < D.smB_dirScale x ε s := by
  sorry

/-! ### §2d Underlying crossings and the over data (definitions independent of `Small`) -/

open scoped Classical in
/-- The crossing of `D` underlying a crossing of the smoothed shadow (junk `x` if the underlying
strand pair were not a crossing — it always is, `smB_toD_isCrossing`). -/
def smB_toDCrossing (y : (D.smoothShadow x ε).Crossing) : D.Γ.Crossing :=
  if hy : D.Γ.IsCrossing {D.smB_toD x ε ((D.smoothShadow x ε).someStrand y),
      D.smB_toD x ε ((D.smoothShadow x ε).other y ((D.smoothShadow x ε).someStrand_mem y))}
  then ⟨_, hy⟩ else x

open scoped Classical in
/-- The over strand of the smoothed diagram: the strand of `y` whose underlying strand is the over
strand of `D` at the underlying crossing. -/
def smB_over (y : (D.smoothShadow x ε).Crossing) : (D.smoothShadow x ε).Strand :=
  if D.smB_toD x ε ((D.smoothShadow x ε).someStrand y) = D.overStrand (D.smB_toDCrossing x ε y)
  then (D.smoothShadow x ε).someStrand y
  else (D.smoothShadow x ε).other y ((D.smoothShadow x ε).someStrand_mem y)

theorem smB_over_mem (y : (D.smoothShadow x ε).Crossing) : D.smB_over x ε y ∈ y.val := by
  unfold smB_over
  split_ifs
  · exact (D.smoothShadow x ε).someStrand_mem y
  · exact (D.smoothShadow x ε).other_mem y _

/-- The strand of the smoothed shadow through the occurrence of the crossing `y ≠ x` of `D` on its
strand `d`: the old image, or the half-edge of `o`/`u` containing the double point. -/
def smB_ofDStrandAt (y : D.Γ.Crossing) {d : D.Γ.Strand} (hd : d ∈ y.val) :
    (D.smoothShadow x ε).Strand :=
  if d = D.smB_o x then
    (if D.crossingParam y hd < D.smB_τo x then D.smB_hOm x ε else D.smB_hOp x ε)
  else if d = D.smB_u x then
    (if D.crossingParam y hd < D.smB_τu x then D.smB_hUm x ε else D.smB_hUp x ε)
  else D.smB_ofD x ε d

/-! ## §3 Genericity of the smoothed shadow -/

variable (r : ℝ) (h : D.Small x ε r)
include h

/-- L3.1: every new component is a regular polygon (old corners unchanged up to positive
rescaling; the corners at the cut points are `(l•do, do+du)`-type pairs, regular by
transversality). -/
theorem smB_regular (j : Fin (D.smB_c x)) : Regular ((D.smoothShadow x ε).comp j).P := by
  sorry

/-- L3.2: no vertex on a non-incident edge (old vertices: from `D` and the clean disc; cut points:
inside the disc, on their own half-edges only). -/
theorem smB_tail_off (s t : (D.smoothShadow x ε).Strand)
    (hst : ¬ (D.smoothShadow x ε).IncidentTail s t) :
    (D.smoothShadow x ε).tail s ∉ (D.smoothShadow x ε).seg t := by
  sorry

/-- L3.3: transversality (old–old and old–half-edge meetings are meetings of `D`; nothing else
meets). -/
theorem smB_transverse (s t : (D.smoothShadow x ε).Strand) (hna : ¬ (D.smoothShadow x ε).Adjacent s t)
    (hmeet : ((D.smoothShadow x ε).seg s ∩ (D.smoothShadow x ε).seg t).Nonempty) :
    det ((D.smoothShadow x ε).dir s) ((D.smoothShadow x ε).dir t) ≠ 0 := by
  sorry

/-- L3.4: no triple point (a triple point would be one of `D`, or would lie in the disc). -/
theorem smB_no_triple : ¬ ∃ s t u : (D.smoothShadow x ε).Strand, s ≠ t ∧ t ≠ u ∧ s ≠ u ∧
    ((D.smoothShadow x ε).interior s ∩ (D.smoothShadow x ε).interior t ∩
      (D.smoothShadow x ε).interior u).Nonempty := by
  sorry

/-- L3.5: the smoothed shadow is generic. -/
theorem smoothShadow_generic : (D.smoothShadow x ε).Generic where
  regular := D.smB_regular x ε r h
  tail_off := D.smB_tail_off x ε r h
  transverse := D.smB_transverse x ε r h
  no_triple := D.smB_no_triple x ε r h

/-! ## §4 Crossings, over data, visits of the smoothed shadow -/

/-- **The smoothed diagram.** -/
def smoothDiagram : Diagram where
  Γ := D.smoothShadow x ε
  generic := D.smoothShadow_generic x ε r h
  overStrand := D.smB_over x ε
  over_mem := D.smB_over_mem x ε

@[simp] theorem smoothDiagram_Γ : (D.smoothDiagram x ε r h).Γ = D.smoothShadow x ε := rfl
theorem smoothDiagram_overStrand : (D.smoothDiagram x ε r h).overStrand = D.smB_over x ε := rfl

/-- L4.1: the two strands of a crossing of the smoothed shadow are never smoothing segments, and
their underlying strands form a crossing of `D` other than `x`. -/
theorem smB_crossing_kind_ne_n1 (y : (D.smoothShadow x ε).Crossing) {s : (D.smoothShadow x ε).Strand}
    (hs : s ∈ y.val) : D.smB_kind x ε s ≠ .n1 := by
  sorry
theorem smB_crossing_kind_ne_n2 (y : (D.smoothShadow x ε).Crossing) {s : (D.smoothShadow x ε).Strand}
    (hs : s ∈ y.val) : D.smB_kind x ε s ≠ .n2 := by
  sorry
theorem smB_toD_isCrossing (y : (D.smoothShadow x ε).Crossing) {s t : (D.smoothShadow x ε).Strand}
    (hs : s ∈ y.val) (ht : t ∈ y.val) (hst : s ≠ t) :
    D.Γ.IsCrossing {D.smB_toD x ε s, D.smB_toD x ε t} := by
  sorry
theorem smB_toD_mem (y : (D.smoothShadow x ε).Crossing) {s : (D.smoothShadow x ε).Strand}
    (hs : s ∈ y.val) : D.smB_toD x ε s ∈ (D.smB_toDCrossing x ε y).val := by
  sorry
theorem smB_toDCrossing_ne (y : (D.smoothShadow x ε).Crossing) : D.smB_toDCrossing x ε y ≠ x := by
  sorry
theorem smB_toDCrossing_val (y : (D.smoothShadow x ε).Crossing) :
    (D.smB_toDCrossing x ε y).val = y.val.image (D.smB_toD x ε) := by
  sorry
/-- The double points agree. -/
theorem smB_crossingPoint_eq (y : (D.smoothShadow x ε).Crossing) :
    D.Γ.crossingPoint (D.smB_toDCrossing x ε y) = (D.smoothShadow x ε).crossingPoint y := by
  sorry
theorem smB_toDCrossing_injective : Function.Injective (D.smB_toDCrossing x ε) := by
  sorry

/-- L4.2: the lifted strand pair of a crossing `y ≠ x` is a crossing of the smoothed shadow. -/
theorem smB_ofD_isCrossing (y : D.Γ.Crossing) (hy : y ≠ x) :
    (D.smoothShadow x ε).IsCrossing {D.smB_ofDStrandAt x ε y (D.Γ.someStrand_mem y),
      D.smB_ofDStrandAt x ε y (D.Γ.other_mem y (D.Γ.someStrand_mem y))} := by
  sorry

/-- The crossing of the smoothed shadow over a crossing `y ≠ x` of `D`. -/
def smB_ofDCrossing (y : {y : D.Γ.Crossing // y ≠ x}) : (D.smoothShadow x ε).Crossing :=
  ⟨_, D.smB_ofD_isCrossing x ε r h y.1 y.2⟩

theorem smB_toD_ofDCrossing (y : {y : D.Γ.Crossing // y ≠ x}) :
    D.smB_toDCrossing x ε (D.smB_ofDCrossing x ε r h y) = y.1 := by
  sorry
theorem smB_ofD_toDCrossing (y : (D.smoothShadow x ε).Crossing) :
    D.smB_ofDCrossing x ε r h ⟨D.smB_toDCrossing x ε y, D.smB_toDCrossing_ne x ε r h y⟩ = y := by
  sorry

/-- The crossing bijection: crossings of the smoothing ↔ crossings of `D` other than `x`
("It removes just the selected crossing and creates no other crossing", sm-3:1085-1086). -/
def smB_crossingEquiv : (D.smoothShadow x ε).Crossing ≃ {y : D.Γ.Crossing // y ≠ x} where
  toFun y := ⟨D.smB_toDCrossing x ε y, D.smB_toDCrossing_ne x ε r h y⟩
  invFun := D.smB_ofDCrossing x ε r h
  left_inv := D.smB_ofD_toDCrossing x ε r h
  right_inv y := Subtype.ext (D.smB_toD_ofDCrossing x ε r h y)

/-- L4.3: the over data is carried to the over data of `D`. -/
theorem smB_toD_over (y : (D.smoothShadow x ε).Crossing) :
    D.smB_toD x ε ((D.smoothDiagram x ε r h).overStrand y) = D.overStrand (D.smB_toDCrossing x ε y) := by
  sorry
theorem smB_toD_under (y : (D.smoothShadow x ε).Crossing) :
    D.smB_toD x ε ((D.smoothDiagram x ε r h).underStrand y) = D.underStrand (D.smB_toDCrossing x ε y) := by
  sorry

/-- L4.5: the crossing parameter transports by the parameter rescaling of the strand. -/
theorem smB_crossingParam_eq (y : (D.smoothShadow x ε).Crossing) {s : (D.smoothShadow x ε).Strand}
    (hs : s ∈ y.val) :
    D.crossingParam (D.smB_toDCrossing x ε y) (D.smB_toD_mem x ε r h y hs) =
      D.smB_toParam x ε s ((D.smoothDiagram x ε r h).crossingParam y hs) := by
  sorry

/-- L4.6: signs agree (directions are positive multiples). -/
theorem smB_sign_eq (y : (D.smoothShadow x ε).Crossing) :
    (D.smoothDiagram x ε r h).sign y = D.sign (D.smB_toDCrossing x ε y) := by
  sorry

/-- The occurrence of `D` underlying an occurrence of the smoothing. -/
def smB_toDVisit (w : (D.smoothDiagram x ε r h).Γ.Visit) : D.Γ.Visit :=
  ⟨D.smB_toDCrossing x ε w.1, ⟨D.smB_toD x ε w.2.val, D.smB_toD_mem x ε r h w.1 w.2.2⟩⟩

theorem smB_toDVisit_keep (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    D.record.SmoothKeep (D.smB_vo x) (D.smB_toDVisit x ε r h w) := by
  sorry
theorem smB_toDVisit_injective : Function.Injective (D.smB_toDVisit x ε r h) := by
  sorry
theorem smB_toDVisit_surjective (v : D.Γ.Visit) (hv : D.record.SmoothKeep (D.smB_vo x) v) :
    ∃ w, D.smB_toDVisit x ε r h w = v := by
  sorry

/-- L4.4: the occurrence bijection `Φ` of the record isomorphism: occurrences of the smoothing ↔
retained occurrences of `D` (`M' = M ∖ {x, τx}`). -/
def smB_visitEquiv :
    (D.smoothDiagram x ε r h).Γ.Visit ≃ {v : D.Γ.Visit // D.record.SmoothKeep (D.smB_vo x) v} :=
  Equiv.ofBijective (fun w => ⟨D.smB_toDVisit x ε r h w, D.smB_toDVisit_keep x ε r h w⟩)
    ⟨fun w w' e => D.smB_toDVisit_injective x ε r h (congrArg Subtype.val e),
     fun v => by
      obtain ⟨w, hw⟩ := D.smB_toDVisit_surjective x ε r h v.1 v.2
      exact ⟨w, Subtype.ext hw⟩⟩

@[simp] theorem smB_visitEquiv_apply_val (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    (D.smB_visitEquiv x ε r h w).1 = D.smB_toDVisit x ε r h w := rfl

/-- Pairing transports (`twin ↔ twin`). -/
theorem smB_toDVisit_twin (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    D.smB_toDVisit x ε r h ((D.smoothDiagram x ε r h).twin w) = D.twin (D.smB_toDVisit x ε r h w) := by
  sorry
/-- Bits transport (`overBit`). -/
theorem smB_overBit_eq (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    (D.smoothDiagram x ε r h).overBit w = D.overBit (D.smB_toDVisit x ε r h w) := by
  sorry

/-! ## §5 Components and the cyclic order of occurrences -/

/-- L5.1: the component of an occurrence of the smoothing is the index of the `s₁`-cycle of the
underlying occurrence (the polygon of a cycle carries exactly the retained occurrences of that
cycle: `A` carries the `A`-word, `B` the `B`-word, the merged component both words). -/
theorem smB_compOf_eq (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    (D.smoothDiagram x ε r h).compOf w =
      D.smB_idx x (Sum.inl (Quotient.mk _ (D.smB_toDVisit x ε r h w))) := by
  sorry

omit h in
/-- The smoothed coordinate of an occurrence of `D`: the traversal offset from the over
occurrence on `o`'s circle, `k_o +` the offset from the under occurrence on `u`'s circle, and the
plain traversal coordinate elsewhere.  On every `s₁`-cycle this is a coordinate for the cyclic
order in which the smoothing traverses the retained occurrences. -/
def smB_off (v : D.Γ.Visit) : ℝ :=
  if D.compOf v = (D.smB_o x).1 then
    cyclicOffset (D.Γ.comp (D.smB_o x).1).k (D.visitCoord (D.smB_vo x)) (D.visitCoord v)
  else if D.compOf v = (D.smB_u x).1 then
    (D.Γ.comp (D.smB_o x).1).k +
      cyclicOffset (D.Γ.comp (D.smB_u x).1).k (D.visitCoord (D.smB_vu x)) (D.visitCoord v)
  else D.visitCoord v

/-- L5.2a: on each component of the smoothing the traversal coordinate is a strictly increasing
(piecewise affine) function of the smoothed coordinate of the underlying occurrence. -/
theorem smB_exists_monotone_coord (j : Fin (D.smB_c x)) :
    ∃ G : ℝ → ℝ, StrictMonoOn G (Set.Ico 0 (((D.smoothShadow x ε).comp j).k : ℝ)) ∧
      ∀ w : (D.smoothDiagram x ε r h).Γ.Visit, (D.smoothDiagram x ε r h).compOf w = j →
        D.smB_off x (D.smB_toDVisit x ε r h w) = G ((D.smoothDiagram x ε r h).visitCoord w) := by
  sorry

/-- L5.2: coordinates compare as the smoothed coordinates of the underlying occurrences. -/
theorem smB_visitCoord_lt_iff (w w' : (D.smoothDiagram x ε r h).Γ.Visit)
    (hc : (D.smoothDiagram x ε r h).compOf w' = (D.smoothDiagram x ε r h).compOf w) :
    (D.smoothDiagram x ε r h).visitCoord w < (D.smoothDiagram x ε r h).visitCoord w' ↔
      D.smB_off x (D.smB_toDVisit x ε r h w) < D.smB_off x (D.smB_toDVisit x ε r h w') := by
  sorry

/-- L5.3: the oriented cyclic order of the smoothing is the cyclic order of smoothed coordinates. -/
theorem smB_visitBetween_iff (w w' w'' : (D.smoothDiagram x ε r h).Γ.Visit)
    (hc' : (D.smoothDiagram x ε r h).compOf w' = (D.smoothDiagram x ε r h).compOf w)
    (hc'' : (D.smoothDiagram x ε r h).compOf w'' = (D.smoothDiagram x ε r h).compOf w) :
    (D.smoothDiagram x ε r h).VisitBetween w w' w'' ↔
      cycBetween (D.smB_off x (D.smB_toDVisit x ε r h w)) (D.smB_off x (D.smB_toDVisit x ε r h w'))
        (D.smB_off x (D.smB_toDVisit x ε r h w'')) := by
  sorry

omit h in
/-- L5.4a: the reconnected successor `s₁` is the cyclic successor for the smoothed coordinate on
each of its cycles (`s₁ v = s v` away from `x, τx` by `nextVisit_no_between`; at `x` the jump to
`s (τx)` skips exactly the other word). -/
theorem smB_reconnect_no_between (v u : D.Γ.Visit) (hu : (D.smB_rec x).SameCycle u v) :
    ¬ cycBetween (D.smB_off x v) (D.smB_off x u) (D.smB_off x (D.smB_rec x v)) := by
  sorry

omit h in
/-- The smoothed coordinate is injective on each `s₁`-cycle. -/
theorem smB_off_injOn (v u : D.Γ.Visit) (hu : (D.smB_rec x).SameCycle u v)
    (he : D.smB_off x u = D.smB_off x v) : u = v := by
  sorry

/-- L5.4b (general): the first return of a cyclic-successor permutation to a set `p` is the
cyclic successor within `p` on the cycle (no `p`-element strictly between). -/
theorem firstReturn_no_between {α : Type*} [Fintype α] (f : Perm α) (p : α → Prop)
    [DecidablePred p] (κ : α → ℝ)
    (hκ : ∀ v u, f.SameCycle u v → κ u = κ v → u = v)
    (hf : ∀ v u, f.SameCycle u v → ¬ cycBetween (κ v) (κ u) (κ (f v)))
    (v : {m // p m}) (u : α) (hu : f.SameCycle u v.1) (hp : p u) :
    ¬ cycBetween (κ v.1) (κ u) (κ (firstReturn f p v).1) := by
  sorry

/-- L5.4: the successor of the smoothing is the smoothed record's successor
(`s'(s⁻¹x) = s(τx)`, `s'(s⁻¹ τx) = s x`, `s' = s` elsewhere; sm-3:1092-1096). -/
theorem smB_nextVisit (w : (D.smoothDiagram x ε r h).Γ.Visit) :
    D.smB_toDVisit x ε r h ((D.smoothDiagram x ε r h).nextVisit w) =
      ((D.record.smooth (D.smB_vo x)).succ (D.smB_visitEquiv x ε r h w)).1 := by
  sorry

/-! ## §6 The record isomorphism and the counts -/

/-- The five clauses of the record isomorphism, each stated with the exact type of the
corresponding `RecordIso` field. -/
theorem smB_comp_eq (w : (D.smoothDiagram x ε r h).record.M) :
    (D.record.smooth (D.smB_vo x)).comp (D.smB_visitEquiv x ε r h w) =
      (D.smB_idx x).symm ((D.smoothDiagram x ε r h).record.comp w) := by
  have h1 : (D.smoothDiagram x ε r h).record.comp w = (D.smoothDiagram x ε r h).compOf w := rfl
  have h2 : (D.record.smooth (D.smB_vo x)).comp (D.smB_visitEquiv x ε r h w) =
      Sum.inl (Quotient.mk _ (D.smB_toDVisit x ε r h w)) := rfl
  rw [h1, h2, D.smB_compOf_eq x ε r h w]
  exact (Equiv.symm_apply_apply _ _).symm

theorem smB_succ_eq (w : (D.smoothDiagram x ε r h).record.M) :
    D.smB_visitEquiv x ε r h ((D.smoothDiagram x ε r h).record.succ w) =
      (D.record.smooth (D.smB_vo x)).succ (D.smB_visitEquiv x ε r h w) := by
  apply Subtype.ext
  rw [smB_visitEquiv_apply_val, record_succ_apply]
  exact D.smB_nextVisit x ε r h w

theorem smB_pair_eq (w : (D.smoothDiagram x ε r h).record.M) :
    D.smB_visitEquiv x ε r h ((D.smoothDiagram x ε r h).record.pair w) =
      (D.record.smooth (D.smB_vo x)).pair (D.smB_visitEquiv x ε r h w) := by
  apply Subtype.ext
  have h3 : ((D.record.smooth (D.smB_vo x)).pair (D.smB_visitEquiv x ε r h w)).1 =
      D.twin (D.smB_toDVisit x ε r h w) := rfl
  rw [smB_visitEquiv_apply_val, record_pair_apply, h3]
  exact D.smB_toDVisit_twin x ε r h w

theorem smB_bit_eq (w : (D.smoothDiagram x ε r h).record.M) :
    (D.record.smooth (D.smB_vo x)).isOver (D.smB_visitEquiv x ε r h w) =
      (D.smoothDiagram x ε r h).record.isOver w := by
  have h3 : (D.record.smooth (D.smB_vo x)).isOver (D.smB_visitEquiv x ε r h w) =
      D.overBit (D.smB_toDVisit x ε r h w) := rfl
  have h4 : (D.smoothDiagram x ε r h).record.isOver w = (D.smoothDiagram x ε r h).overBit w := rfl
  rw [h3, h4]
  exact (D.smB_overBit_eq x ε r h w).symm

theorem smB_sgn_eq (w : (D.smoothDiagram x ε r h).record.M) :
    (D.record.smooth (D.smB_vo x)).sgn (D.smB_visitEquiv x ε r h w) =
      (D.smoothDiagram x ε r h).record.sgn w := by
  have h3 : (D.record.smooth (D.smB_vo x)).sgn (D.smB_visitEquiv x ε r h w) =
      D.sign (D.smB_toDCrossing x ε w.1) := rfl
  have h4 : (D.smoothDiagram x ε r h).record.sgn w = (D.smoothDiagram x ε r h).sign w.1 := rfl
  rw [h3, h4]
  exact (D.smB_sign_eq x ε r h w.1).symm

/-- **`smoothing_record` for the constructed smoothing**: the record of the smoothed diagram is
isomorphic to the record of `D` smoothed at the over occurrence of `x`. -/
def smoothRecordIso :
    RecordIso (D.smoothDiagram x ε r h).record (D.record.smooth (D.smB_vo x)) where
  e := (D.smB_idx x).symm
  Φ := D.smB_visitEquiv x ε r h
  comp_eq := D.smB_comp_eq x ε r h
  succ_eq := D.smB_succ_eq x ε r h
  pair_eq := D.smB_pair_eq x ε r h
  bit_eq := D.smB_bit_eq x ε r h
  sgn_eq := D.smB_sgn_eq x ε r h

/-- The design's record clause, instantiated (`SmoothingRecordClause` of LinkMoves). -/
theorem smoothing_record_clause :
    SmoothingRecordClause Diagram.record (fun _ v => v) D x (D.smoothDiagram x ε r h) :=
  ⟨D.smoothRecordIso x ε r h⟩

omit h in
/-- `x` is a self crossing of the record iff `o` and `u` lie on one component. -/
theorem smB_isSelfCrossing_iff :
    D.record.IsSelfCrossing (D.smB_vo x) ↔ (D.smB_o x).1 = (D.smB_u x).1 :=
  D.record_isSelfCrossing_iff (D.smB_vo x)

/-- "the resulting component counts are `c+1`, or `c−1 ≥ 1` in the mixed case" (sm-3:1099-1100). -/
theorem smoothDiagram_componentCount :
    (D.smoothDiagram x ε r h).componentCount =
      if (D.smB_o x).1 = (D.smB_u x).1 then D.componentCount + 1 else D.componentCount - 1 := by
  have h1 := (D.smoothRecordIso x ε r h).componentCount_eq
  rw [record_componentCount] at h1
  rw [h1, Record.componentCount_smooth, D.record_componentCount]
  by_cases hs : (D.smB_o x).1 = (D.smB_u x).1
  · rw [ite_eq_left ((D.smB_isSelfCrossing_iff x).mpr hs), ite_eq_left hs]
  · rw [ite_eq_right (fun hc => hs ((D.smB_isSelfCrossing_iff x).mp hc)), ite_eq_right hs]

/-- "Its crossing count is `N−1`" (sm-3:1102). -/
theorem smoothDiagram_card_crossing :
    Fintype.card (D.smoothDiagram x ε r h).Γ.Crossing + 1 = Fintype.card D.Γ.Crossing := by
  sorry

/-! ## §7 The oriented-smoothing data: clean disc, outside match, arcs -/

omit h in
/-- Clamp into `[0, 1)` (junk `0` outside; every use is inside). -/
def smB_ico (t : ℝ) : Set.Ico (0 : ℝ) 1 :=
  if ht : 0 ≤ t ∧ t < 1 then ⟨t, ht⟩ else ⟨0, ⟨le_rfl, zero_lt_one⟩⟩

omit h in
/-- The traversal point of the smoothing over a traversal point of `D` (meaningful outside the
open disc): the same parameter on old edges, the rescaled parameter on the half-edges. -/
def smB_ofDPt (p : D.Γ.Pt) : (D.smoothShadow x ε).Pt :=
  if (⟨p.1, p.2.1⟩ : D.Γ.Strand) = D.smB_o x then
    (if p.2.2.val < D.smB_τo x then
      ⟨(D.smB_hOm x ε).1, ((D.smB_hOm x ε).2, smB_ico (p.2.2.val / (D.smB_τo x - ε)))⟩
     else ⟨(D.smB_hOp x ε).1,
      ((D.smB_hOp x ε).2, smB_ico ((p.2.2.val - D.smB_τo x - ε) / (1 - D.smB_τo x - ε)))⟩)
  else if (⟨p.1, p.2.1⟩ : D.Γ.Strand) = D.smB_u x then
    (if p.2.2.val < D.smB_τu x then
      ⟨(D.smB_hUm x ε).1, ((D.smB_hUm x ε).2, smB_ico (p.2.2.val / (D.smB_τu x - ε)))⟩
     else ⟨(D.smB_hUp x ε).1,
      ((D.smB_hUp x ε).2, smB_ico ((p.2.2.val - D.smB_τu x - ε) / (1 - D.smB_τu x - ε)))⟩)
  else ⟨(D.smB_ofD x ε ⟨p.1, p.2.1⟩).1, ((D.smB_ofD x ε ⟨p.1, p.2.1⟩).2, p.2.2)⟩

omit h in
/-- The traversal point of `D` under a traversal point of the smoothing (junk on the smoothing
segments, which lie inside the open disc). -/
def smB_toDPt (q : (D.smoothShadow x ε).Pt) : D.Γ.Pt :=
  ⟨(D.smB_toD x ε ((D.smoothShadow x ε).strandOf q)).1,
    ((D.smB_toD x ε ((D.smoothShadow x ε).strandOf q)).2,
      smB_ico (D.smB_toParam x ε ((D.smoothShadow x ε).strandOf q) q.2.2.val))⟩

/-- L7.2a: the two maps are inverse bijections between the outside traversal points, tracing the
same plane points. -/
theorem smB_ofDPt_outside (p : D.Γ.Outside (D.smB_U x r)) :
    (D.smoothShadow x ε).eval (D.smB_ofDPt x ε p.1) ∉ interior (D.smB_U x r) := by
  sorry
theorem smB_toDPt_outside (q : (D.smoothDiagram x ε r h).Γ.Outside (D.smB_U x r)) :
    D.Γ.eval (D.smB_toDPt x ε q.1) ∉ interior (D.smB_U x r) := by
  sorry
theorem smB_toDPt_ofDPt (p : D.Γ.Outside (D.smB_U x r)) :
    D.smB_toDPt x ε (D.smB_ofDPt x ε p.1) = p.1 := by
  sorry
theorem smB_ofDPt_toDPt (q : (D.smoothDiagram x ε r h).Γ.Outside (D.smB_U x r)) :
    D.smB_ofDPt x ε (D.smB_toDPt x ε q.1) = q.1 := by
  sorry
theorem smB_eval_ofDPt (p : D.Γ.Outside (D.smB_U x r)) :
    (D.smoothShadow x ε).eval (D.smB_ofDPt x ε p.1) = D.Γ.eval p.1 := by
  sorry

/-- The outside correspondence `φ`. -/
def smB_outside : D.Γ.Outside (D.smB_U x r) ≃ (D.smoothDiagram x ε r h).Γ.Outside (D.smB_U x r) where
  toFun p := ⟨D.smB_ofDPt x ε p.1, D.smB_ofDPt_outside x ε r h p⟩
  invFun q := ⟨D.smB_toDPt x ε q.1, D.smB_toDPt_outside x ε r h q⟩
  left_inv p := Subtype.ext (D.smB_toDPt_ofDPt x ε r h p)
  right_inv q := Subtype.ext (D.smB_ofDPt_toDPt x ε r h q)

/-- L7.2b: directions agree up to the positive factor `dirScale` (forward and arriving). -/
theorem smB_dir_pos (p : D.Γ.Outside (D.smB_U x r)) (hp : D.Γ.eval p.1 ∉ D.smB_U x r) :
    ∃ l : ℝ, 0 < l ∧ (D.smoothShadow x ε).dir ((D.smoothShadow x ε).strandOf (D.smB_ofDPt x ε p.1)) =
      l • D.Γ.dir (D.Γ.strandOf p.1) := by
  sorry
theorem smB_dir_pos_before (p : D.Γ.Outside (D.smB_U x r)) (hp : D.Γ.eval p.1 ∉ D.smB_U x r) :
    ∃ l : ℝ, 0 < l ∧
      (D.smoothShadow x ε).dir ((D.smoothShadow x ε).strandBefore (D.smB_ofDPt x ε p.1)) =
        l • D.Γ.dir (D.Γ.strandBefore p.1) := by
  sorry

/-- L7.2c: the outer crossings of `D` are the crossings other than `x`; every crossing of the
smoothing is outer. -/
theorem smB_outer_iff (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∉ interior (D.smB_U x r) ↔ y ≠ x := by
  sorry
theorem smB_outer₀ (y : (D.smoothDiagram x ε r h).Γ.Crossing) :
    (D.smoothDiagram x ε r h).Γ.crossingPoint y ∉ interior (D.smB_U x r) := by
  sorry

/-- The outer-crossing correspondence `ψ`. -/
def smB_outer : D.OuterCrossing (D.smB_U x r) ≃ (D.smoothDiagram x ε r h).OuterCrossing (D.smB_U x r) :=
  (Equiv.subtypeEquivRight (D.smB_outer_iff x ε r h)).trans
    ((D.smB_crossingEquiv x ε r h).symm.trans (Equiv.subtypeUnivEquiv (D.smB_outer₀ x ε r h)).symm)

/-- L7.2d: over and under occurrences correspond under `φ` and `ψ`. -/
theorem smB_over_eq (y : D.OuterCrossing (D.smB_U x r)) :
    D.smB_outside x ε r h (D.outerOverPt y) = (D.smoothDiagram x ε r h).outerOverPt (D.smB_outer x ε r h y) := by
  sorry
theorem smB_under_eq (y : D.OuterCrossing (D.smB_U x r)) :
    D.smB_outside x ε r h (D.outerUnderPt y) = (D.smoothDiagram x ε r h).outerUnderPt (D.smB_outer x ε r h y) := by
  sorry

/-- The outside match of the smoothing. -/
def smB_outsideMatch : OutsideMatch (D.smB_U x r) D (D.smoothDiagram x ε r h) where
  φ := D.smB_outside x ε r h
  eval_eq p := D.smB_eval_ofDPt x ε r h p
  dir_pos p hp := D.smB_dir_pos x ε r h p hp
  dir_pos_before p hp := D.smB_dir_pos_before x ε r h p hp
  ψ := D.smB_outer x ε r h
  over_eq := D.smB_over_eq x ε r h
  under_eq := D.smB_under_eq x ε r h

/-- L7.1: both diagrams meet the disc cleanly (the four frontier points are traversed once; every
component has a vertex, and all vertices are outside the disc). -/
theorem smB_clean : Clean (D.smB_U x r) D := by
  sorry
theorem smB_clean₀ : Clean (D.smB_U x r) (D.smoothDiagram x ε r h) := by
  sorry

theorem smB_frame : LocalFrame (D.smB_U x r) D (D.smoothDiagram x ε r h) :=
  ⟨isDisc_closedBall _ h.r_pos, D.smB_clean x ε r h, D.smB_clean₀ x ε r h⟩

omit h in
/-- The half-widths of the disc in edge parameters of `o` and `u`. -/
def smB_ρo : ℝ := r / ‖D.smB_do x‖
omit h in
def smB_ρu : ℝ := r / ‖D.smB_du x‖

omit h in
/-- The arc of `D` through the over occurrence: the piece of the edge `o` inside the disc. -/
def smB_a : D.Γ.Arc :=
  ⟨(D.smB_o x).1, ((D.smB_o x).2, smB_ico (D.smB_τo x - D.smB_ρo x r)),
    ((D.smB_o x).2, smB_ico (D.smB_τo x + D.smB_ρo x r))⟩
omit h in
/-- The arc of `D` through the under occurrence. -/
def smB_b : D.Γ.Arc :=
  ⟨(D.smB_u x).1, ((D.smB_u x).2, smB_ico (D.smB_τu x - D.smB_ρu x r)),
    ((D.smB_u x).2, smB_ico (D.smB_τu x + D.smB_ρu x r))⟩

omit h in
/-- The smoothing arc `a₀`: from the entering end of `a` (on `hOm`) through `om`, `n1`, `up` to
the exiting end of `b` (on `hUp`); it lies on the component `jO`. -/
def smB_a₀ : (D.smoothShadow x ε).Arc :=
  ⟨D.smB_jO x,
    ((D.smB_lOm x : ZMod ((D.smoothShadow x ε).comp (D.smB_jO x)).k),
      smB_ico ((D.smB_τo x - D.smB_ρo x r) / (D.smB_τo x - ε))),
    ((D.smB_lUp x : ZMod ((D.smoothShadow x ε).comp (D.smB_jO x)).k),
      smB_ico ((D.smB_ρu x r - ε) / (1 - D.smB_τu x - ε)))⟩

omit h in
/-- The smoothing arc `b₀`: from the entering end of `b` (on `hUm`) through `um`, `n2`, `op` to
the exiting end of `a` (on `hOp`); it lies on the component `jU`. -/
def smB_b₀ : (D.smoothShadow x ε).Arc :=
  ⟨D.smB_jU x,
    ((D.smB_lUm x : ZMod ((D.smoothShadow x ε).comp (D.smB_jU x)).k),
      smB_ico ((D.smB_τu x - D.smB_ρu x r) / (D.smB_τu x - ε))),
    ((0 : ZMod ((D.smoothShadow x ε).comp (D.smB_jU x)).k),
      smB_ico ((D.smB_ρo x r - ε) / (1 - D.smB_τo x - ε)))⟩

/-- L7.3: the arc data. -/
theorem smB_a_ne_b : D.smB_a x r ≠ D.smB_b x r := by
  sorry
theorem smB_arcCover : D.Γ.ArcCover (D.smB_U x r) {D.smB_a x r, D.smB_b x r} := by
  sorry
theorem smB_over_on_a : D.OverOn (D.smB_a x r) x := by
  sorry
theorem smB_under_on_b : D.UnderOn (D.smB_b x r) x := by
  sorry
theorem smB_inner_iff (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∈ interior (D.smB_U x r) ↔ y = x := by
  sorry
theorem smB_a₀_ne_b₀ : D.smB_a₀ x ε r ≠ D.smB_b₀ x ε r := by
  sorry
theorem smB_arcCover₀ :
    (D.smoothDiagram x ε r h).Γ.ArcCover (D.smB_U x r) {D.smB_a₀ x ε r, D.smB_b₀ x ε r} := by
  sorry
theorem smB_a₀_start :
    (D.smoothDiagram x ε r h).Γ.eval (D.smB_a₀ x ε r).startPt = D.Γ.eval (D.smB_a x r).startPt := by
  sorry
theorem smB_a₀_stop :
    (D.smoothDiagram x ε r h).Γ.eval (D.smB_a₀ x ε r).stopPt = D.Γ.eval (D.smB_b x r).stopPt := by
  sorry
theorem smB_b₀_start :
    (D.smoothDiagram x ε r h).Γ.eval (D.smB_b₀ x ε r).startPt = D.Γ.eval (D.smB_b x r).startPt := by
  sorry
theorem smB_b₀_stop :
    (D.smoothDiagram x ε r h).Γ.eval (D.smB_b₀ x ε r).stopPt = D.Γ.eval (D.smB_a x r).stopPt := by
  sorry

/-- L7.4: the oriented-smoothing data of the constructed smoothing. -/
def smB_orientedSmoothingData : OrientedSmoothingData (D.smB_U x r) D x (D.smoothDiagram x ε r h) where
  frame := D.smB_frame x ε r h
  center := Metric.ball_subset_interior_closedBall (Metric.mem_ball_self h.r_pos)
  out := D.smB_outsideMatch x ε r h
  a := D.smB_a x r
  b := D.smB_b x r
  ab := D.smB_a_ne_b x ε r h
  cover := D.smB_arcCover x ε r h
  over_on_a := D.smB_over_on_a x ε r h
  under_on_b := D.smB_under_on_b x ε r h
  inner_iff := D.smB_inner_iff x ε r h
  a₀ := D.smB_a₀ x ε r
  b₀ := D.smB_b₀ x ε r
  ab₀ := D.smB_a₀_ne_b₀ x ε r h
  cover₀ := D.smB_arcCover₀ x ε r h
  no_inner₀ := D.smB_outer₀ x ε r h
  a₀_start := D.smB_a₀_start x ε r h
  a₀_stop := D.smB_a₀_stop x ε r h
  b₀_start := D.smB_b₀_start x ε r h
  b₀_stop := D.smB_b₀_stop x ε r h

/-- The constructed diagram is an oriented smoothing of `D` at `x`. -/
theorem isOrientedSmoothing_smoothDiagram : IsOrientedSmoothing D x (D.smoothDiagram x ε r h) :=
  ⟨D.smB_U x r, ⟨D.smB_orientedSmoothingData x ε r h⟩⟩

end Diagram

/-! ## §8 The goal theorems -/

/-- **exists_smoothing** (design file, skein_and_moves; sm-3:1084-1086): every crossing of every
diagram admits an oriented smoothing. -/
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ :=
  let ⟨ε, r, h⟩ := D.exists_small x
  ⟨D.smoothDiagram x ε r h, D.isOrientedSmoothing_smoothDiagram x ε r h⟩

/-- **smoothing_record** (constructed form, the one the `(N, b)` inductions of
rp:record-polynomial and lp:core use — "the resulting actual smoothed diagrams", sm-3:1256-1258):
there is an oriented smoothing of `D` at `x` whose record is isomorphic to the record of `D`
smoothed at the over occurrence of `x`. -/
theorem smoothing_record (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) :=
  let ⟨ε, r, h⟩ := D.exists_small x
  ⟨D.smoothDiagram x ε r h, D.isOrientedSmoothing_smoothDiagram x ε r h, ⟨D.smoothRecordIso x ε r h⟩⟩

/-- The same, in the `SmoothingRecordClause` form of LinkMoves. -/
theorem smoothing_record_clause (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      SmoothingRecordClause Diagram.record (fun _ v => v) D x D₀ :=
  let ⟨ε, r, h⟩ := D.exists_small x
  ⟨D.smoothDiagram x ε r h, D.isOrientedSmoothing_smoothDiagram x ε r h,
    D.smoothing_record_clause x ε r h⟩

/-- The consumers' package: an oriented smoothing with `N(D₀) + 1 = N(D)`, `c(D₀) = c ± 1` and
the record bridge (sm-3:1097-1103). -/
theorem exists_smoothing_with_counts (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing ∧
      D₀.componentCount = (if (D.overStrand x).1 = (D.underStrand x).1 then D.componentCount + 1
        else D.componentCount - 1) ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) :=
  let ⟨ε, r, h⟩ := D.exists_small x
  ⟨D.smoothDiagram x ε r h, D.isOrientedSmoothing_smoothDiagram x ε r h,
    D.smoothDiagram_card_crossing x ε r h, D.smoothDiagram_componentCount x ε r h,
    ⟨D.smoothRecordIso x ε r h⟩⟩

end

end SM.Link
