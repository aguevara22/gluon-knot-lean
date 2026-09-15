import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.LinkRecordExtras
import SM.LinkDiagramExtras
import SM.LinkRecordExtension

/-! # Skeleton FINAL — the oriented smoothing `exists_smoothing` / `smoothing_record`
(Chapter-3 representation layer; lane sm-3:1084-1103).  Plan of record 2026-09-13
(work/drafts/smoothing/PLAN_FINAL.md): tag A's splice-model construction with the following
grafts from tag B — the reusable generic-shadow lemmas (§0'), the `[0,1)`-clamp `clampIco`
(fixing A's `origPt`, which clamped at `1/2`), the explicit no-wrap law `cut_val` of the splice
model, and B's record-bridge architecture (a global "smoothed coordinate" `key` on the occurrences
of `D`, the general first-return lemma `firstReturn_no_between`, and the successor law derived once
at the model level from a per-component rotated monotone coordinate, `succ_of_coord`).

Construction (design note, "cut both strands at parameter distance ε before and after the crossing
point, join crosswise"): with `s = D.overStrand x = ⟨i, a⟩`, `t = D.underStrand x = ⟨j, b⟩`,
`p = crossingPoint x`, `τs, τt ∈ (0,1)` the crossing parameters and `es = edge P_i a`,
`et = edge P_j b`, the four new corner points are
`s⁻ = p − ε es`, `s⁺ = p + ε es`, `t⁻ = p − ε et`, `t⁺ = p + ε et`; the smoothing arcs are the
segments `s⁻ → t⁺` and `t⁻ → s⁺`.  Every strand of the smoothed shadow is of one of seven *kinds*
(`StrandKind`): an unchanged old strand, one of the four cut pieces `[tail s, s⁻]`, `[s⁺, head s]`,
`[tail t, t⁻]`, `[t⁺, head t]`, or one of the two arcs.  All geometry (genericity, cleanness of the
disc, the arcs inside the disc, the outside match, the crossing correspondence) is proved once for an
abstract *splice model* (`SpliceModel`: a shadow with a kind map satisfying six index laws); the two
concrete shadows — `mixedShadow` (two components joined into one of `k_i + k_j + 4` vertices) and
`selfShadow` (one component of `k` vertices split into two of `d + 2` and `k − d + 2` vertices) —
are given explicit vertex tuples by `ZMod.val` index arithmetic and are shown to be splice models.

Status: definitions are real; every lemma of the chain is `sorry`; the two goal theorems at the end
are proved from the chain.  Plan: work/drafts/smoothing/PLAN_A.md. -/

namespace SM.Link

open SM

noncomputable section

/-- The first strand of a crossing (the chosen witness of `IsCrossing`). -/
def Shadow.Crossing.fst {Γ : Shadow} (y : Γ.Crossing) : Γ.Strand := Classical.choose y.2

theorem Shadow.Crossing.fst_mem {Γ : Shadow} (y : Γ.Crossing) : y.fst ∈ y.val := by
  obtain ⟨t, hy, -, -⟩ := Classical.choose_spec y.2
  exact (Finset.ext_iff.mp hy _).mpr (Finset.mem_insert_self _ _)

/-- The second strand of a crossing. -/
def Shadow.Crossing.snd {Γ : Shadow} (y : Γ.Crossing) : Γ.Strand := Γ.other y y.fst_mem

theorem Shadow.Crossing.snd_mem {Γ : Shadow} (y : Γ.Crossing) : y.snd ∈ y.val :=
  Γ.other_mem y y.fst_mem

theorem Shadow.Crossing.val_eq {Γ : Shadow} (y : Γ.Crossing) : y.val = {y.fst, y.snd} :=
  Γ.eq_pair_other y y.fst_mem

/-! ## 0'. Reusable lemmas on generic shadows and on the plane (graft from tag B, §0)

Small facts about any generic shadow, stated once here so that the smoothing lane can cite them;
they belong in LinkDiagramExtras when the lane lands. -/

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

/-- Distances along an edge scale with the edge vector. -/
theorem dist_edgePt (s : Γ.Strand) (t t' : ℝ) :
    dist (Γ.edgePt s t) (Γ.edgePt s t') = |t - t'| * ‖Γ.dir s‖ := by
  sorry

/-- Closed edge segments are closed (compact) sets: continuous image of `[0,1]`. -/
theorem isClosed_seg (s : Γ.Strand) : IsClosed (Γ.seg s) := by
  sorry

theorem isCompact_seg (s : Γ.Strand) : IsCompact (Γ.seg s) := by
  sorry

/-- Two consecutive edges of a generic shadow meet only at their common vertex (independent
directions meet once; positively collinear consecutive edges only touch). -/
theorem Generic.seg_inter_succ {Γ : Shadow} (hΓ : Γ.Generic) (u : Γ.Strand) :
    Γ.seg u ∩ Γ.seg ⟨u.1, u.2 + 1⟩ = {Γ.head u} := by
  sorry

/-- The double point of `x` lies on no edge other than the two edges of `x` (a non-adjacent third
edge through it would give a second crossing with the same point, `crossingPoint_injective`; an
adjacent one a vertex on an edge of `x`, `tail_off`, or a triple point, `no_triple`). -/
theorem Generic.crossingPoint_not_mem_seg {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    {t : Γ.Strand} (ht : t ∉ x.val) : Γ.crossingPoint x ∉ Γ.seg t := by
  sorry

/-- The double point is not a vertex. -/
theorem Generic.crossingPoint_ne_tail {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)
    (s : Γ.Strand) : Γ.crossingPoint x ≠ Γ.tail s := by
  sorry

/-- The two edges of a crossing meet exactly in the double point. -/
theorem Generic.seg_inter_seg_eq {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}
    (hs : s ∈ x.val) (ht : t ∈ x.val) (hst : s ≠ t) :
    Γ.seg s ∩ Γ.seg t = {Γ.crossingPoint x} := by
  sorry

/-- The edge parameter of a point of an edge is unique (nonzero edge vector). -/
theorem Generic.edgePt_injective {Γ : Shadow} (hΓ : Γ.Generic) (s : Γ.Strand) :
    Function.Injective (Γ.edgePt s) := by
  sorry

end Shadow

/-- The labels of two non-adjacent edges of a `k`-gon differ by at least `2` in both cyclic
directions. -/
theorem two_le_val_sub_of_not_adjacent {k : ℕ} [NeZero k] {a b : ZMod k} (h : ¬ adjacent a b) :
    2 ≤ (b - a).val ∧ (b - a).val + 2 ≤ k := by
  sorry

/-- Coordinates in a basis `(u, v)` with `det u v ≠ 0` are unique (the form of
`intersection_parameters_unique` used for all geometry inside the disc). -/
theorem coords_unique {u v : Plane} (hd : det u v ≠ 0) {α β α' β' : ℝ}
    (h : α • u + β • v = α' • u + β' • v) : α = α' ∧ β = β' := by
  sorry

/-- A positive rescaling keeps a regular pair regular. -/
theorem regularPair_smul_pos {u v : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)
    (h : RegularPair u v) : RegularPair (l • u) (m • v) := by
  sorry

/-- Two independent vectors form a regular pair. -/
theorem regularPair_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v := by
  sorry

/-- The corners at the cut points: `(l•u, u+v)` and `(u+v, l•v)` are regular when `det u v ≠ 0`. -/
theorem regularPair_add_right_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (l • u) (u + v) := by
  sorry

theorem regularPair_add_left_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :
    RegularPair (u + v) (l • v) := by
  sorry

/-- The traversal coordinate of an occurrence, unfolded: edge label plus crossing parameter. -/
theorem Diagram.visitCoord_eq (D : Diagram) (v : D.Γ.Visit) :
    D.visitCoord v = (v.2.val.2.val : ℝ) + D.crossingParam v.1 v.2.2 := rfl

/-- Clamp a real number into `[0, 1)` (identity on `[0,1)`, junk `0` outside; every use in this
file is on a parameter already in `[0,1)`). -/
def clampIco (t : ℝ) : Set.Ico (0 : ℝ) 1 :=
  if ht : 0 ≤ t ∧ t < 1 then ⟨t, ht⟩ else ⟨0, ⟨le_rfl, zero_lt_one⟩⟩

theorem clampIco_val_of_mem {t : ℝ} (ht : 0 ≤ t ∧ t < 1) : (clampIco t).val = t := by
  simp [clampIco, ht]

theorem clampIco_val_of_mem' (t : Set.Ico (0 : ℝ) 1) : clampIco t.val = t := by
  apply Subtype.ext; exact clampIco_val_of_mem t.2

/-- **The first return of a cyclic-successor permutation is the cyclic successor within `p`**
(graft from tag B, L5.4b).  If `κ` is injective on each cycle of `f` and no element of the cycle
lies strictly between `κ v` and `κ (f v)`, then no `p`-element of the cycle lies strictly between
`κ v` and the key of the first return of `v` to `p`.  Proof: induction on the return time; the
points `f v, …, f^(n-1) v` are exactly the cycle elements strictly between `κ v` and `κ (f^n v)`
(arcs concatenate, `cycBetween` is a case bash with `linarith`), and none of them is in `p`. -/
theorem firstReturn_no_between {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)
    [DecidablePred p] (κ : α → ℝ)
    (hκ : ∀ v u, f.SameCycle u v → κ u = κ v → u = v)
    (hf : ∀ v u, f.SameCycle u v → ¬ cycBetween (κ v) (κ u) (κ (f v)))
    (v : {m // p m}) (u : α) (hu : f.SameCycle u v.1) (hp : p u) :
    ¬ cycBetween (κ v.1) (κ u) (κ (firstReturn f p v).1) := by
  sorry

namespace Smoothing

variable (D : Diagram) (x : D.Γ.Crossing)

/-! ## 0. The crossing data -/

/-- The over strand `s = ⟨i, a⟩` of the smoothed crossing. -/
abbrev sS : D.Γ.Strand := D.overStrand x

/-- The under strand `t = ⟨j, b⟩` of the smoothed crossing. -/
abbrev tS : D.Γ.Strand := D.underStrand x

/-- The double point `p`. -/
abbrev pt : Plane := D.Γ.crossingPoint x

/-- The edge parameter of `p` on `s`. -/
abbrev τs : ℝ := D.crossingParam x (D.over_mem x)

/-- The edge parameter of `p` on `t`. -/
abbrev τt : ℝ := D.crossingParam x (D.under_mem x)

/-- The direction of `s`. -/
abbrev es : Plane := D.Γ.dir (sS D x)

/-- The direction of `t`. -/
abbrev et : Plane := D.Γ.dir (tS D x)

theorem sS_ne_tS : sS D x ≠ tS D x := D.over_ne_under x

theorem not_adjacent_sS_tS : ¬ D.Γ.Adjacent (sS D x) (tS D x) := D.not_adjacent_over_under x

theorem det_es_et_ne_zero : det (es D x) (et D x) ≠ 0 := D.det_over_under_ne_zero x

theorem es_ne_zero : es D x ≠ 0 := D.Γ.edge_ne_zero D.generic _

theorem et_ne_zero : et D x ≠ 0 := D.Γ.edge_ne_zero D.generic _

theorem τs_pos : 0 < τs D x := D.crossingParam_pos x _
theorem τs_lt_one : τs D x < 1 := D.crossingParam_lt_one x _
theorem τt_pos : 0 < τt D x := D.crossingParam_pos x _
theorem τt_lt_one : τt D x < 1 := D.crossingParam_lt_one x _

theorem pt_eq_s : pt D x = D.Γ.tail (sS D x) + τs D x • es D x :=
  (D.crossingParam_spec x (D.over_mem x)).2.2

theorem pt_eq_t : pt D x = D.Γ.tail (tS D x) + τt D x • et D x :=
  (D.crossingParam_spec x (D.under_mem x)).2.2

/-! ## 1. The clearance radius `r₁`

`r₁` is the least distance from `p` to a closed edge segment of a strand other than `s`, `t`.  It is
positive because (`crossingPoint_not_mem_seg_other`) no third strand passes through `p`: a
non-adjacent third strand through `p` would give a second crossing with the same double point
(`Generic.crossingPoint_injective`), an adjacent one would put a vertex on `s` or `t` (`tail_off`)
or a triple point (`no_triple`). -/

/-- The strands other than `s` and `t`. -/
def others : Finset D.Γ.Strand :=
  Finset.univ.filter (fun e => e ≠ sS D x ∧ e ≠ tS D x)

theorem mem_others (e : D.Γ.Strand) : e ∈ others D x ↔ e ≠ sS D x ∧ e ≠ tS D x := by
  simp [others]

/-- The strand preceding `s` on its component is neither `s` nor `t`. -/
theorem others_nonempty : (others D x).Nonempty := by
  sorry

/-- **Key clearance lemma**: no strand other than `s`, `t` passes through the double point. -/
theorem crossingPoint_not_mem_seg_other (e : D.Γ.Strand) (hs : e ≠ sS D x) (ht : e ≠ tS D x) :
    pt D x ∉ D.Γ.seg e := by
  sorry

/-- The clearance radius: the least distance from `p` to a strand other than `s`, `t`. -/
def r₁ : ℝ :=
  (others D x).inf' (others_nonempty D x) (fun e => Metric.infDist (pt D x) (D.Γ.seg e))

theorem r₁_pos : 0 < r₁ D x := by
  sorry

theorem r₁_le_dist {e : D.Γ.Strand} (hs : e ≠ sS D x) (ht : e ≠ tS D x) {q : Plane}
    (hq : q ∈ D.Γ.seg e) : r₁ D x ≤ dist (pt D x) q := by
  sorry

/-- Every vertex of `D` lies on a strand other than `s`, `t` (a vertex of `s` lies on `s ∓ 1`),
hence at distance `≥ r₁` from `p`. -/
theorem r₁_le_dist_tail (e : D.Γ.Strand) : r₁ D x ≤ dist (pt D x) (D.Γ.tail e) := by
  sorry

/-- Every other crossing point is at distance `≥ r₁` from `p` (one of its strands is not `s`,`t`). -/
theorem r₁_le_dist_crossingPoint {y : D.Γ.Crossing} (hy : y ≠ x) :
    r₁ D x ≤ dist (pt D x) (D.Γ.crossingPoint y) := by
  sorry

theorem r₁_le_τs_mul : r₁ D x ≤ τs D x * ‖es D x‖ := by
  sorry
theorem r₁_le_one_sub_τs_mul : r₁ D x ≤ (1 - τs D x) * ‖es D x‖ := by
  sorry
theorem r₁_le_τt_mul : r₁ D x ≤ τt D x * ‖et D x‖ := by
  sorry
theorem r₁_le_one_sub_τt_mul : r₁ D x ≤ (1 - τt D x) * ‖et D x‖ := by
  sorry

/-! ## 2. Admissible cut parameters `ε` -/

/-- The constraints on the cut parameter: the cut points stay inside the open edges and inside the
clearance ball. -/
structure SmallEps (ε : ℝ) : Prop where
  pos : 0 < ε
  lt_τs : ε < τs D x
  lt_one_sub_τs : ε < 1 - τs D x
  lt_τt : ε < τt D x
  lt_one_sub_τt : ε < 1 - τt D x
  mul_es_lt : ε * ‖es D x‖ < r₁ D x
  mul_et_lt : ε * ‖et D x‖ < r₁ D x

/-- An explicit admissible cut parameter: half the minimum of the six bounds. -/
def eps : ℝ :=
  min (min (min (τs D x) (1 - τs D x)) (min (τt D x) (1 - τt D x)))
    (min (r₁ D x / ‖es D x‖) (r₁ D x / ‖et D x‖)) / 2

theorem eps_small : SmallEps D x (eps D x) := by
  sorry

/-- No other occurrence on `s` lies within parameter distance `ε` of the double point (its crossing
point is at distance `≥ r₁ > ε‖es‖` from `p`, `r₁_le_dist_crossingPoint`); the analogue of tag B's
`Small.ε_vis_o`.  Used to place the passage of every other crossing on the right cut piece. -/
theorem crossingParam_far_s {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = sS D x)
    (hne : w.1 ≠ x) : ε < |D.crossingParam w.1 w.2.2 - τs D x| := by
  sorry

theorem crossingParam_far_t {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = tS D x)
    (hne : w.1 ≠ x) : ε < |D.crossingParam w.1 w.2.2 - τt D x| := by
  sorry

/-! ## 3. The four new corner points and the smoothing arcs -/

variable (ε : ℝ)

/-- `s⁻ = p − ε es`: the cut point on `s` before the crossing. -/
def sMinus : Plane := pt D x - ε • es D x
/-- `s⁺ = p + ε es`. -/
def sPlus : Plane := pt D x + ε • es D x
/-- `t⁻ = p − ε et`. -/
def tMinus : Plane := pt D x - ε • et D x
/-- `t⁺ = p + ε et`. -/
def tPlus : Plane := pt D x + ε • et D x

theorem sMinus_eq_edgePoint : sMinus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x - ε) := by
  sorry
theorem sPlus_eq_edgePoint : sPlus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x + ε) := by
  sorry
theorem tMinus_eq_edgePoint : tMinus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x - ε) := by
  sorry
theorem tPlus_eq_edgePoint : tPlus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x + ε) := by
  sorry

/-- Distance of the cut points from `p`. -/
theorem dist_sMinus : dist (sMinus D x ε) (pt D x) = |ε| * ‖es D x‖ := by
  sorry

/-! ## 4. Strand kinds and the abstract splice model

The seven kinds of strands of a smoothed shadow.  `kindTail`, `kindDir` give the tail vertex and
the direction of a kind; `kindPred` is the kind of the preceding strand on the same component
(the reconnection is visible here: the successor of `cutStartS` is `arcST`, whose successor is
`cutEndT`).  `kindOrig` is the strand of `D` a kind is a piece of (arcs are assigned `s`; never
used for arcs). -/

inductive StrandKind (D : Diagram) (x : D.Γ.Crossing)
  | old (e : D.Γ.Strand)
  | cutStartS | cutEndS | cutStartT | cutEndT
  | arcST | arcTS
  deriving DecidableEq

namespace StrandKind

variable {D x}

/-- Tail vertex of a kind. -/
def tail (ε : ℝ) : StrandKind D x → Plane
  | old e => D.Γ.tail e
  | cutStartS => D.Γ.tail (sS D x)
  | cutEndS => sPlus D x ε
  | cutStartT => D.Γ.tail (tS D x)
  | cutEndT => tPlus D x ε
  | arcST => sMinus D x ε
  | arcTS => tMinus D x ε

/-- Direction of a kind. -/
def dir (ε : ℝ) : StrandKind D x → Plane
  | old e => D.Γ.dir e
  | cutStartS => (τs D x - ε) • es D x
  | cutEndS => (1 - τs D x - ε) • es D x
  | cutStartT => (τt D x - ε) • et D x
  | cutEndT => (1 - τt D x - ε) • et D x
  | arcST => ε • (es D x + et D x)
  | arcTS => ε • (es D x + et D x)

/-- Head vertex of a kind. -/
def head (ε : ℝ) (κ : StrandKind D x) : Plane := κ.tail ε + κ.dir ε

/-- Closed segment of a kind. -/
def seg (ε : ℝ) (κ : StrandKind D x) : Set Plane :=
  {q | ∃ θ : ℝ, 0 ≤ θ ∧ θ ≤ 1 ∧ q = κ.tail ε + θ • κ.dir ε}

/-- Open segment of a kind. -/
def interior (ε : ℝ) (κ : StrandKind D x) : Set Plane :=
  {q | ∃ θ : ℝ, 0 < θ ∧ θ < 1 ∧ q = κ.tail ε + θ • κ.dir ε}

/-- The strand of `D` a kind is a piece of. -/
def orig : StrandKind D x → D.Γ.Strand
  | old e => e
  | cutStartS => sS D x
  | cutEndS => sS D x
  | cutStartT => tS D x
  | cutEndT => tS D x
  | arcST => sS D x
  | arcTS => tS D x

/-- The kind of the strand preceding a strand of the given kind on its component. -/
def pred : StrandKind D x → StrandKind D x
  | old e =>
      if e = ⟨(sS D x).1, (sS D x).2 + 1⟩ then cutEndS
      else if e = ⟨(tS D x).1, (tS D x).2 + 1⟩ then cutEndT
      else old ⟨e.1, e.2 - 1⟩
  | cutStartS => old ⟨(sS D x).1, (sS D x).2 - 1⟩
  | cutEndS => arcTS
  | cutStartT => old ⟨(tS D x).1, (tS D x).2 - 1⟩
  | cutEndT => arcST
  | arcST => cutStartS
  | arcTS => cutStartT

/-- The kind of the strand following a strand of the given kind on its component. -/
def succ : StrandKind D x → StrandKind D x
  | old e =>
      if e = ⟨(sS D x).1, (sS D x).2 - 1⟩ then cutStartS
      else if e = ⟨(tS D x).1, (tS D x).2 - 1⟩ then cutStartT
      else old ⟨e.1, e.2 + 1⟩
  | cutStartS => arcST
  | cutEndS => old ⟨(sS D x).1, (sS D x).2 + 1⟩
  | cutStartT => arcTS
  | cutEndT => old ⟨(tS D x).1, (tS D x).2 + 1⟩
  | arcST => cutEndT
  | arcTS => cutEndS

/-- The kinds that occur in a smoothed shadow: everything except the two erased strands. -/
def Occurs (κ : StrandKind D x) : Prop := κ ≠ old (sS D x) ∧ κ ≠ old (tS D x)

theorem occurs_cutStartS : (cutStartS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutEndS : (cutEndS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutStartT : (cutStartT : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_cutEndT : (cutEndT : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_arcST : (arcST : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_arcTS : (arcTS : StrandKind D x).Occurs := ⟨(fun h => nomatch h), (fun h => nomatch h)⟩
theorem occurs_old {e : D.Γ.Strand} (hs : e ≠ sS D x) (ht : e ≠ tS D x) : (old e : StrandKind D x).Occurs :=
  ⟨fun h => hs (StrandKind.old.inj h), fun h => ht (StrandKind.old.inj h)⟩

/-- The kind of the crossing parameter: the parameter on the original strand of a point at
parameter `θ` of a kind (identity on old strands, affine rescaling on the cut pieces). -/
def origParam (ε : ℝ) : StrandKind D x → ℝ → ℝ
  | old _ => fun θ => θ
  | cutStartS => fun θ => θ * (τs D x - ε)
  | cutEndS => fun θ => τs D x + ε + θ * (1 - τs D x - ε)
  | cutStartT => fun θ => θ * (τt D x - ε)
  | cutEndT => fun θ => τt D x + ε + θ * (1 - τt D x - ε)
  | arcST => fun _ => τs D x
  | arcTS => fun _ => τt D x

/-- The inverse rescaling: the parameter on the cut piece of a point at parameter `θ` of the
original strand. -/
def liftParam (ε : ℝ) : StrandKind D x → ℝ → ℝ
  | old _ => fun θ => θ
  | cutStartS => fun θ => θ / (τs D x - ε)
  | cutEndS => fun θ => (θ - τs D x - ε) / (1 - τs D x - ε)
  | cutStartT => fun θ => θ / (τt D x - ε)
  | cutEndT => fun θ => (θ - τt D x - ε) / (1 - τt D x - ε)
  | arcST => fun θ => θ
  | arcTS => fun θ => θ

/-- Adjacency of kinds: same kind, or successor/predecessor. -/
def Adj (κ κ' : StrandKind D x) : Prop := κ' = κ ∨ κ' = κ.succ ∨ κ' = κ.pred

/-- The tail vertex of a kind is an endpoint of another kind: the kind itself or its predecessor. -/
def Incident (κ κ' : StrandKind D x) : Prop := κ' = κ ∨ κ' = κ.pred

theorem pred_succ (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.pred = κ := by
  sorry

theorem succ_pred (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.succ = κ := by
  sorry

theorem succ_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.Occurs := by
  sorry

theorem pred_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.Occurs := by
  sorry

/-- Consecutive kinds fit: the head of a kind is the tail of its successor. -/
theorem head_eq_tail_succ (ε : ℝ) (κ : StrandKind D x) (hκ : κ.Occurs) :
    κ.head ε = κ.succ.tail ε := by
  sorry

/-- Every point of a kind lies on its original strand at the rescaled parameter (cut pieces and
old strands). -/
theorem tail_add_smul_dir (ε : ℝ) (κ : StrandKind D x) (hκ : κ ≠ arcST) (hκ' : κ ≠ arcTS) (θ : ℝ) :
    κ.tail ε + θ • κ.dir ε = edgePoint (D.Γ.comp κ.orig.1).P κ.orig.2 (κ.origParam ε θ) := by
  sorry

theorem seg_subset_seg_orig (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) : κ.seg ε ⊆ D.Γ.seg κ.orig := by
  sorry

theorem seg_old (ε : ℝ) (e : D.Γ.Strand) : (old e : StrandKind D x).seg ε = D.Γ.seg e := by
  sorry

theorem interior_old (ε : ℝ) (e : D.Γ.Strand) :
    (old e : StrandKind D x).interior ε = D.Γ.interior e := by
  sorry

/-- The arcs lie in the open ball of radius `ε · max(‖es‖, ‖et‖) < r₁` about `p`. -/
theorem seg_arc_subset_ball (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)
    (hκ : κ = arcST ∨ κ = arcTS) :
    κ.seg ε ⊆ Metric.ball (pt D x) (max (ε * ‖es D x‖) (ε * ‖et D x‖)) := by
  sorry

/-- The cut points are inside the clearance ball, so the cut pieces reach the ball's boundary. -/
theorem dist_cut_lt (ε : ℝ) (hε : SmallEps D x ε) :
    dist (sMinus D x ε) (pt D x) < r₁ D x ∧ dist (sPlus D x ε) (pt D x) < r₁ D x ∧
      dist (tMinus D x ε) (pt D x) < r₁ D x ∧ dist (tPlus D x ε) (pt D x) < r₁ D x := by
  sorry

end StrandKind

/-- **The abstract splice model.**  A shadow `Γ₀` together with a kind map on its strands that is a
bijection onto the occurring kinds and respects tails, directions and the cyclic predecessor.  All
geometric statements about the smoothing are proved for an arbitrary splice model; the concrete
shadows `mixedShadow` / `selfShadow` are shown to be models by index arithmetic. -/
structure SpliceModel (ε : ℝ) (Γ₀ : Shadow) where
  /-- the kind of every strand -/
  kind : Γ₀.Strand → StrandKind D x
  kind_injective : Function.Injective kind
  /-- every occurring kind is realised -/
  kind_surj : ∀ κ : StrandKind D x, κ.Occurs → ∃ u, kind u = κ
  /-- the erased strands do not occur -/
  kind_occurs : ∀ u, (kind u).Occurs
  /-- the predecessor law (encodes the reconnection and all adjacency) -/
  kind_pred : ∀ u : Γ₀.Strand, kind ⟨u.1, u.2 - 1⟩ = (kind u).pred
  tail_eq : ∀ u, Γ₀.tail u = (kind u).tail ε
  dir_eq : ∀ u, Γ₀.dir u = (kind u).dir ε
  /-- the no-wrap law: a cut-start piece, the arc after it and the cut-end piece after that occupy
  three consecutive labels `m, m+1, m+2` without passing label `0` (so the smoothing arcs of `D₀`
  need no wrap-around case, `traversalBetween_span_two`).  Not derivable from the other laws;
  trivial index arithmetic in both concrete models. -/
  cut_val : ∀ u : Γ₀.Strand, (kind u = StrandKind.cutStartS ∨ kind u = StrandKind.cutStartT) →
    u.2.val + 2 < (Γ₀.comp u.1).k

namespace SpliceModel

variable {D x ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀)

/-- The strand of a given occurring kind. -/
def strandOf (κ : StrandKind D x) (hκ : κ.Occurs) : Γ₀.Strand :=
  Classical.choose (M.kind_surj κ hκ)

@[simp] theorem kind_strandOf (κ : StrandKind D x) (hκ : κ.Occurs) : M.kind (M.strandOf κ hκ) = κ :=
  Classical.choose_spec (M.kind_surj κ hκ)

theorem strandOf_kind (u : Γ₀.Strand) : M.strandOf (M.kind u) (M.kind_occurs u) = u :=
  M.kind_injective (M.kind_strandOf _ _)

/-- The original strand of `D` a strand of `Γ₀` is a piece of. -/
def orig (u : Γ₀.Strand) : D.Γ.Strand := (M.kind u).orig

theorem kind_succ (u : Γ₀.Strand) : M.kind ⟨u.1, u.2 + 1⟩ = (M.kind u).succ := by
  sorry

theorem seg_eq (u : Γ₀.Strand) : Γ₀.seg u = (M.kind u).seg ε := by
  sorry

theorem interior_eq (u : Γ₀.Strand) : Γ₀.interior u = (M.kind u).interior ε := by
  sorry

theorem head_eq (u : Γ₀.Strand) : Γ₀.head u = (M.kind u).head ε := by
  sorry

/-- Adjacency in `Γ₀` is adjacency of kinds. -/
theorem adjacent_iff (u u' : Γ₀.Strand) : Γ₀.Adjacent u u' ↔ (M.kind u).Adj (M.kind u') := by
  sorry

theorem incidentTail_iff (u u' : Γ₀.Strand) :
    Γ₀.IncidentTail u u' ↔ (M.kind u).Incident (M.kind u') := by
  sorry

/-- Adjacency of old strands is inherited. -/
theorem adjacent_old_iff (e e' : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)
    (he' : e' ≠ sS D x ∧ e' ≠ tS D x) :
    (StrandKind.old e : StrandKind D x).Adj (StrandKind.old e') ↔ D.Γ.Adjacent e e' := by
  sorry

/-- The evaluation of a traversal point of `Γ₀`, through its kind. -/
theorem eval_eq (q : Γ₀.Pt) :
    Γ₀.eval q = (M.kind ⟨q.1, q.2.1⟩).tail ε + q.2.2.val • (M.kind ⟨q.1, q.2.1⟩).dir ε := by
  sorry

end SpliceModel

/-! ## 5. The disc and the trace of `D` inside it

The disc is `U = closedBall p r` with `r = discRadius`, strictly between `ε · max(‖es‖,‖et‖)` (so
the cut points and both arcs are inside the open ball) and `r₁` (so no other strand, vertex or
crossing point of `D` meets the closed ball). -/

/-- The disc radius: the midpoint between the arc radius and the clearance radius. -/
def discRadius : ℝ := (max (ε * ‖es D x‖) (ε * ‖et D x‖) + r₁ D x) / 2

/-- The smoothing disc `U` (a closed ball of the sup metric of `ℝ × ℝ`, an axis-parallel square). -/
def disc : Set Plane := Metric.closedBall (pt D x) (discRadius D x ε)

theorem discRadius_pos (hε : SmallEps D x ε) : 0 < discRadius D x ε := by
  sorry

theorem discRadius_lt_r₁ (hε : SmallEps D x ε) : discRadius D x ε < r₁ D x := by
  sorry

theorem arc_lt_discRadius (hε : SmallEps D x ε) :
    max (ε * ‖es D x‖) (ε * ‖et D x‖) < discRadius D x ε := by
  sorry

theorem isDisc_disc (hε : SmallEps D x ε) : IsDisc (disc D x ε) :=
  isDisc_closedBall _ (discRadius_pos D x ε hε)

theorem interior_disc (hε : SmallEps D x ε) :
    interior (disc D x ε) = Metric.ball (pt D x) (discRadius D x ε) :=
  interior_closedBall _ (discRadius_pos D x ε hε).ne'

theorem frontier_disc (hε : SmallEps D x ε) :
    frontier (disc D x ε) = Metric.sphere (pt D x) (discRadius D x ε) :=
  frontier_closedBall _ (discRadius_pos D x ε hε).ne'

/-- The trace of `D` inside the closed disc lies on `s ∪ t`. -/
theorem mem_seg_of_mem_disc (hε : SmallEps D x ε) {e : D.Γ.Strand} {q : Plane} (hq : q ∈ D.Γ.seg e)
    (hU : q ∈ disc D x ε) : e = sS D x ∨ e = tS D x := by
  sorry

/-- No crossing point of `D` other than `p` lies in the closed disc. -/
theorem crossingPoint_ne_not_mem_disc (hε : SmallEps D x ε) {y : D.Γ.Crossing} (hy : y ≠ x) :
    D.Γ.crossingPoint y ∉ disc D x ε := by
  sorry

/-- No vertex of `D` lies in the closed disc. -/
theorem tail_not_mem_disc (hε : SmallEps D x ε) (e : D.Γ.Strand) : D.Γ.tail e ∉ disc D x ε := by
  sorry

/-- The frontier parameters of `s` and `t`: the entering and exiting parameters of the two strands
through the square `U` are `τ ∓ r/‖e‖`. -/
def θsIn : ℝ := τs D x - discRadius D x ε / ‖es D x‖
def θsOut : ℝ := τs D x + discRadius D x ε / ‖es D x‖
def θtIn : ℝ := τt D x - discRadius D x ε / ‖et D x‖
def θtOut : ℝ := τt D x + discRadius D x ε / ‖et D x‖

theorem θsIn_pos (hε : SmallEps D x ε) : 0 < θsIn D x ε := by
  sorry
theorem θsOut_lt_one (hε : SmallEps D x ε) : θsOut D x ε < 1 := by
  sorry
theorem θtIn_pos (hε : SmallEps D x ε) : 0 < θtIn D x ε := by
  sorry
theorem θtOut_lt_one (hε : SmallEps D x ε) : θtOut D x ε < 1 := by
  sorry
theorem θsIn_lt_θsOut (hε : SmallEps D x ε) : θsIn D x ε < θsOut D x ε := by
  sorry
theorem θtIn_lt_θtOut (hε : SmallEps D x ε) : θtIn D x ε < θtOut D x ε := by
  sorry

/-- The cut parameters lie strictly inside the frontier parameters:
`θsIn < τs − ε < τs + ε < θsOut` (the cut points are inside the open disc). -/
theorem θsIn_lt_cut (hε : SmallEps D x ε) : θsIn D x ε < τs D x - ε ∧ τs D x + ε < θsOut D x ε := by
  sorry
theorem θtIn_lt_cut (hε : SmallEps D x ε) : θtIn D x ε < τt D x - ε ∧ τt D x + ε < θtOut D x ε := by
  sorry

/-- A point of `s` is in the closed (open) disc iff its parameter lies in `[θsIn, θsOut]`
(`(θsIn, θsOut)`). -/
theorem edgePoint_s_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ disc D x ε ↔
      θsIn D x ε ≤ θ ∧ θ ≤ θsOut D x ε := by
  sorry

theorem edgePoint_s_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θsIn D x ε < θ ∧ θ < θsOut D x ε := by
  sorry

theorem edgePoint_t_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ disc D x ε ↔
      θtIn D x ε ≤ θ ∧ θ ≤ θtOut D x ε := by
  sorry

theorem edgePoint_t_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔
      θtIn D x ε < θ ∧ θ < θtOut D x ε := by
  sorry

/-- The frontier parameters on the cut pieces of `Γ₀` (rescaled frontier parameters of `D`). -/
def θ₀sIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartS (θsIn D x ε)
def θ₀sOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndS (θsOut D x ε)
def θ₀tIn : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutStartT (θtIn D x ε)
def θ₀tOut : ℝ := StrandKind.liftParam (D := D) (x := x) ε StrandKind.cutEndT (θtOut D x ε)

theorem θ₀_mem (hε : SmallEps D x ε) : θ₀sIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀sOut D x ε ∈ Set.Ico (0:ℝ) 1 ∧
    θ₀tIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀tOut D x ε ∈ Set.Ico (0:ℝ) 1 := by
  sorry

/-- Traversal betweenness on one edge: the points strictly between two points of the same edge in
the cyclic order are the points of that edge with parameter strictly between (accepted
`traversalBetween`, key form). -/
theorem traversalBetween_same_edge {n : ℕ} [NeZero n] (a : ZMod n) (θ₁ θ₂ : Set.Ico (0:ℝ) 1)
    (h : θ₁.val < θ₂.val) (r : TraversalPoint n) :
    traversalBetween (a, θ₁) r (a, θ₂) ↔ r.1 = a ∧ θ₁.val < r.2.val ∧ r.2.val < θ₂.val := by
  sorry

/-- Traversal betweenness across two consecutive edges `m`, `m+2` (used for the smoothing arcs of
`D₀`: start on the cut piece, through the arc, stop on the next cut piece; no wrap). -/
theorem traversalBetween_span_two {n : ℕ} [NeZero n] (m : ZMod n) (hm : m.val + 2 < n)
    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :
    traversalBetween (m, θ₁) r (m + 2, θ₂) ↔
      (r.1 = m ∧ θ₁.val < r.2.val) ∨ r.1 = m + 1 ∨ (r.1 = m + 2 ∧ r.2.val < θ₂.val) := by
  sorry

section DiscD

variable {ε} (hε : SmallEps D x ε)
include hε

theorem clean_D : Clean (disc D x ε) D := by
  sorry

theorem center_mem : pt D x ∈ interior (disc D x ε) := by
  sorry

/-- The arc of `D` through the over occurrence: on `s`, from parameter `θsIn` to `θsOut`. -/
def arcS : D.Γ.Arc :=
  ⟨(sS D x).1,
    ((sS D x).2, ⟨θsIn D x ε, (θsIn_pos D x ε hε).le,
      (θsIn_lt_θsOut D x ε hε).trans (θsOut_lt_one D x ε hε)⟩),
    ((sS D x).2, ⟨θsOut D x ε, ((θsIn_pos D x ε hε).trans (θsIn_lt_θsOut D x ε hε)).le,
      θsOut_lt_one D x ε hε⟩)⟩

/-- The arc of `D` through the under occurrence: on `t`, from `θtIn` to `θtOut`. -/
def arcT : D.Γ.Arc :=
  ⟨(tS D x).1,
    ((tS D x).2, ⟨θtIn D x ε, (θtIn_pos D x ε hε).le,
      (θtIn_lt_θtOut D x ε hε).trans (θtOut_lt_one D x ε hε)⟩),
    ((tS D x).2, ⟨θtOut D x ε, ((θtIn_pos D x ε hε).trans (θtIn_lt_θtOut D x ε hε)).le,
      θtOut_lt_one D x ε hε⟩)⟩

theorem arcS_ne_arcT : arcS D x hε ≠ arcT D x hε := by
  sorry

theorem arcCover_D : D.Γ.ArcCover (disc D x ε) {arcS D x hε, arcT D x hε} := by
  sorry

theorem overOn_arcS : D.OverOn (arcS D x hε) x := by
  sorry

theorem underOn_arcT : D.UnderOn (arcT D x hε) x := by
  sorry

theorem inner_iff_D (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∈ interior (disc D x ε) ↔ y = x := by
  sorry

end DiscD

/-! ## 6. Model-level geometry

Everything in this section is stated for an arbitrary splice model `M : SpliceModel D x ε Γ₀` with
`hε : SmallEps D x ε`. -/

section Model

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-! ### 6a. Genericity of the spliced shadow -/

omit M in
/-- Non-adjacent kinds that are not both old have disjoint segments, except an old strand meeting a
cut piece at a crossing of `D` (cut pieces of one strand are disjoint; cut pieces of `s` and `t`
are disjoint since their only common point `p` is cut away; arcs are disjoint from each other and
from the cut pieces they are not adjacent to, by independence of `es`, `et`; arcs are disjoint from
old strands by the clearance radius). -/
theorem kind_disjoint (κ κ' : StrandKind D x) (hκ : ¬ ∃ e, κ = StrandKind.old e)
    (hadj : ¬ κ.Adj κ') (hold : ∀ e, κ' = StrandKind.old e → False) :
    Disjoint (κ.seg ε) (κ'.seg ε) := by
  sorry

omit M in
/-- A cut piece meets an old strand `e ≠ s, t` only if `e` is non-adjacent to the original strand
(so the meeting is a crossing of `D`); adjacent old strands `s ∓ 1` meet only the piece they touch,
at the common vertex. -/
theorem cut_inter_old (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS)
    (hκo : ¬ ∃ e, κ = StrandKind.old e) (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)
    (hmeet : (κ.seg ε ∩ D.Γ.seg e).Nonempty) (hadj : ¬ κ.Adj (StrandKind.old e)) :
    ¬ D.Γ.Adjacent κ.orig e := by
  sorry

/-- Every component of `Γ₀` is a regular polygon: old corners are inherited, the corners at the
cut points are positively collinear, the corners at the arc ends are transverse
(`det es et ≠ 0`). -/
theorem regular (i : Fin Γ₀.c) : Regular (Γ₀.comp i).P := by
  sorry

theorem tail_off (u u' : Γ₀.Strand) (h : ¬ Γ₀.IncidentTail u u') : Γ₀.tail u ∉ Γ₀.seg u' := by
  sorry

theorem transverse (u u' : Γ₀.Strand) (h : ¬ Γ₀.Adjacent u u')
    (hmeet : (Γ₀.seg u ∩ Γ₀.seg u').Nonempty) : det (Γ₀.dir u) (Γ₀.dir u') ≠ 0 := by
  sorry

theorem no_triple : ¬ ∃ u u' u'' : Γ₀.Strand, u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧
    (Γ₀.interior u ∩ Γ₀.interior u' ∩ Γ₀.interior u'').Nonempty := by
  sorry

/-- **Genericity of the spliced shadow.** -/
theorem generic : Γ₀.Generic where
  regular := regular D x M hε
  tail_off := tail_off D x M hε
  transverse := transverse D x M hε
  no_triple := no_triple D x M hε

/-! ### 6b. Crossings of the spliced shadow -/

/-- A crossing of `Γ₀` consists of two strands whose original strands form a crossing of `D`
other than `x` (cut pieces meet nothing but old strands; arcs meet nothing). -/
theorem isCrossing_orig {u u' : Γ₀.Strand} (h : Γ₀.IsCrossing {u, u'}) :
    D.Γ.IsCrossing {M.orig u, M.orig u'} ∧ ({M.orig u, M.orig u'} : Finset D.Γ.Strand) ≠ x.val := by
  sorry

/-- The crossing of `D` under a crossing of `Γ₀`. -/
def origCrossing (y : Γ₀.Crossing) : D.Γ.Crossing :=
  ⟨{M.orig y.fst, M.orig y.snd}, (isCrossing_orig D x M hε (y.val_eq ▸ y.2)).1⟩

theorem origCrossing_ne (y : Γ₀.Crossing) : origCrossing D x M hε y ≠ x := by
  sorry

theorem orig_mem_origCrossing {y : Γ₀.Crossing} {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.orig u ∈ (origCrossing D x M hε y).val := by
  sorry

theorem origCrossing_injective : Function.Injective (origCrossing D x M hε) := by
  sorry

/-- The crossing point of `Γ₀` at `y` is the crossing point of `D` at `origCrossing y`. -/
theorem crossingPoint_origCrossing (y : Γ₀.Crossing) :
    Γ₀.crossingPoint y = D.Γ.crossingPoint (origCrossing D x M hε y) := by
  sorry

omit hε in
/-- The strand of `Γ₀` carrying the passage of the strand `e ∈ y` of `D` through the crossing
`y ≠ x`: the old strand, or the cut piece of `s` (`t`) containing the crossing point. -/
def liftStrand (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) : Γ₀.Strand :=
  if hs : e = sS D x then
    (if D.crossingParam y he < τs D x then M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
     else M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS)
  else if ht : e = tS D x then
    (if D.crossingParam y he < τt D x then M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
     else M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT)
  else M.strandOf (StrandKind.old e) (StrandKind.occurs_old hs ht)

omit hε in
theorem orig_liftStrand (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) :
    M.orig (liftStrand D x M y e he) = e := by
  sorry

/-- Every crossing of `D` other than `x` lifts to a crossing of `Γ₀`. -/
theorem isCrossing_lift {y : D.Γ.Crossing} (hy : y ≠ x) :
    Γ₀.IsCrossing {liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem} := by
  sorry

/-- The lift of a crossing `y ≠ x`. -/
def liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) : Γ₀.Crossing :=
  ⟨_, isCrossing_lift D x M hε hy⟩

theorem origCrossing_liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) :
    origCrossing D x M hε (liftCrossing D x M hε y hy) = y := by
  sorry

theorem liftCrossing_origCrossing (y : Γ₀.Crossing) :
    liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y) = y := by
  sorry

/-- The crossings of `Γ₀` are the crossings of `D` other than `x`. -/
def crossingEquiv : Γ₀.Crossing ≃ {y : D.Γ.Crossing // y ≠ x} where
  toFun y := ⟨origCrossing D x M hε y, origCrossing_ne D x M hε y⟩
  invFun y := liftCrossing D x M hε y.1 y.2
  left_inv y := liftCrossing_origCrossing D x M hε y
  right_inv y := Subtype.ext (origCrossing_liftCrossing D x M hε y.1 y.2)

/-- The strands of a crossing of `Γ₀` lie over distinct strands of the original crossing. -/
theorem orig_injOn_crossing (y : Γ₀.Crossing) {u u' : Γ₀.Strand} (hu : u ∈ y.val) (hu' : u' ∈ y.val)
    (h : M.orig u = M.orig u') : u = u' := by
  sorry

/-! ### 6c. The smoothed diagram: over data pulled back through `orig` -/

/-- The over strand of the smoothed diagram at `y`: the strand of `y` lying over the over strand of
`D` at the original crossing. -/
def overStrand₀ (y : Γ₀.Crossing) : Γ₀.Strand :=
  if M.orig y.fst = D.overStrand (origCrossing D x M hε y) then y.fst else y.snd

theorem overStrand₀_mem (y : Γ₀.Crossing) : overStrand₀ D x M hε y ∈ y.val := by
  unfold overStrand₀
  split_ifs
  · exact y.fst_mem
  · exact y.snd_mem

theorem orig_overStrand₀ (y : Γ₀.Crossing) :
    M.orig (overStrand₀ D x M hε y) = D.overStrand (origCrossing D x M hε y) := by
  sorry

/-- **The smoothed diagram** on a splice model. -/
def toDiagram : Diagram where
  Γ := Γ₀
  generic := generic D x M hε
  overStrand := overStrand₀ D x M hε
  over_mem := overStrand₀_mem D x M hε

@[simp] theorem toDiagram_Γ : (toDiagram D x M hε).Γ = Γ₀ := rfl

theorem toDiagram_underStrand_orig (y : Γ₀.Crossing) :
    M.orig ((toDiagram D x M hε).underStrand y) = D.underStrand (origCrossing D x M hε y) := by
  sorry

/-- Signs are inherited (directions of cut pieces are positive multiples of the originals). -/
theorem toDiagram_sign (y : Γ₀.Crossing) :
    (toDiagram D x M hε).sign y = D.sign (origCrossing D x M hε y) := by
  sorry

/-- The crossing parameter of a strand of `Γ₀` through `y` is the rescaled parameter of `D`. -/
theorem crossingParam_toDiagram (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    (toDiagram D x M hε).crossingParam y hu =
      (M.kind u).liftParam ε (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
  sorry

/-! ### 6d. Cleanness of `D₀` and its two arcs inside the disc -/

/-- No crossing point of `Γ₀` lies in the closed disc. -/
theorem crossingPoint_not_mem_disc (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ disc D x ε := by
  rw [crossingPoint_origCrossing D x M hε y]
  exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)

theorem no_inner_toDiagram (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ interior (disc D x ε) :=
  fun h => crossingPoint_not_mem_disc D x M hε y (interior_subset h)

theorem clean_toDiagram : Clean (disc D x ε) (toDiagram D x M hε) := by
  sorry

theorem localFrame : LocalFrame (disc D x ε) D (toDiagram D x M hε) where
  disc := isDisc_disc D x ε hε
  clean := clean_D D x hε
  clean' := clean_toDiagram D x M hε

/-- The smoothing arc `a₀` of `D₀`: from the frontier point on `[tail s, s⁻]`, along `s⁻ → t⁺`, to
the frontier point on `[t⁺, head t]` (two strands later on the same component). -/
def arcST₀ : Γ₀.Arc :=
  ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
    ((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2, ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩),
    ((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2, ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩)⟩

/-- The smoothing arc `b₀` of `D₀`: from the frontier point on `[tail t, t⁻]`, along `t⁻ → s⁺`, to
the frontier point on `[s⁺, head s]`. -/
def arcTS₀ : Γ₀.Arc :=
  ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
    ((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2, ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩),
    ((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2, ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩)⟩

omit hε in
/-- The strand two steps after `cutStartS` is `cutEndT` (through `arcST`), on the same component
(from `kind_pred`/`kind_succ`). -/
theorem strandOf_cutEndT_eq :
    M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT =
      ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ := by
  sorry

omit hε in
theorem strandOf_cutEndS_eq :
    M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS =
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ := by
  sorry

omit hε in
/-- The no-wrap law at the two cut-start strands (feeds `traversalBetween_span_two`). -/
theorem strandOf_cutStartS_val :
    (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2.val + 2 <
      (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k :=
  M.cut_val _ (Or.inl (M.kind_strandOf _ _))

omit hε in
theorem strandOf_cutStartT_val :
    (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2.val + 2 <
      (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k :=
  M.cut_val _ (Or.inr (M.kind_strandOf _ _))

theorem arcST₀_ne_arcTS₀ : arcST₀ D x M hε ≠ arcTS₀ D x M hε := by
  sorry

theorem arcCover_toDiagram : Γ₀.ArcCover (disc D x ε) {arcST₀ D x M hε, arcTS₀ D x M hε} := by
  sorry

theorem arcST₀_start : Γ₀.eval (arcST₀ D x M hε).startPt = D.Γ.eval (arcS D x hε).startPt := by
  sorry
theorem arcST₀_stop : Γ₀.eval (arcST₀ D x M hε).stopPt = D.Γ.eval (arcT D x hε).stopPt := by
  sorry
theorem arcTS₀_start : Γ₀.eval (arcTS₀ D x M hε).startPt = D.Γ.eval (arcT D x hε).startPt := by
  sorry
theorem arcTS₀_stop : Γ₀.eval (arcTS₀ D x M hε).stopPt = D.Γ.eval (arcS D x hε).stopPt := by
  sorry

/-! ### 6e. The outside match -/

omit hε in
/-- The traversal point of `D` under a traversal point of `Γ₀`: the original strand at the
rescaled parameter (clamped into `[0,1)`; the clamp only acts on the arcs, which never occur
outside the disc). -/
def origPt (q : Γ₀.Pt) : D.Γ.Pt :=
  ⟨(M.orig ⟨q.1, q.2.1⟩).1, ((M.orig ⟨q.1, q.2.1⟩).2,
    clampIco ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val))⟩

omit hε in
theorem origPt_fst (q : Γ₀.Pt) : (origPt D x M q).1 = (M.orig ⟨q.1, q.2.1⟩).1 := rfl

omit hε in
theorem origPt_edge (q : Γ₀.Pt) : (origPt D x M q).2.1 = (M.orig ⟨q.1, q.2.1⟩).2 := rfl

/-- The rescaled parameter of a non-arc kind lies in `[0,1)` (so the clamp is inactive); arcs have
the constant parameter `τ ∈ (0,1)`. -/
theorem origParam_mem (κ : StrandKind D x) (θ : Set.Ico (0:ℝ) 1) :
    κ.origParam ε θ.val ∈ Set.Ico (0:ℝ) 1 := by
  sorry

theorem origPt_param (q : Γ₀.Pt) :
    (origPt D x M q).2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val :=
  clampIco_val_of_mem (origParam_mem D x M hε _ _)

/-- Outside the open disc, `origPt` traces the same point. -/
theorem eval_origPt (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) = Γ₀.eval q := by
  sorry

theorem origPt_outside (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) ∉ interior (disc D x ε) := by
  rw [eval_origPt D x M hε q hq]; exact hq

/-- `origPt` is a bijection from the outside traversal points of `Γ₀` onto those of `D`. -/
theorem origPt_bijective :
    Function.Bijective (fun q : Γ₀.Outside (disc D x ε) =>
      (⟨origPt D x M q.1, origPt_outside D x M hε q.1 q.2⟩ : D.Γ.Outside (disc D x ε))) := by
  sorry

/-- The outside correspondence `φ`. -/
def outsideEquiv : D.Γ.Outside (disc D x ε) ≃ Γ₀.Outside (disc D x ε) :=
  (Equiv.ofBijective _ (origPt_bijective D x M hε)).symm

theorem outsideEquiv_eval (q : D.Γ.Outside (disc D x ε)) :
    Γ₀.eval (outsideEquiv D x M hε q).1 = D.Γ.eval q.1 := by
  sorry

theorem outsideEquiv_dir_pos (q : D.Γ.Outside (disc D x ε)) (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧
      Γ₀.dir (Γ₀.strandOf (outsideEquiv D x M hε q).1) = l • D.Γ.dir (D.Γ.strandOf q.1) := by
  sorry

theorem outsideEquiv_dir_pos_before (q : D.Γ.Outside (disc D x ε))
    (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore (outsideEquiv D x M hε q).1) =
      l • D.Γ.dir (D.Γ.strandBefore q.1) := by
  sorry

/-- The outer crossings of `D` are the crossings other than `x`; all crossings of `D₀` are outer. -/
def outerEquiv : D.OuterCrossing (disc D x ε) ≃ (toDiagram D x M hε).OuterCrossing (disc D x ε) :=
  ((Equiv.subtypeEquivRight (fun y => by
      show D.Γ.crossingPoint y ∉ interior (disc D x ε) ↔ y ≠ x
      rw [inner_iff_D D x hε])).trans (crossingEquiv D x M hε).symm).trans
    (Equiv.subtypeUnivEquiv (no_inner_toDiagram D x M hε)).symm

theorem outsideEquiv_outerOverPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerOverPt y) =
      (toDiagram D x M hε).outerOverPt (outerEquiv D x M hε y) := by
  sorry

theorem outsideEquiv_outerUnderPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerUnderPt y) =
      (toDiagram D x M hε).outerUnderPt (outerEquiv D x M hε y) := by
  sorry

/-- The outside match of `D` and its smoothing. -/
def outsideMatch : OutsideMatch (disc D x ε) D (toDiagram D x M hε) where
  φ := outsideEquiv D x M hε
  eval_eq := outsideEquiv_eval D x M hε
  dir_pos := outsideEquiv_dir_pos D x M hε
  dir_pos_before := outsideEquiv_dir_pos_before D x M hε
  ψ := outerEquiv D x M hε
  over_eq := outsideEquiv_outerOverPt D x M hε
  under_eq := outsideEquiv_outerUnderPt D x M hε

/-! ### 6f. The smoothing data -/

/-- **The oriented smoothing data** of a splice model. -/
def orientedSmoothingData : OrientedSmoothingData (disc D x ε) D x (toDiagram D x M hε) where
  frame := localFrame D x M hε
  center := center_mem D x hε
  out := outsideMatch D x M hε
  a := arcS D x hε
  b := arcT D x hε
  ab := arcS_ne_arcT D x hε
  cover := arcCover_D D x hε
  over_on_a := overOn_arcS D x hε
  under_on_b := underOn_arcT D x hε
  inner_iff := inner_iff_D D x hε
  a₀ := arcST₀ D x M hε
  b₀ := arcTS₀ D x M hε
  ab₀ := arcST₀_ne_arcTS₀ D x M hε
  cover₀ := arcCover_toDiagram D x M hε
  no_inner₀ := no_inner_toDiagram D x M hε
  a₀_start := arcST₀_start D x M hε
  a₀_stop := arcST₀_stop D x M hε
  b₀_start := arcTS₀_start D x M hε
  b₀_stop := arcTS₀_stop D x M hε

theorem isOrientedSmoothing_toDiagram : IsOrientedSmoothing D x (toDiagram D x M hε) :=
  ⟨disc D x ε, ⟨orientedSmoothingData D x M hε⟩⟩

end Model

/-! ## 7. The concrete shadows

Both shadows list the new component(s) first (index `0`, and `1` in the self case, via
`Fin.cases`, which reduces definitionally on `0` and `Fin.succ`), then the untouched components of
`D` in increasing order (`Finset.orderEmbOfFin`).  Vertex tuples are given by `ZMod.val` case
analysis; old vertices are addressed as `P (a + 1 + m)` so that no cast between `ZMod` sizes is
needed. -/

/-- `k_i`, the vertex count of the component of `s`. -/
abbrev kI : ℕ := (D.Γ.comp (sS D x).1).k
/-- `k_j`, the vertex count of the component of `t`. -/
abbrev kJ : ℕ := (D.Γ.comp (tS D x).1).k
/-- The vertex tuple of the component of `s`. -/
abbrev Pi : LabelledTuple (kI D x) := (D.Γ.comp (sS D x).1).P
/-- The vertex tuple of the component of `t`. -/
abbrev Pj : LabelledTuple (kJ D x) := (D.Γ.comp (tS D x).1).P
/-- The edge label `a` of `s`. -/
abbrev aS : ZMod (kI D x) := (sS D x).2
/-- The edge label `b` of `t`. -/
abbrev bT : ZMod (kJ D x) := (tS D x).2

/-! ### 7-pre. A small `ZMod.val` toolbox for the index arithmetic of the concrete models
(U5-concrete-models).  Everything here is elementary; the lemmas are phrased so that every use in
§7a/§7b is a `rw` followed by `omega`, `ring` or `module`. -/

theorem three_le_kI : 3 ≤ kI D x := (D.Γ.comp (sS D x).1).hk
theorem three_le_kJ : 3 ≤ kJ D x := (D.Γ.comp (tS D x).1).hk

theorem zval_one_of_two_le {n : ℕ} (hn : 2 ≤ n) : (1 : ZMod n).val = 1 := by
  rw [ZMod.val_one_eq_one_mod, Nat.mod_eq_of_lt (by omega)]

theorem zval_add_one_of_lt {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val + 1 < n) :
    (m + 1).val = m.val + 1 := by
  have h1 : (1 : ZMod n).val = 1 := zval_one_of_two_le (by omega)
  rw [ZMod.val_add_of_lt (by rw [h1]; exact h), h1]

theorem zval_add_one_of_eq {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val + 1 = n) : (m + 1).val = 0 := by
  rw [ZMod.val_eq_zero]
  have : ((m.val + 1 : ℕ) : ZMod n) = 0 := by rw [h, ZMod.natCast_self]
  rwa [Nat.cast_succ, ZMod.natCast_zmod_val] at this

theorem zval_sub_one_of_pos {n : ℕ} [NeZero n] (m : ZMod n) (h : 0 < m.val) :
    (m - 1).val = m.val - 1 := by
  have hn : 2 ≤ n := by have := ZMod.val_lt m; omega
  have h1 : (1 : ZMod n).val = 1 := zval_one_of_two_le hn
  rw [ZMod.val_sub (by rw [h1]; exact h), h1]

/-- `(n - c : ℕ)` cast to `ZMod n` is `-c`. -/
theorem zcast_sub_self {n c : ℕ} (hc : c ≤ n) : ((n - c : ℕ) : ZMod n) = -(c : ZMod n) := by
  rw [Nat.cast_sub hc, ZMod.natCast_self, zero_sub]

theorem zval_sub_one_of_zero {n : ℕ} [NeZero n] (m : ZMod n) (h : m.val = 0) : (m - 1).val = n - 1 := by
  rw [ZMod.val_eq_zero] at h
  subst h
  have hn : 0 < n := NeZero.pos n
  rw [zero_sub, ← Nat.cast_one, ← zcast_sub_self (by omega), ZMod.val_natCast_of_lt (by omega)]

theorem zcast_pred {n v : ℕ} (hv : 0 < v) : ((v - 1 : ℕ) : ZMod n) = (v : ZMod n) - 1 := by
  rw [Nat.cast_sub hv, Nat.cast_one]

theorem nat_eq_of_zcast_eq {n v v' : ℕ} (hv : v < n) (hv' : v' < n) (h : (v : ZMod n) = v') : v = v' := by
  have := congrArg ZMod.val h
  rwa [ZMod.val_natCast_of_lt hv, ZMod.val_natCast_of_lt hv'] at this

theorem zcast_ne_zero_of_lt {n v : ℕ} (h0 : 0 < v) (hv : v < n) : (v : ZMod n) ≠ 0 := by
  intro h
  rw [ZMod.natCast_eq_zero_iff] at h
  exact absurd (Nat.le_of_dvd h0 h) (by omega)

/-- A strand with first component `i` is `⟨i, its label transported by value⟩`. -/
theorem Strand_eq_mk_val {Γ : Shadow} {e : Γ.Strand} {i : Fin Γ.c} (hi : i = e.1) :
    e = ⟨i, (e.2.val : ZMod (Γ.comp i).k)⟩ := by
  obtain ⟨l, c⟩ := e
  dsimp only at hi
  subst hi
  simp

theorem Strand_mk_eq_mk_iff {Γ : Shadow} {i : Fin Γ.c} {c c' : ZMod (Γ.comp i).k} :
    (⟨i, c⟩ : Γ.Strand) = ⟨i, c'⟩ ↔ c = c' := by
  simp

theorem Strand_mk_ne_mk_of_ne {Γ : Shadow} {i j : Fin Γ.c} {c : ZMod (Γ.comp i).k}
    {c' : ZMod (Γ.comp j).k} (h : i ≠ j) : (⟨i, c⟩ : Γ.Strand) ≠ ⟨j, c'⟩ :=
  fun heq => h (congrArg Sigma.fst heq)

/-- The vertex identities used to place the cut points: `P_i (a + 1 + (k_i − 1)) = P_i a`. -/
theorem Pi_a_wrap : Pi D x (aS D x + 1 + ((kI D x - 1 : ℕ) : ZMod (kI D x))) = D.Γ.tail (sS D x) := by
  have := three_le_kI D x
  rw [zcast_sub_self (by omega), Nat.cast_one, add_neg_cancel_right]; rfl

theorem Pj_b_wrap : Pj D x (bT D x + 1 + ((kJ D x - 1 : ℕ) : ZMod (kJ D x))) = D.Γ.tail (tS D x) := by
  have := three_le_kJ D x
  rw [zcast_sub_self (by omega), Nat.cast_one, add_neg_cancel_right]; rfl

theorem tail_sS : D.Γ.tail (sS D x) = Pi D x (aS D x) := rfl
theorem tail_tS : D.Γ.tail (tS D x) = Pj D x (bT D x) := rfl
theorem es_eq : es D x = Pi D x (aS D x + 1) - Pi D x (aS D x) := rfl
theorem et_eq : et D x = Pj D x (bT D x + 1) - Pj D x (bT D x) := rfl

/-! ### 7a. The mixed case: `i ≠ j`, two components joined into one

Vertices of the merged component, `N = k_i + k_j + 4`:
`Q m = P_i (a+1+m)` for `m < k_i` (so `Q (k_i−1) = P_i a`), `Q k_i = s⁻`, `Q (k_i+1) = t⁺`,
`Q (k_i+2+m) = P_j (b+1+m)` for `m < k_j` (so `Q (k_i+1+k_j) = P_j b`), `Q (k_i+2+k_j) = t⁻`,
`Q (k_i+3+k_j) = s⁺`, and `Q N = Q 0 = P_i (a+1)`.
Edges: `0 … k_i−2` old `⟨i, a+1+m⟩`; `k_i−1` = `[P_i a, s⁻]` (cutStartS); `k_i` = arcST;
`k_i+1` = `[t⁺, P_j (b+1)]` (cutEndT); `k_i+2 … k_i+k_j` old `⟨j, b+1+m⟩`; `k_i+1+k_j` = cutStartT;
`k_i+2+k_j` = arcTS; `k_i+3+k_j` = `[s⁺, P_i (a+1)]` (cutEndS). -/

/-- The vertex tuple of the merged component. -/
def mergedTuple : LabelledTuple (kI D x + kJ D x + 4) := fun m =>
  if m.val < kI D x then Pi D x (aS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = kI D x then sMinus D x ε
  else if m.val = kI D x + 1 then tPlus D x ε
  else if m.val < kI D x + 2 + kJ D x then
    Pj D x (bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x)))
  else if m.val = kI D x + 2 + kJ D x then tMinus D x ε
  else sPlus D x ε

/-- The merged component (`k_i + k_j + 4 ≥ 10` vertices). -/
def mergedComp : PolyComp := ⟨kI D x + kJ D x + 4, by omega, mergedTuple D x ε⟩

/-- The components of `D` other than those of `s` and `t`. -/
def othersM : Finset (Fin D.Γ.c) := (Finset.univ.erase (sS D x).1).erase (tS D x).1

theorem card_othersM (h : (sS D x).1 ≠ (tS D x).1) : (othersM D x).card + 2 = D.Γ.c := by
  have hj : (tS D x).1 ∈ Finset.univ.erase (sS D x).1 := by
    rw [Finset.mem_erase]; exact ⟨Ne.symm h, Finset.mem_univ _⟩
  have h1 : 0 < (Finset.univ.erase (sS D x).1).card := Finset.card_pos.mpr ⟨_, hj⟩
  unfold othersM
  rw [Finset.card_erase_of_mem hj, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
    Fintype.card_fin] at *
  omega

/-- The mixed smoothed shadow: the merged component first, then the untouched components. -/
def mixedShadow : Shadow where
  c := (othersM D x).card + 1
  hc := Nat.succ_pos _
  comp := Fin.cases (mergedComp D x ε) (fun l => D.Γ.comp ((othersM D x).orderEmbOfFin rfl l))

@[simp] theorem mixedShadow_comp_zero :
    (mixedShadow D x ε).comp (0 : Fin ((othersM D x).card + 1)) = mergedComp D x ε := rfl

@[simp] theorem mixedShadow_comp_succ (l : Fin (othersM D x).card) :
    (mixedShadow D x ε).comp l.succ = D.Γ.comp ((othersM D x).orderEmbOfFin rfl l) := rfl

/-- The kind of the edge with index `m` (as a natural number) of the merged component. -/
def mergedKindIdx (m : ℕ) : StrandKind D x :=
  if m < kI D x - 1 then StrandKind.old ⟨(sS D x).1, aS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = kI D x - 1 then StrandKind.cutStartS
  else if m = kI D x then StrandKind.arcST
  else if m = kI D x + 1 then StrandKind.cutEndT
  else if m < kI D x + 1 + kJ D x then
    StrandKind.old ⟨(tS D x).1, bT D x + 1 + ((m - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩
  else if m = kI D x + 1 + kJ D x then StrandKind.cutStartT
  else if m = kI D x + 2 + kJ D x then StrandKind.arcTS
  else StrandKind.cutEndS

/-- The kind map of the mixed shadow. -/
def mixedKind (u : (mixedShadow D x ε).Strand) : StrandKind D x :=
  Fin.cases (motive := fun l => ZMod ((mixedShadow D x ε).comp l).k → StrandKind D x)
    (fun m => mergedKindIdx D x m.val)
    (fun l m => StrandKind.old ⟨(othersM D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩) u.1 u.2

/-! #### Index arithmetic for the mixed shadow (U5) -/

/-- Case analysis on the strands of the mixed shadow: the merged component, or an untouched one. -/
theorem mixedShadow_strand_cases {P : (mixedShadow D x ε).Strand → Prop}
    (h0 : ∀ m : ZMod (kI D x + kJ D x + 4), P ⟨(0 : Fin ((othersM D x).card + 1)), m⟩)
    (hs : ∀ (l : Fin (othersM D x).card)
      (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k), P ⟨l.succ, m⟩)
    (u : (mixedShadow D x ε).Strand) : P u := by
  obtain ⟨l, m⟩ := u
  induction l using Fin.cases with
  | zero => exact h0 m
  | succ l => exact hs l m

theorem mixedKind_zero (m : ZMod (kI D x + kJ D x + 4)) :
    mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ = mergedKindIdx D x m.val := rfl

theorem mixedKind_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    mixedKind D x ε ⟨l.succ, m⟩ =
      StrandKind.old ⟨(othersM D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩ := rfl

theorem mixedShadow_tail_zero (m : ZMod (kI D x + kJ D x + 4)) :
    (mixedShadow D x ε).tail ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ = mergedTuple D x ε m := rfl

theorem mixedShadow_dir_zero (m : ZMod (kI D x + kJ D x + 4)) :
    (mixedShadow D x ε).dir ⟨(0 : Fin ((othersM D x).card + 1)), m⟩ =
      mergedTuple D x ε (m + 1) - mergedTuple D x ε m := rfl

theorem mixedShadow_tail_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    (mixedShadow D x ε).tail ⟨l.succ, m⟩ = D.Γ.tail ⟨(othersM D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem mixedShadow_dir_succ (l : Fin (othersM D x).card)
    (m : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k) :
    (mixedShadow D x ε).dir ⟨l.succ, m⟩ = D.Γ.dir ⟨(othersM D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem mixedShadow_comp_succ_k (l : Fin (othersM D x).card) :
    ((mixedShadow D x ε).comp l.succ).k = (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k := rfl

/-- The untouched components are neither `i` nor `j`. -/
theorem orderEmbOfFin_othersM_ne (l : Fin (othersM D x).card) :
    (othersM D x).orderEmbOfFin rfl l ≠ (sS D x).1 ∧ (othersM D x).orderEmbOfFin rfl l ≠ (tS D x).1 := by
  have := Finset.orderEmbOfFin_mem (othersM D x) rfl l
  simp only [othersM, Finset.mem_erase, Finset.mem_univ, and_true] at this
  exact ⟨this.2, this.1⟩

/-- The eight blocks of labels of the merged component. -/
theorem merged_block (v : ℕ) (hv : v < kI D x + kJ D x + 4) :
    v < kI D x - 1 ∨ v = kI D x - 1 ∨ v = kI D x ∨ v = kI D x + 1 ∨
    (kI D x + 2 ≤ v ∧ v < kI D x + 1 + kJ D x) ∨ v = kI D x + 1 + kJ D x ∨
    v = kI D x + 2 + kJ D x ∨ v = kI D x + 3 + kJ D x := by
  omega

theorem mergedKindIdx_of_lt {v : ℕ} (hv : v < kI D x - 1) :
    mergedKindIdx D x v = StrandKind.old ⟨(sS D x).1, aS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold mergedKindIdx; split_ifs; rfl

theorem mergedKindIdx_eq_cutStartS {v : ℕ} (hv : v = kI D x - 1) :
    mergedKindIdx D x v = StrandKind.cutStartS := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_arcST {v : ℕ} (hv : v = kI D x) : mergedKindIdx D x v = StrandKind.arcST := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutEndT {v : ℕ} (hv : v = kI D x + 1) :
    mergedKindIdx D x v = StrandKind.cutEndT := by
  have := three_le_kI D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_of_j {v : ℕ} (h1 : kI D x + 2 ≤ v) (h2 : v < kI D x + 1 + kJ D x) :
    mergedKindIdx D x v =
      StrandKind.old ⟨(tS D x).1, bT D x + 1 + ((v - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ := by
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutStartT {v : ℕ} (hv : v = kI D x + 1 + kJ D x) :
    mergedKindIdx D x v = StrandKind.cutStartT := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_arcTS {v : ℕ} (hv : v = kI D x + 2 + kJ D x) :
    mergedKindIdx D x v = StrandKind.arcTS := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedKindIdx_eq_cutEndS {v : ℕ} (hv : v = kI D x + 3 + kJ D x) :
    mergedKindIdx D x v = StrandKind.cutEndS := by
  have := three_le_kJ D x
  unfold mergedKindIdx; split_ifs <;> first | rfl | omega

theorem mergedTuple_of_lt (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val < kI D x) :
    mergedTuple D x ε m = Pi D x (aS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold mergedTuple; split_ifs; rfl

theorem mergedTuple_eq_sMinus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x) :
    mergedTuple D x ε m = sMinus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_tPlus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 1) :
    mergedTuple D x ε m = tPlus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_of_j (m : ZMod (kI D x + kJ D x + 4)) (h1 : kI D x + 2 ≤ m.val)
    (h2 : m.val < kI D x + 2 + kJ D x) :
    mergedTuple D x ε m = Pj D x (bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))) := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_tMinus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 2 + kJ D x) :
    mergedTuple D x ε m = tMinus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

theorem mergedTuple_eq_sPlus (m : ZMod (kI D x + kJ D x + 4)) (hv : m.val = kI D x + 3 + kJ D x) :
    mergedTuple D x ε m = sPlus D x ε := by
  unfold mergedTuple; split_ifs <;> first | rfl | omega

/-- An old kind of the merged component lies on the component of `s` or of `t`. -/
theorem mergedKindIdx_old_fst {v : ℕ} (hv : v < kI D x + kJ D x + 4) (e : D.Γ.Strand)
    (he : mergedKindIdx D x v = StrandKind.old e) : e.1 = (sS D x).1 ∨ e.1 = (tS D x).1 := by
  rcases merged_block D x v hv with h1 | h1 | h1 | h1 | ⟨h1, h1'⟩ | h1 | h1 | h1
  · rw [mergedKindIdx_of_lt D x h1] at he; exact Or.inl (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [mergedKindIdx_eq_cutStartS D x h1] at he; cases he
  · rw [mergedKindIdx_eq_arcST D x h1] at he; cases he
  · rw [mergedKindIdx_eq_cutEndT D x h1] at he; cases he
  · rw [mergedKindIdx_of_j D x h1 h1'] at he; exact Or.inr (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [mergedKindIdx_eq_cutStartT D x h1] at he; cases he
  · rw [mergedKindIdx_eq_arcTS D x h1] at he; cases he
  · rw [mergedKindIdx_eq_cutEndS D x h1] at he; cases he

/-- The label of an old strand `a + 1 + v` of a `n`-gon, recovered from its value. -/
theorem zmod_code_eq {n : ℕ} [NeZero n] (a : ZMod n) {v : ℕ} (hv : v < n) :
    ((a + 1 + (v : ZMod n)).val + (n - 1) - a.val) % n = v := by
  have hn := NeZero.pos n
  have ha := ZMod.val_lt a
  have h1 : a.val ≤ (a + 1 + (v : ZMod n)).val + (n - 1) := by omega
  have h2 : (((a + 1 + (v : ZMod n)).val + (n - 1) - a.val : ℕ) : ZMod n) = (v : ZMod n) := by
    rw [Nat.cast_sub h1, Nat.cast_add, ZMod.natCast_zmod_val, ZMod.natCast_zmod_val,
      zcast_sub_self (by omega), Nat.cast_one]
    ring
  have := congrArg ZMod.val h2
  rwa [ZMod.val_natCast, ZMod.val_natCast_of_lt hv] at this

/-- A left inverse of `mergedKindIdx` on the labels of the merged component. -/
def mergedCode : StrandKind D x → ℕ
  | .old e =>
      if e.1 = (sS D x).1 then (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x
      else kI D x + 2 + (e.2.val + (kJ D x - 1) - (bT D x).val) % kJ D x
  | .cutStartS => kI D x - 1
  | .arcST => kI D x
  | .cutEndT => kI D x + 1
  | .cutStartT => kI D x + 1 + kJ D x
  | .arcTS => kI D x + 2 + kJ D x
  | .cutEndS => kI D x + 3 + kJ D x

theorem mergedCode_mergedKindIdx (h : (sS D x).1 ≠ (tS D x).1) {v : ℕ}
    (hv : v < kI D x + kJ D x + 4) : mergedCode D x (mergedKindIdx D x v) = v := by
  have hk := three_le_kI D x
  have hk' := three_le_kJ D x
  rcases merged_block D x v hv with h1 | h1 | h1 | h1 | ⟨h1, h1'⟩ | h1 | h1 | h1
  · rw [mergedKindIdx_of_lt D x h1]
    simp only [mergedCode, ↓reduceIte]
    exact zmod_code_eq (aS D x) (by omega)
  · rw [mergedKindIdx_eq_cutStartS D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_arcST D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_cutEndT D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_of_j D x h1 h1']
    simp only [mergedCode]
    rw [ite_eq_right (Ne.symm h), zmod_code_eq (bT D x) (by omega)]
    omega
  · rw [mergedKindIdx_eq_cutStartT D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_arcTS D x h1]; simp only [mergedCode]; omega
  · rw [mergedKindIdx_eq_cutEndS D x h1]; simp only [mergedCode]; omega

/-- The kind map of the merged component is injective on its labels. -/
theorem mergedKindIdx_inj (h : (sS D x).1 ≠ (tS D x).1) {v v' : ℕ} (hv : v < kI D x + kJ D x + 4)
    (hv' : v' < kI D x + kJ D x + 4) (heq : mergedKindIdx D x v = mergedKindIdx D x v') : v = v' := by
  have := congrArg (mergedCode D x) heq
  rwa [mergedCode_mergedKindIdx D x h hv, mergedCode_mergedKindIdx D x h hv'] at this

/-- The mixed shadow is a splice model (index arithmetic on `ZMod.val`). -/
def mixedModel (h : (sS D x).1 ≠ (tS D x).1) : SpliceModel D x ε (mixedShadow D x ε) where
  kind := mixedKind D x ε
  kind_injective := by
    show ∀ u u' : (mixedShadow D x ε).Strand, mixedKind D x ε u = mixedKind D x ε u' → u = u'
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      refine mixedShadow_strand_cases D x ε ?_ ?_
      · intro m' heq
        rw [mixedKind_zero, mixedKind_zero] at heq
        rw [ZMod.val_injective _ (mergedKindIdx_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro l' m' heq
        exfalso
        rw [mixedKind_zero, mixedKind_succ] at heq
        rcases mergedKindIdx_old_fst D x (ZMod.val_lt m) _ heq with h1 | h1
        · exact (orderEmbOfFin_othersM_ne D x l').1 h1
        · exact (orderEmbOfFin_othersM_ne D x l').2 h1
    · intro l m
      refine mixedShadow_strand_cases D x ε ?_ ?_
      · intro m' heq
        exfalso
        rw [mixedKind_zero, mixedKind_succ] at heq
        rcases mergedKindIdx_old_fst D x (ZMod.val_lt m') _ heq.symm with h1 | h1
        · exact (orderEmbOfFin_othersM_ne D x l).1 h1
        · exact (orderEmbOfFin_othersM_ne D x l).2 h1
      · intro l' m' heq
        rw [mixedKind_succ, mixedKind_succ] at heq
        have h1 := StrandKind.old.inj heq
        rw [Sigma.mk.inj_iff] at h1
        obtain ⟨h1, h2⟩ := h1
        have hl : l = l' := ((othersM D x).orderEmbOfFin rfl).injective h1
        subst hl
        have h3 := eq_of_heq h2
        simp only [ZMod.natCast_zmod_val] at h3
        rw [h3]
  kind_surj := by
    intro κ hκ
    have hk := three_le_kI D x
    have hk' := three_le_kJ D x
    cases κ with
    | old e =>
      obtain ⟨hs, ht⟩ := hκ
      have hs' : e ≠ sS D x := fun h' => hs (by rw [h'])
      have ht' : e ≠ tS D x := fun h' => ht (by rw [h'])
      obtain ⟨l₀, c⟩ := e
      by_cases hi : l₀ = (sS D x).1
      · subst hi
        have hca : c ≠ aS D x := fun h' => hs' (Sigma.ext rfl (heq_of_eq h'))
        obtain ⟨v, hv⟩ : ∃ v, v = (c - aS D x - 1).val := ⟨_, rfl⟩
        have hv1 : v < kI D x := by rw [hv]; exact ZMod.val_lt _
        have hv2 : v ≠ kI D x - 1 := by
          intro h2
          apply hca
          have h3 : ((c - aS D x - 1).val : ZMod (kI D x)) = c - aS D x - 1 := ZMod.natCast_zmod_val _
          rw [← hv, h2, zcast_sub_self (by omega), Nat.cast_one] at h3
          linear_combination -h3
        refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), (v : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
        rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega), mergedKindIdx_of_lt D x (by omega)]
        simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        rw [hv, ZMod.natCast_zmod_val]; ring
      · by_cases hj : l₀ = (tS D x).1
        · subst hj
          have hcb : c ≠ bT D x := fun h' => ht' (Sigma.ext rfl (heq_of_eq h'))
          obtain ⟨w, hw⟩ : ∃ w, w = (c - bT D x - 1).val := ⟨_, rfl⟩
          have hw1 : w < kJ D x := by rw [hw]; exact ZMod.val_lt _
          have hw2 : w ≠ kJ D x - 1 := by
            intro h2
            apply hcb
            have h3 : ((c - bT D x - 1).val : ZMod (kJ D x)) = c - bT D x - 1 := ZMod.natCast_zmod_val _
            rw [← hw, h2, zcast_sub_self (by omega), Nat.cast_one] at h3
            linear_combination -h3
          refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
            ((kI D x + 2 + w : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
          rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega),
            mergedKindIdx_of_j D x (by omega) (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have : kI D x + 2 + w - (kI D x + 2) = w := by omega
          rw [this, hw, ZMod.natCast_zmod_val]; ring
        · have hmem : l₀ ∈ othersM D x := by
            simp only [othersM, Finset.mem_erase, Finset.mem_univ, and_true]
            exact ⟨hj, hi⟩
          have hrange : l₀ ∈ Set.range ((othersM D x).orderEmbOfFin rfl) := by
            rw [Finset.range_orderEmbOfFin]; exact hmem
          obtain ⟨l, hl⟩ := hrange
          subst hl
          exact ⟨⟨l.succ, c⟩, by rw [mixedKind_succ, ZMod.natCast_zmod_val]⟩
    | cutStartS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x - 1 : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutStartS D x rfl
    | cutEndS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 3 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutEndS D x rfl
    | cutStartT =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 1 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutStartT D x rfl
    | cutEndT =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x + 1 : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_cutEndT D x rfl
    | arcST =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)), ((kI D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_arcST D x rfl
    | arcTS =>
      refine ⟨⟨(0 : Fin ((othersM D x).card + 1)),
        ((kI D x + 2 + kJ D x : ℕ) : ZMod (kI D x + kJ D x + 4))⟩, ?_⟩
      rw [mixedKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact mergedKindIdx_eq_arcTS D x rfl
  kind_occurs := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · rw [mergedKindIdx_of_lt D x hv]
        refine StrandKind.occurs_old ?_ (Strand_mk_ne_mk_of_ne h)
        intro heq
        have heq2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
            ⟨(sS D x).1, (sS D x).2⟩ := heq
        have heq' := Strand_mk_eq_mk_iff.mp heq2
        have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
          push_cast; linear_combination heq'
        exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [mergedKindIdx_eq_cutStartS D x hv]; exact StrandKind.occurs_cutStartS
      · rw [mergedKindIdx_eq_arcST D x hv]; exact StrandKind.occurs_arcST
      · rw [mergedKindIdx_eq_cutEndT D x hv]; exact StrandKind.occurs_cutEndT
      · rw [mergedKindIdx_of_j D x hv hv']
        refine StrandKind.occurs_old (Strand_mk_ne_mk_of_ne (Ne.symm h)) ?_
        intro heq
        have heq2 : (⟨(tS D x).1, bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ :
            D.Γ.Strand) = ⟨(tS D x).1, (tS D x).2⟩ := heq
        have heq' := Strand_mk_eq_mk_iff.mp heq2
        have h2 : ((m.val - (kI D x + 2) + 1 : ℕ) : ZMod (kJ D x)) = 0 := by
          push_cast; linear_combination heq'
        exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [mergedKindIdx_eq_cutStartT D x hv]; exact StrandKind.occurs_cutStartT
      · rw [mergedKindIdx_eq_arcTS D x hv]; exact StrandKind.occurs_arcTS
      · rw [mergedKindIdx_eq_cutEndS D x hv]; exact StrandKind.occurs_cutEndS
    · intro l m
      rw [mixedKind_succ]
      exact StrandKind.occurs_old (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).1)
        (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).2)
  kind_pred := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      show mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), (m - 1 : ZMod (kI D x + kJ D x + 4))⟩ =
        (mixedKind D x ε ⟨(0 : Fin ((othersM D x).card + 1)), m⟩).pred
      rw [mixedKind_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · -- old strands of the component of `s`
        rw [mergedKindIdx_of_lt D x hv]
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, mergedKindIdx_eq_cutEndS D x (by omega), h0, Nat.cast_zero,
            add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
        · rw [zval_sub_one_of_pos m h0, mergedKindIdx_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne1 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          rw [ite_eq_right hne1, ite_eq_right (Strand_mk_ne_mk_of_ne h)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartS at `k_i − 1`: predecessor `old ⟨i, a − 1⟩` at `k_i − 2`
        rw [mergedKindIdx_eq_cutStartS D x hv, zval_sub_one_of_pos m (by omega), hv,
          mergedKindIdx_of_lt D x (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have : kI D x - 1 - 1 = kI D x - 2 := by omega
        rw [this, zcast_sub_self (by omega)]
        push_cast; ring
      · rw [mergedKindIdx_eq_arcST D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_cutStartS D x (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutEndT D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_arcST D x (by omega)]; rfl
      · -- old strands of the component of `t`
        rw [mergedKindIdx_of_j D x hv hv']
        rcases Nat.lt_or_ge (kI D x + 2) m.val with h0 | h0
        · rw [zval_sub_one_of_pos m (by omega), mergedKindIdx_of_j D x (by omega) (by omega)]
          simp only [StrandKind.pred]
          have hne2 : (⟨(tS D x).1, bT D x + 1 + ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x))⟩ :
              D.Γ.Strand) ≠ ⟨(tS D x).1, (tS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : ((m.val - (kI D x + 2) : ℕ) : ZMod (kJ D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt (by omega) (by omega) h2
          rw [ite_eq_right (Strand_mk_ne_mk_of_ne (Ne.symm h)), ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have : m.val - 1 - (kI D x + 2) = m.val - (kI D x + 2) - 1 := by omega
          rw [this, zcast_pred (by omega)]; ring
        · have hv2 : m.val = kI D x + 2 := by omega
          rw [zval_sub_one_of_pos m (by omega), mergedKindIdx_eq_cutEndT D x (by omega), hv2]
          have : kI D x + 2 - (kI D x + 2) = 0 := by omega
          rw [this, Nat.cast_zero, add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
          rw [ite_eq_right (Strand_mk_ne_mk_of_ne (Ne.symm h))]
      · -- cutStartT at `k_i + 1 + k_j`: predecessor `old ⟨j, b − 1⟩`
        rw [mergedKindIdx_eq_cutStartT D x hv, zval_sub_one_of_pos m (by omega), hv,
          mergedKindIdx_of_j D x (by omega) (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have : kI D x + 1 + kJ D x - 1 - (kI D x + 2) = kJ D x - 2 := by omega
        rw [this, zcast_sub_self (by omega)]
        push_cast; ring
      · rw [mergedKindIdx_eq_arcTS D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_cutStartT D x (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutEndS D x hv, zval_sub_one_of_pos m (by omega),
          mergedKindIdx_eq_arcTS D x (by omega)]; rfl
    · intro l m
      show mixedKind D x ε ⟨l.succ, (m - 1 : ZMod (D.Γ.comp ((othersM D x).orderEmbOfFin rfl l)).k)⟩ =
        (mixedKind D x ε ⟨l.succ, m⟩).pred
      rw [mixedKind_succ, mixedKind_succ]
      simp only [StrandKind.pred, ZMod.natCast_zmod_val]
      rw [ite_eq_right (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).1),
        ite_eq_right (Strand_mk_ne_mk_of_ne (orderEmbOfFin_othersM_ne D x l).2)]
  tail_eq := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedShadow_tail_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · rw [mergedKindIdx_of_lt D x hv, mergedTuple_of_lt D x ε m (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutStartS D x hv, mergedTuple_of_lt D x ε m (by omega), hv, Pi_a_wrap]; rfl
      · rw [mergedKindIdx_eq_arcST D x hv, mergedTuple_eq_sMinus D x ε m hv]; rfl
      · rw [mergedKindIdx_eq_cutEndT D x hv, mergedTuple_eq_tPlus D x ε m hv]; rfl
      · rw [mergedKindIdx_of_j D x hv hv', mergedTuple_of_j D x ε m hv (by omega)]; rfl
      · rw [mergedKindIdx_eq_cutStartT D x hv, mergedTuple_of_j D x ε m (by omega) (by omega), hv]
        have : kI D x + 1 + kJ D x - (kI D x + 2) = kJ D x - 1 := by omega
        rw [this, Pj_b_wrap]; rfl
      · rw [mergedKindIdx_eq_arcTS D x hv, mergedTuple_eq_tMinus D x ε m hv]; rfl
      · rw [mergedKindIdx_eq_cutEndS D x hv, mergedTuple_eq_sPlus D x ε m hv]; rfl
    · intro l m
      rw [mixedShadow_tail_succ, mixedKind_succ]
      simp only [StrandKind.tail, ZMod.natCast_zmod_val]
  dir_eq := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m
      rw [mixedShadow_dir_zero, mixedKind_zero]
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_of_lt D x hv, mergedTuple_of_lt D x ε (m + 1) (by omega),
          mergedTuple_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutStartS D x hv, mergedTuple_eq_sMinus D x ε (m + 1) (by omega),
          mergedTuple_of_lt D x ε m (by omega), hv, Pi_a_wrap]
        simp only [StrandKind.dir, sMinus]
        rw [pt_eq_s]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_arcST D x hv, mergedTuple_eq_tPlus D x ε (m + 1) (by omega),
          mergedTuple_eq_sMinus D x ε m hv]
        simp only [StrandKind.dir, sMinus, tPlus]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutEndT D x hv, mergedTuple_of_j D x ε (m + 1) (by omega) (by omega),
          mergedTuple_eq_tPlus D x ε m hv, h1, hv]
        have : kI D x + 1 + 1 - (kI D x + 2) = 0 := by omega
        rw [this, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, tPlus]
        rw [pt_eq_t, tail_tS, et_eq]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_of_j D x hv hv', mergedTuple_of_j D x ε (m + 1) (by omega) (by omega),
          mergedTuple_of_j D x ε m hv (by omega), h1]
        have : m.val + 1 - (kI D x + 2) = m.val - (kI D x + 2) + 1 := by omega
        rw [this, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_cutStartT D x hv, mergedTuple_eq_tMinus D x ε (m + 1) (by omega),
          mergedTuple_of_j D x ε m (by omega) (by omega), hv]
        have : kI D x + 1 + kJ D x - (kI D x + 2) = kJ D x - 1 := by omega
        rw [this, Pj_b_wrap]
        simp only [StrandKind.dir, tMinus]
        rw [pt_eq_t]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [mergedKindIdx_eq_arcTS D x hv, mergedTuple_eq_sPlus D x ε (m + 1) (by omega),
          mergedTuple_eq_tMinus D x ε m hv]
        simp only [StrandKind.dir, sPlus, tMinus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [mergedKindIdx_eq_cutEndS D x hv, mergedTuple_of_lt D x ε (m + 1) (by omega),
          mergedTuple_eq_sPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, sPlus]
        rw [pt_eq_s, tail_sS, es_eq]; module
    · intro l m
      rw [mixedShadow_dir_succ, mixedKind_succ]
      simp only [StrandKind.dir, ZMod.natCast_zmod_val]
  cut_val := by
    refine mixedShadow_strand_cases D x ε ?_ ?_
    · intro m hm
      rw [mixedKind_zero] at hm
      have hk := three_le_kI D x
      have hk' := three_le_kJ D x
      have hmv := ZMod.val_lt m
      show m.val + 2 < kI D x + kJ D x + 4
      rcases merged_block D x m.val hmv with hv | hv | hv | hv | ⟨hv, hv'⟩ | hv | hv | hv
      · omega
      · omega
      · omega
      · omega
      · omega
      · omega
      · rw [mergedKindIdx_eq_arcTS D x hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [mergedKindIdx_eq_cutEndS D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro l m hm
      rw [mixedKind_succ] at hm
      rcases hm with hm | hm <;> cases hm

/-! ### 7b. The self case: `i = j`, one component split into two

With `d = (b − a).val ∈ [2, k−2]` (non-adjacency), component `A` (`d + 2` vertices):
`Q_A m = P (a+1+m)` for `m < d` (so `Q_A (d−1) = P b`), `Q_A d = t⁻`, `Q_A (d+1) = s⁺`; edges
`0 … d−2` old `⟨i, a+1+m⟩`, `d−1` cutStartT, `d` arcTS, `d+1` cutEndS.  Component `B`
(`k − d + 2` vertices): `Q_B m = P (b+1+m)` for `m < k−d` (so `Q_B (k−d−1) = P a`),
`Q_B (k−d) = s⁻`, `Q_B (k−d+1) = t⁺`; edges `0 … k−d−2` old `⟨i, b+1+m⟩`, `k−d−1` cutStartS,
`k−d` arcST, `k−d+1` cutEndT.  `A` carries the occurrences met after `x` and before `τx`, `B` the
others (`A ↦ ⟦τx⟧`, `B ↦ ⟦x⟧` in `Record.SmoothComps`). -/

/-- The edge label of `t` transported to the component of `s` (by its value; meaningful when
`i = j`). -/
abbrev bS : ZMod (kI D x) := ((tS D x).2.val : ZMod (kI D x))

/-- `d = (b − a).val`: the number of edges from `a` to `b` going forward. -/
def dd : ℕ := (bS D x - aS D x).val

/-- In the self case the under strand is `⟨i, bS⟩`: `t` transported to the component of `s`. -/
theorem tS_eq_self (h : (sS D x).1 = (tS D x).1) : tS D x = ⟨(sS D x).1, bS D x⟩ :=
  Strand_eq_mk_val h

theorem tail_tS_self (h : (sS D x).1 = (tS D x).1) : D.Γ.tail (tS D x) = Pi D x (bS D x) :=
  congrArg D.Γ.tail (tS_eq_self D x h)

theorem et_self (h : (sS D x).1 = (tS D x).1) :
    et D x = Pi D x (bS D x + 1) - Pi D x (bS D x) :=
  congrArg D.Γ.dir (tS_eq_self D x h)

theorem pt_eq_t_self (h : (sS D x).1 = (tS D x).1) :
    pt D x = Pi D x (bS D x) + τt D x • et D x := by
  rw [pt_eq_t, tail_tS_self D x h]

theorem tS_succ_self (h : (sS D x).1 = (tS D x).1) :
    (⟨(tS D x).1, (tS D x).2 + 1⟩ : D.Γ.Strand) = ⟨(sS D x).1, bS D x + 1⟩ :=
  congrArg (fun e : D.Γ.Strand => (⟨e.1, e.2 + 1⟩ : D.Γ.Strand)) (tS_eq_self D x h)

theorem tS_pred_self (h : (sS D x).1 = (tS D x).1) :
    (⟨(tS D x).1, (tS D x).2 - 1⟩ : D.Γ.Strand) = ⟨(sS D x).1, bS D x - 1⟩ :=
  congrArg (fun e : D.Γ.Strand => (⟨e.1, e.2 - 1⟩ : D.Γ.Strand)) (tS_eq_self D x h)

theorem not_adjacent_aS_bS (h : (sS D x).1 = (tS D x).1) : ¬ adjacent (aS D x) (bS D x) := by
  intro had
  apply not_adjacent_sS_tS D x
  rw [tS_eq_self D x h]
  exact ⟨(sS D x).1, aS D x, bS D x, rfl, rfl, had⟩

theorem two_le_dd (h : (sS D x).1 = (tS D x).1) : 2 ≤ dd D x :=
  (two_le_val_sub_of_not_adjacent (not_adjacent_aS_bS D x h)).1

theorem dd_add_two_le (h : (sS D x).1 = (tS D x).1) : dd D x + 2 ≤ kI D x :=
  (two_le_val_sub_of_not_adjacent (not_adjacent_aS_bS D x h)).2

theorem dd_cast : (dd D x : ZMod (kI D x)) = bS D x - aS D x := ZMod.natCast_zmod_val _

/-- The vertex tuple of component `A`. -/
def tupleA : LabelledTuple (dd D x + 2) := fun m =>
  if m.val < dd D x then Pi D x (aS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = dd D x then tMinus D x ε
  else sPlus D x ε

/-- The vertex tuple of component `B`. -/
def tupleB : LabelledTuple (kI D x - dd D x + 2) := fun m =>
  if m.val < kI D x - dd D x then Pi D x (bS D x + 1 + (m.val : ZMod (kI D x)))
  else if m.val = kI D x - dd D x then sMinus D x ε
  else tPlus D x ε

def compA (h : (sS D x).1 = (tS D x).1) : PolyComp :=
  ⟨dd D x + 2, by have := two_le_dd D x h; omega, tupleA D x ε⟩

def compB (h : (sS D x).1 = (tS D x).1) : PolyComp :=
  ⟨kI D x - dd D x + 2, by have := dd_add_two_le D x h; omega, tupleB D x ε⟩

/-- The components of `D` other than that of `s` (`= t`). -/
def othersS : Finset (Fin D.Γ.c) := Finset.univ.erase (sS D x).1

theorem card_othersS : (othersS D x).card + 1 = D.Γ.c := by
  unfold othersS
  rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin]
  have := D.Γ.hc
  omega

/-- The self smoothed shadow: `A`, then `B`, then the untouched components. -/
def selfShadow (h : (sS D x).1 = (tS D x).1) : Shadow where
  c := (othersS D x).card + 2
  hc := by omega
  comp := Fin.cases (compA D x ε h)
    (Fin.cases (compB D x ε h) (fun l => D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)))

@[simp] theorem selfShadow_comp_zero (h : (sS D x).1 = (tS D x).1) :
    (selfShadow D x ε h).comp (0 : Fin ((othersS D x).card + 2)) = compA D x ε h := rfl

@[simp] theorem selfShadow_comp_one (h : (sS D x).1 = (tS D x).1) :
    (selfShadow D x ε h).comp (1 : Fin ((othersS D x).card + 2)) = compB D x ε h := rfl

@[simp] theorem selfShadow_comp_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card) :
    (selfShadow D x ε h).comp l.succ.succ = D.Γ.comp ((othersS D x).orderEmbOfFin rfl l) := rfl

/-- The kind of the edge with index `m` of component `A`. -/
def kindIdxA (m : ℕ) : StrandKind D x :=
  if m < dd D x - 1 then StrandKind.old ⟨(sS D x).1, aS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = dd D x - 1 then StrandKind.cutStartT
  else if m = dd D x then StrandKind.arcTS
  else StrandKind.cutEndS

/-- The kind of the edge with index `m` of component `B`. -/
def kindIdxB (m : ℕ) : StrandKind D x :=
  if m < kI D x - dd D x - 1 then StrandKind.old ⟨(sS D x).1, bS D x + 1 + (m : ZMod (kI D x))⟩
  else if m = kI D x - dd D x - 1 then StrandKind.cutStartS
  else if m = kI D x - dd D x then StrandKind.arcST
  else StrandKind.cutEndT

/-- The kind map of the self shadow. -/
def selfKind (h : (sS D x).1 = (tS D x).1) (u : (selfShadow D x ε h).Strand) : StrandKind D x :=
  Fin.cases (motive := fun l => ZMod ((selfShadow D x ε h).comp l).k → StrandKind D x)
    (fun m => kindIdxA D x m.val)
    (Fin.cases (motive := fun l => ZMod ((selfShadow D x ε h).comp l.succ).k → StrandKind D x)
      (fun m => kindIdxB D x m.val)
      (fun l m => StrandKind.old ⟨(othersS D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩)) u.1 u.2

/-! #### Index arithmetic for the self shadow (U5) -/

/-- Case analysis on the strands of the self shadow: `A`, `B`, or an untouched component. -/
theorem selfShadow_strand_cases (h : (sS D x).1 = (tS D x).1) {P : (selfShadow D x ε h).Strand → Prop}
    (h0 : ∀ m : ZMod (dd D x + 2), P ⟨(0 : Fin ((othersS D x).card + 2)), m⟩)
    (h1 : ∀ m : ZMod (kI D x - dd D x + 2), P ⟨(1 : Fin ((othersS D x).card + 2)), m⟩)
    (hs : ∀ (l : Fin (othersS D x).card)
      (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k), P ⟨l.succ.succ, m⟩)
    (u : (selfShadow D x ε h).Strand) : P u := by
  obtain ⟨l, m⟩ := u
  induction l using Fin.cases with
  | zero => exact h0 m
  | succ l =>
    induction l using Fin.cases with
    | zero => exact h1 m
    | succ l => exact hs l m

theorem selfKind_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ = kindIdxA D x m.val := rfl

theorem selfKind_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ = kindIdxB D x m.val := rfl

theorem selfKind_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    selfKind D x ε h ⟨l.succ.succ, m⟩ =
      StrandKind.old ⟨(othersS D x).orderEmbOfFin rfl l, (m.val : ZMod _)⟩ := rfl

theorem selfShadow_tail_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    (selfShadow D x ε h).tail ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ = tupleA D x ε m := rfl

theorem selfShadow_dir_zero (h : (sS D x).1 = (tS D x).1) (m : ZMod (dd D x + 2)) :
    (selfShadow D x ε h).dir ⟨(0 : Fin ((othersS D x).card + 2)), m⟩ =
      tupleA D x ε (m + 1) - tupleA D x ε m := rfl

theorem selfShadow_tail_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    (selfShadow D x ε h).tail ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ = tupleB D x ε m := rfl

theorem selfShadow_dir_one (h : (sS D x).1 = (tS D x).1) (m : ZMod (kI D x - dd D x + 2)) :
    (selfShadow D x ε h).dir ⟨(1 : Fin ((othersS D x).card + 2)), m⟩ =
      tupleB D x ε (m + 1) - tupleB D x ε m := rfl

theorem selfShadow_tail_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    (selfShadow D x ε h).tail ⟨l.succ.succ, m⟩ = D.Γ.tail ⟨(othersS D x).orderEmbOfFin rfl l, m⟩ := rfl

theorem selfShadow_dir_succ_succ (h : (sS D x).1 = (tS D x).1) (l : Fin (othersS D x).card)
    (m : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k) :
    (selfShadow D x ε h).dir ⟨l.succ.succ, m⟩ = D.Γ.dir ⟨(othersS D x).orderEmbOfFin rfl l, m⟩ := rfl

/-- The untouched components are not the component of `s` (`= t`). -/
theorem orderEmbOfFin_othersS_ne (l : Fin (othersS D x).card) :
    (othersS D x).orderEmbOfFin rfl l ≠ (sS D x).1 := by
  have := Finset.orderEmbOfFin_mem (othersS D x) rfl l
  simp only [othersS, Finset.mem_erase, Finset.mem_univ, and_true] at this
  exact this

/-- The four blocks of labels of `A` and of `B`. -/
theorem blockA (v : ℕ) (hv : v < dd D x + 2) :
    v < dd D x - 1 ∨ v = dd D x - 1 ∨ v = dd D x ∨ v = dd D x + 1 := by omega

theorem blockB (v : ℕ) (hv : v < kI D x - dd D x + 2) :
    v < kI D x - dd D x - 1 ∨ v = kI D x - dd D x - 1 ∨ v = kI D x - dd D x ∨
      v = kI D x - dd D x + 1 := by omega

theorem kindIdxA_of_lt {v : ℕ} (hv : v < dd D x - 1) :
    kindIdxA D x v = StrandKind.old ⟨(sS D x).1, aS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold kindIdxA; split_ifs; rfl

theorem kindIdxA_eq_cutStartT {v : ℕ} (hv : v = dd D x - 1) : kindIdxA D x v = StrandKind.cutStartT := by
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxA_eq_arcTS (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v = dd D x) :
    kindIdxA D x v = StrandKind.arcTS := by
  have := two_le_dd D x h
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxA_eq_cutEndS {v : ℕ} (hv : v = dd D x + 1) : kindIdxA D x v = StrandKind.cutEndS := by
  unfold kindIdxA; split_ifs <;> first | rfl | omega

theorem kindIdxB_of_lt {v : ℕ} (hv : v < kI D x - dd D x - 1) :
    kindIdxB D x v = StrandKind.old ⟨(sS D x).1, bS D x + 1 + (v : ZMod (kI D x))⟩ := by
  unfold kindIdxB; split_ifs; rfl

theorem kindIdxB_eq_cutStartS {v : ℕ} (hv : v = kI D x - dd D x - 1) :
    kindIdxB D x v = StrandKind.cutStartS := by
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem kindIdxB_eq_arcST (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v = kI D x - dd D x) :
    kindIdxB D x v = StrandKind.arcST := by
  have := dd_add_two_le D x h
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem kindIdxB_eq_cutEndT {v : ℕ} (hv : v = kI D x - dd D x + 1) :
    kindIdxB D x v = StrandKind.cutEndT := by
  unfold kindIdxB; split_ifs <;> first | rfl | omega

theorem tupleA_of_lt (m : ZMod (dd D x + 2)) (hv : m.val < dd D x) :
    tupleA D x ε m = Pi D x (aS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold tupleA; split_ifs; rfl

theorem tupleA_eq_tMinus (m : ZMod (dd D x + 2)) (hv : m.val = dd D x) :
    tupleA D x ε m = tMinus D x ε := by
  unfold tupleA; split_ifs <;> first | rfl | omega

theorem tupleA_eq_sPlus (m : ZMod (dd D x + 2)) (hv : m.val = dd D x + 1) :
    tupleA D x ε m = sPlus D x ε := by
  unfold tupleA; split_ifs <;> first | rfl | omega

theorem tupleB_of_lt (m : ZMod (kI D x - dd D x + 2)) (hv : m.val < kI D x - dd D x) :
    tupleB D x ε m = Pi D x (bS D x + 1 + (m.val : ZMod (kI D x))) := by
  unfold tupleB; split_ifs; rfl

theorem tupleB_eq_sMinus (m : ZMod (kI D x - dd D x + 2)) (hv : m.val = kI D x - dd D x) :
    tupleB D x ε m = sMinus D x ε := by
  unfold tupleB; split_ifs <;> first | rfl | omega

theorem tupleB_eq_tPlus (m : ZMod (kI D x - dd D x + 2)) (hv : m.val = kI D x - dd D x + 1) :
    tupleB D x ε m = tPlus D x ε := by
  unfold tupleB; split_ifs <;> first | rfl | omega

/-- `P (a + 1 + (d − 1)) = P b`: the last old vertex of `A` is the tail of `t`. -/
theorem Pi_bS_wrap (h : (sS D x).1 = (tS D x).1) :
    Pi D x (aS D x + 1 + ((dd D x - 1 : ℕ) : ZMod (kI D x))) = Pi D x (bS D x) := by
  have := two_le_dd D x h
  congr 1
  rw [zcast_pred (by omega), dd_cast]; ring

/-- `P (b + 1 + (k − d − 1)) = P a`: the last old vertex of `B` is the tail of `s`. -/
theorem Pi_aS_wrapB (h : (sS D x).1 = (tS D x).1) :
    Pi D x (bS D x + 1 + ((kI D x - dd D x - 1 : ℕ) : ZMod (kI D x))) = Pi D x (aS D x) := by
  have := dd_add_two_le D x h
  congr 1
  have e : kI D x - dd D x - 1 = kI D x - (dd D x + 1) := by omega
  rw [e, zcast_sub_self (by omega)]
  push_cast
  rw [dd_cast]; ring

/-- An old kind of `A` or `B` lies on the component of `s`. -/
theorem kindIdxA_old_fst (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < dd D x + 2) (e : D.Γ.Strand)
    (he : kindIdxA D x v = StrandKind.old e) : e.1 = (sS D x).1 := by
  rcases blockA D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxA_of_lt D x h1] at he; exact (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [kindIdxA_eq_cutStartT D x h1] at he; cases he
  · rw [kindIdxA_eq_arcTS D x h h1] at he; cases he
  · rw [kindIdxA_eq_cutEndS D x h1] at he; cases he

theorem kindIdxB_old_fst (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < kI D x - dd D x + 2)
    (e : D.Γ.Strand) (he : kindIdxB D x v = StrandKind.old e) : e.1 = (sS D x).1 := by
  rcases blockB D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxB_of_lt D x h1] at he; exact (congrArg Sigma.fst (StrandKind.old.inj he)).symm
  · rw [kindIdxB_eq_cutStartS D x h1] at he; cases he
  · rw [kindIdxB_eq_arcST D x h h1] at he; cases he
  · rw [kindIdxB_eq_cutEndT D x h1] at he; cases he

/-- A left inverse of the two kind maps `kindIdxA`, `kindIdxB`: component (`0` = `A`, `1` = `B`)
and label. -/
def selfCode : StrandKind D x → ℕ × ℕ
  | .old e =>
      if e.1 = (sS D x).1 then
        if (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x < dd D x - 1 then
          (0, (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x)
        else (1, (e.2.val + (kI D x - 1) - (aS D x).val) % kI D x - dd D x)
      else (2, 0)
  | .cutStartT => (0, dd D x - 1)
  | .arcTS => (0, dd D x)
  | .cutEndS => (0, dd D x + 1)
  | .cutStartS => (1, kI D x - dd D x - 1)
  | .arcST => (1, kI D x - dd D x)
  | .cutEndT => (1, kI D x - dd D x + 1)

theorem selfCode_kindIdxA (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < dd D x + 2) :
    selfCode D x (kindIdxA D x v) = (0, v) := by
  have hd := two_le_dd D x h
  have hd' := dd_add_two_le D x h
  rcases blockA D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxA_of_lt D x h1]
    simp only [selfCode, ↓reduceIte]
    rw [zmod_code_eq (aS D x) (by omega), ite_eq_left h1]
  · rw [kindIdxA_eq_cutStartT D x h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxA_eq_arcTS D x h h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxA_eq_cutEndS D x h1]; simp only [selfCode]; rw [h1]

theorem selfCode_kindIdxB (h : (sS D x).1 = (tS D x).1) {v : ℕ} (hv : v < kI D x - dd D x + 2) :
    selfCode D x (kindIdxB D x v) = (1, v) := by
  have hd := two_le_dd D x h
  have hd' := dd_add_two_le D x h
  rcases blockB D x v hv with h1 | h1 | h1 | h1
  · rw [kindIdxB_of_lt D x h1]
    simp only [selfCode, ↓reduceIte]
    have e : bS D x + 1 + (v : ZMod (kI D x)) = aS D x + 1 + ((dd D x + v : ℕ) : ZMod (kI D x)) := by
      push_cast; rw [dd_cast]; ring
    rw [e, zmod_code_eq (aS D x) (by omega), ite_eq_right (by omega)]
    congr 1; omega
  · rw [kindIdxB_eq_cutStartS D x h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxB_eq_arcST D x h h1]; simp only [selfCode]; rw [h1]
  · rw [kindIdxB_eq_cutEndT D x h1]; simp only [selfCode]; rw [h1]

theorem kindIdxA_inj (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < dd D x + 2)
    (hv' : v' < dd D x + 2) (heq : kindIdxA D x v = kindIdxA D x v') : v = v' := by
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxA D x h hv, selfCode_kindIdxA D x h hv'] at this
  exact (Prod.mk.inj this).2

theorem kindIdxB_inj (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < kI D x - dd D x + 2)
    (hv' : v' < kI D x - dd D x + 2) (heq : kindIdxB D x v = kindIdxB D x v') : v = v' := by
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxB D x h hv, selfCode_kindIdxB D x h hv'] at this
  exact (Prod.mk.inj this).2

theorem kindIdxA_ne_kindIdxB (h : (sS D x).1 = (tS D x).1) {v v' : ℕ} (hv : v < dd D x + 2)
    (hv' : v' < kI D x - dd D x + 2) : kindIdxA D x v ≠ kindIdxB D x v' := by
  intro heq
  have := congrArg (selfCode D x) heq
  rw [selfCode_kindIdxA D x h hv, selfCode_kindIdxB D x h hv'] at this
  exact absurd (Prod.mk.inj this).1 (by decide)

/-- The self shadow is a splice model. -/
def selfModel (h : (sS D x).1 = (tS D x).1) : SpliceModel D x ε (selfShadow D x ε h) where
  kind := selfKind D x ε h
  kind_injective := by
    show ∀ u u' : (selfShadow D x ε h).Strand, selfKind D x ε h u = selfKind D x ε h u' → u = u'
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_zero, selfKind_zero] at heq
        rw [ZMod.val_injective _ (kindIdxA_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro m' heq
        rw [selfKind_zero, selfKind_one] at heq
        exact absurd heq (kindIdxA_ne_kindIdxB D x h (ZMod.val_lt m) (ZMod.val_lt m'))
      · intro l' m' heq
        rw [selfKind_zero, selfKind_succ_succ] at heq
        exact absurd (kindIdxA_old_fst D x h (ZMod.val_lt m) _ heq) (orderEmbOfFin_othersS_ne D x l')
    · intro m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_one, selfKind_zero] at heq
        exact absurd heq.symm (kindIdxA_ne_kindIdxB D x h (ZMod.val_lt m') (ZMod.val_lt m))
      · intro m' heq
        rw [selfKind_one, selfKind_one] at heq
        rw [ZMod.val_injective _ (kindIdxB_inj D x h (ZMod.val_lt m) (ZMod.val_lt m') heq)]
      · intro l' m' heq
        rw [selfKind_one, selfKind_succ_succ] at heq
        exact absurd (kindIdxB_old_fst D x h (ZMod.val_lt m) _ heq) (orderEmbOfFin_othersS_ne D x l')
    · intro l m
      refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
      · intro m' heq
        rw [selfKind_succ_succ, selfKind_zero] at heq
        exact absurd (kindIdxA_old_fst D x h (ZMod.val_lt m') _ heq.symm) (orderEmbOfFin_othersS_ne D x l)
      · intro m' heq
        rw [selfKind_succ_succ, selfKind_one] at heq
        exact absurd (kindIdxB_old_fst D x h (ZMod.val_lt m') _ heq.symm) (orderEmbOfFin_othersS_ne D x l)
      · intro l' m' heq
        rw [selfKind_succ_succ, selfKind_succ_succ] at heq
        have h1 := StrandKind.old.inj heq
        rw [Sigma.mk.inj_iff] at h1
        obtain ⟨h1, h2⟩ := h1
        have hl : l = l' := ((othersS D x).orderEmbOfFin rfl).injective h1
        subst hl
        have h3 := eq_of_heq h2
        simp only [ZMod.natCast_zmod_val] at h3
        rw [h3]
  kind_surj := by
    intro κ hκ
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    cases κ with
    | old e =>
      obtain ⟨hs, ht⟩ := hκ
      have hs' : e ≠ sS D x := fun h' => hs (by rw [h'])
      have ht' : e ≠ tS D x := fun h' => ht (by rw [h'])
      rw [tS_eq_self D x h] at ht'
      obtain ⟨l₀, c⟩ := e
      by_cases hi : l₀ = (sS D x).1
      · subst hi
        have hca : c ≠ aS D x := fun h' => hs' (Sigma.ext rfl (heq_of_eq h'))
        have hcb : c ≠ bS D x := fun h' => ht' (Sigma.ext rfl (heq_of_eq h'))
        obtain ⟨w, hw⟩ : ∃ w, w = (c - aS D x).val := ⟨_, rfl⟩
        have hw1 : w < kI D x := by rw [hw]; exact ZMod.val_lt _
        have hwc : (w : ZMod (kI D x)) = c - aS D x := by rw [hw, ZMod.natCast_zmod_val]
        have hw0 : w ≠ 0 := by
          intro h0
          apply hca
          rw [h0, Nat.cast_zero] at hwc
          linear_combination -hwc
        have hwd : w ≠ dd D x := by
          intro h0
          apply hcb
          rw [h0, dd_cast] at hwc
          linear_combination -hwc
        rcases Nat.lt_or_gt_of_ne hwd with hlt | hgt
        · refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((w - 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
          rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega), kindIdxA_of_lt D x (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred (by omega), hwc]; ring
        · refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
            ((w - dd D x - 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
          rw [selfKind_one, ZMod.val_natCast_of_lt (by omega), kindIdxB_of_lt D x (by omega)]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          have e : w - dd D x - 1 = w - (dd D x + 1) := by omega
          rw [e, Nat.cast_sub (by omega)]
          push_cast
          rw [hwc, dd_cast]; ring
      · have hmem : l₀ ∈ othersS D x := by
          simp only [othersS, Finset.mem_erase, Finset.mem_univ, and_true]
          exact hi
        have hrange : l₀ ∈ Set.range ((othersS D x).orderEmbOfFin rfl) := by
          rw [Finset.range_orderEmbOfFin]; exact hmem
        obtain ⟨l, hl⟩ := hrange
        subst hl
        exact ⟨⟨l.succ.succ, c⟩, by rw [selfKind_succ_succ, ZMod.natCast_zmod_val]⟩
    | cutStartS =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x - 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_cutStartS D x rfl
    | cutEndS =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x + 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_cutEndS D x rfl
    | cutStartT =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x - 1 : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_cutStartT D x rfl
    | cutEndT =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x + 1 : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_cutEndT D x rfl
    | arcST =>
      refine ⟨⟨(1 : Fin ((othersS D x).card + 2)),
        ((kI D x - dd D x : ℕ) : ZMod (kI D x - dd D x + 2))⟩, ?_⟩
      rw [selfKind_one, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxB_eq_arcST D x h rfl
    | arcTS =>
      refine ⟨⟨(0 : Fin ((othersS D x).card + 2)), ((dd D x : ℕ) : ZMod (dd D x + 2))⟩, ?_⟩
      rw [selfKind_zero, ZMod.val_natCast_of_lt (by omega)]
      exact kindIdxA_eq_arcTS D x h rfl
  kind_occurs := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv]
        refine StrandKind.occurs_old ?_ ?_
        · intro heq
          have heq2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
              ⟨(sS D x).1, (sS D x).2⟩ := heq
          have heq' := Strand_mk_eq_mk_iff.mp heq2
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        · intro heq
          rw [tS_eq_self D x h] at heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = (dd D x : ZMod (kI D x)) := by
            push_cast; rw [dd_cast]; linear_combination heq'
          have := nat_eq_of_zcast_eq (by omega) (by omega) h2
          omega
      · rw [kindIdxA_eq_cutStartT D x hv]; exact StrandKind.occurs_cutStartT
      · rw [kindIdxA_eq_arcTS D x h hv]; exact StrandKind.occurs_arcTS
      · rw [kindIdxA_eq_cutEndS D x hv]; exact StrandKind.occurs_cutEndS
    · intro m
      rw [selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv]
        refine StrandKind.occurs_old ?_ ?_
        · intro heq
          have heq2 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) =
              ⟨(sS D x).1, (sS D x).2⟩ := heq
          have heq' := Strand_mk_eq_mk_iff.mp heq2
          have h2 : ((m.val + 1 + dd D x : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; rw [dd_cast]; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        · intro heq
          rw [tS_eq_self D x h] at heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + 1 : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
      · rw [kindIdxB_eq_cutStartS D x hv]; exact StrandKind.occurs_cutStartS
      · rw [kindIdxB_eq_arcST D x h hv]; exact StrandKind.occurs_arcST
      · rw [kindIdxB_eq_cutEndT D x hv]; exact StrandKind.occurs_cutEndT
    · intro l m
      rw [selfKind_succ_succ]
      have hne := orderEmbOfFin_othersS_ne D x l
      exact StrandKind.occurs_old (Strand_mk_ne_mk_of_ne hne)
        (Strand_mk_ne_mk_of_ne (fun heq => hne (heq.trans h.symm)))
  kind_pred := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      show selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), (m - 1 : ZMod (dd D x + 2))⟩ =
        (selfKind D x ε h ⟨(0 : Fin ((othersS D x).card + 2)), m⟩).pred
      rw [selfKind_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv]
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, kindIdxA_eq_cutEndS D x (by omega), h0, Nat.cast_zero,
            add_zero]
          simp only [StrandKind.pred, ↓reduceIte]
        · rw [zval_sub_one_of_pos m h0, kindIdxA_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne1 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          have hne2 : (⟨(sS D x).1, aS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, bS D x + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = (dd D x : ZMod (kI D x)) := by
              rw [dd_cast]; linear_combination heq'
            have := nat_eq_of_zcast_eq (by omega) (by omega) h2
            omega
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartT at `d − 1`: predecessor `old ⟨i, b − 1⟩` at `d − 2`
        rw [kindIdxA_eq_cutStartT D x hv, zval_sub_one_of_pos m (by omega), hv,
          kindIdxA_of_lt D x (by omega)]
        simp only [StrandKind.pred]
        rw [tS_pred_self D x h]
        simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have e : dd D x - 1 - 1 = dd D x - 2 := by omega
        rw [e, Nat.cast_sub (by omega)]
        push_cast
        rw [dd_cast]; ring
      · rw [kindIdxA_eq_arcTS D x h hv, zval_sub_one_of_pos m (by omega),
          kindIdxA_eq_cutStartT D x (by omega)]; rfl
      · rw [kindIdxA_eq_cutEndS D x hv, zval_sub_one_of_pos m (by omega),
          kindIdxA_eq_arcTS D x h (by omega)]; rfl
    · intro m
      show selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), (m - 1 : ZMod (kI D x - dd D x + 2))⟩ =
        (selfKind D x ε h ⟨(1 : Fin ((othersS D x).card + 2)), m⟩).pred
      rw [selfKind_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv]
        have hne1 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
            ⟨(sS D x).1, (sS D x).2 + 1⟩ := by
          intro heq
          have heq' := Strand_mk_eq_mk_iff.mp heq
          have h2 : ((m.val + dd D x : ℕ) : ZMod (kI D x)) = 0 := by
            push_cast; rw [dd_cast]; linear_combination heq'
          exact zcast_ne_zero_of_lt (by omega) (by omega) h2
        rcases Nat.eq_zero_or_pos m.val with h0 | h0
        · rw [zval_sub_one_of_zero m h0, kindIdxB_eq_cutEndT D x (by omega)]
          rw [h0, Nat.cast_zero, add_zero] at hne1 ⊢
          simp only [StrandKind.pred]
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_left rfl]
        · rw [zval_sub_one_of_pos m h0, kindIdxB_of_lt D x (by omega)]
          simp only [StrandKind.pred]
          have hne2 : (⟨(sS D x).1, bS D x + 1 + (m.val : ZMod (kI D x))⟩ : D.Γ.Strand) ≠
              ⟨(sS D x).1, bS D x + 1⟩ := by
            intro heq
            have heq' := Strand_mk_eq_mk_iff.mp heq
            have h2 : (m.val : ZMod (kI D x)) = 0 := by linear_combination heq'
            exact zcast_ne_zero_of_lt h0 (by omega) h2
          rw [ite_eq_right hne1, tS_succ_self D x h, ite_eq_right hne2]
          simp only [StrandKind.old.injEq, Strand_mk_eq_mk_iff]
          rw [zcast_pred h0]; ring
      · -- cutStartS at `k − d − 1`: predecessor `old ⟨i, a − 1⟩` at `k − d − 2`
        rw [kindIdxB_eq_cutStartS D x hv, zval_sub_one_of_pos m (by omega), hv,
          kindIdxB_of_lt D x (by omega)]
        simp only [StrandKind.pred, StrandKind.old.injEq, Strand_mk_eq_mk_iff]
        have e : kI D x - dd D x - 1 - 1 = kI D x - (dd D x + 2) := by omega
        rw [e, zcast_sub_self (by omega)]
        push_cast
        rw [dd_cast]; ring
      · rw [kindIdxB_eq_arcST D x h hv, zval_sub_one_of_pos m (by omega),
          kindIdxB_eq_cutStartS D x (by omega)]; rfl
      · rw [kindIdxB_eq_cutEndT D x hv, zval_sub_one_of_pos m (by omega),
          kindIdxB_eq_arcST D x h (by omega)]; rfl
    · intro l m
      show selfKind D x ε h ⟨l.succ.succ, (m - 1 : ZMod (D.Γ.comp ((othersS D x).orderEmbOfFin rfl l)).k)⟩ =
        (selfKind D x ε h ⟨l.succ.succ, m⟩).pred
      rw [selfKind_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.pred, ZMod.natCast_zmod_val]
      have hne := orderEmbOfFin_othersS_ne D x l
      rw [ite_eq_right (Strand_mk_ne_mk_of_ne hne),
        ite_eq_right (Strand_mk_ne_mk_of_ne (fun heq => hne (heq.trans h.symm)))]
  tail_eq := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfShadow_tail_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxA_of_lt D x hv, tupleA_of_lt D x ε m (by omega)]; rfl
      · rw [kindIdxA_eq_cutStartT D x hv, tupleA_of_lt D x ε m (by omega), hv, Pi_bS_wrap D x h]
        exact (tail_tS_self D x h).symm
      · rw [kindIdxA_eq_arcTS D x h hv, tupleA_eq_tMinus D x ε m hv]; rfl
      · rw [kindIdxA_eq_cutEndS D x hv, tupleA_eq_sPlus D x ε m hv]; rfl
    · intro m
      rw [selfShadow_tail_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · rw [kindIdxB_of_lt D x hv, tupleB_of_lt D x ε m (by omega)]; rfl
      · rw [kindIdxB_eq_cutStartS D x hv, tupleB_of_lt D x ε m (by omega), hv, Pi_aS_wrapB D x h]; rfl
      · rw [kindIdxB_eq_arcST D x h hv, tupleB_eq_sMinus D x ε m hv]; rfl
      · rw [kindIdxB_eq_cutEndT D x hv, tupleB_eq_tPlus D x ε m hv]; rfl
    · intro l m
      rw [selfShadow_tail_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.tail, ZMod.natCast_zmod_val]
  dir_eq := by
    have hk := three_le_kI D x
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m
      rw [selfShadow_dir_zero, selfKind_zero]
      have hmv := ZMod.val_lt m
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_of_lt D x hv, tupleA_of_lt D x ε (m + 1) (by omega),
          tupleA_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_eq_cutStartT D x hv, tupleA_eq_tMinus D x ε (m + 1) (by omega),
          tupleA_of_lt D x ε m (by omega), hv, Pi_bS_wrap D x h]
        simp only [StrandKind.dir, tMinus]
        rw [pt_eq_t_self D x h]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxA_eq_arcTS D x h hv, tupleA_eq_sPlus D x ε (m + 1) (by omega),
          tupleA_eq_tMinus D x ε m hv]
        simp only [StrandKind.dir, sPlus, tMinus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [kindIdxA_eq_cutEndS D x hv, tupleA_of_lt D x ε (m + 1) (by omega),
          tupleA_eq_sPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, sPlus]
        rw [pt_eq_s, tail_sS, es_eq]; module
    · intro m
      rw [selfShadow_dir_one, selfKind_one]
      have hmv := ZMod.val_lt m
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_of_lt D x hv, tupleB_of_lt D x ε (m + 1) (by omega),
          tupleB_of_lt D x ε m (by omega), h1, Nat.cast_succ]
        simp only [StrandKind.dir, Shadow.dir_mk, edge, add_assoc]
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_eq_cutStartS D x hv, tupleB_eq_sMinus D x ε (m + 1) (by omega),
          tupleB_of_lt D x ε m (by omega), hv, Pi_aS_wrapB D x h]
        simp only [StrandKind.dir, sMinus]
        rw [pt_eq_s, tail_sS]; module
      · have h1 := zval_add_one_of_lt m (by omega)
        rw [kindIdxB_eq_arcST D x h hv, tupleB_eq_tPlus D x ε (m + 1) (by omega),
          tupleB_eq_sMinus D x ε m hv]
        simp only [StrandKind.dir, sMinus, tPlus]; module
      · have h1 := zval_add_one_of_eq m (by omega)
        rw [kindIdxB_eq_cutEndT D x hv, tupleB_of_lt D x ε (m + 1) (by omega),
          tupleB_eq_tPlus D x ε m hv, h1, Nat.cast_zero, add_zero]
        simp only [StrandKind.dir, tPlus]
        rw [pt_eq_t_self D x h, et_self D x h]; module
    · intro l m
      rw [selfShadow_dir_succ_succ, selfKind_succ_succ]
      simp only [StrandKind.dir, ZMod.natCast_zmod_val]
  cut_val := by
    have hd := two_le_dd D x h
    have hd' := dd_add_two_le D x h
    refine selfShadow_strand_cases D x ε h ?_ ?_ ?_
    · intro m hm
      rw [selfKind_zero] at hm
      have hmv := ZMod.val_lt m
      show m.val + 2 < dd D x + 2
      rcases blockA D x m.val hmv with hv | hv | hv | hv
      · omega
      · omega
      · rw [kindIdxA_eq_arcTS D x h hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [kindIdxA_eq_cutEndS D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro m hm
      rw [selfKind_one] at hm
      have hmv := ZMod.val_lt m
      show m.val + 2 < kI D x - dd D x + 2
      rcases blockB D x m.val hmv with hv | hv | hv | hv
      · omega
      · omega
      · rw [kindIdxB_eq_arcST D x h hv] at hm; rcases hm with hm | hm <;> cases hm
      · rw [kindIdxB_eq_cutEndT D x hv] at hm; rcases hm with hm | hm <;> cases hm
    · intro l m hm
      rw [selfKind_succ_succ] at hm
      rcases hm with hm | hm <;> cases hm

/-! ### 7c. The smoothed diagram -/

/-- **The smoothed diagram** `D₀` of `D` at `x` with cut parameter `ε`. -/
def smoothDiagram (hε : SmallEps D x ε) : Diagram :=
  if h : (sS D x).1 = (tS D x).1 then toDiagram D x (selfModel D x ε h) hε
  else toDiagram D x (mixedModel D x ε h) hε

theorem isOrientedSmoothing_smoothDiagram (hε : SmallEps D x ε) :
    IsOrientedSmoothing D x (smoothDiagram D x ε hε) := by
  unfold smoothDiagram
  split_ifs with h
  · exact isOrientedSmoothing_toDiagram D x (selfModel D x ε h) hε
  · exact isOrientedSmoothing_toDiagram D x (mixedModel D x ε h) hε

/-- Component count by construction: `c + 1` (self) or `c − 1` (mixed). -/
theorem smoothDiagram_componentCount (hε : SmallEps D x ε) :
    (smoothDiagram D x ε hε).componentCount =
      if (sS D x).1 = (tS D x).1 then D.componentCount + 1 else D.componentCount - 1 := by
  unfold smoothDiagram
  split_ifs with h
  · show (othersS D x).card + 2 = D.Γ.c + 1
    have := card_othersS D x; omega
  · show (othersM D x).card + 1 = D.Γ.c - 1
    have := card_othersM D x h; omega

/-! ## 8. The record bridge

For a splice model, the occurrences of `D₀` are the occurrences of `D` at crossings other than `x`
(`origVisit`); pairing, bits and signs transport strand-wise; the components of `D₀` are the
`Record.SmoothComps` of `D.record` at the over occurrence (a bijective classification `cls`,
explicit per case); and the successor of `D₀` is the first return of the reconnected successor
(`Record.smoothSucc`).  The successor law is proved **once**, at the model level
(`succ_of_coord`), from three ingredients grafted from tag B:
* the *smoothed coordinate* `key` on the occurrences of `D` (forward distance from `xv` on the
  circle of `s`, `k_i +` forward distance from `τ xv` on the circle of `t`, plain coordinate
  elsewhere), on whose retained values the reconnected successor is the cyclic successor
  (`reconnect_no_between`, stated for `rkey = key ∘ swap(xv, τxv)` so that the two erased
  occurrences sit at their cyclic positions);
* the general first-return lemma `firstReturn_no_between` (§0');
* per concrete model, the statement that the traversal coordinate of `D₀`, rotated on each
  component so that the cut-end piece comes first (`mixedBase`, `selfBase`), is a strictly
  increasing function of `key ∘ origVisit` (`mixed_key_lt_iff`, `self_key_lt_iff`).
Then `cycNext_unique_on` in `D₀` identifies `D₀.nextVisit` with `smoothSucc`, exactly as in
`Diagram.restrictVisit_nextVisit` (LinkDiagramRecord 1344-1452). -/

/-! ### 8-pre. The smoothed coordinate of `D`'s occurrences -/

/-- The over occurrence of `x`, the erased occurrence of `Record.smooth`. -/
abbrev xv : D.Γ.Visit := D.overVisit x

/-- `τ xv` is the under occurrence (by `rfl`). -/
theorem record_pair_xv : D.record.pair (xv D x) = D.underVisit x := rfl

/-- The reconnected successor `s₁ = s ∘ swap(xv, τ xv)`, unfolded (by `rfl`). -/
theorem reconnect_xv_apply (v : D.Γ.Visit) :
    D.record.reconnect (xv D x) v = D.nextVisit (Equiv.swap (xv D x) (D.underVisit x) v) := rfl

/-- The smoothed coordinate of an occurrence of `D` (tag B's `smB_off`): on the circle of `s` the
forward distance from the over occurrence, on the circle of `t` (mixed case) `k_i +` the forward
distance from the under occurrence, and the plain traversal coordinate elsewhere.  In the self
case (`i = j`) the first branch applies to both words. -/
def key (v : D.Γ.Visit) : ℝ :=
  if D.compOf v = (sS D x).1 then
    Diagram.cyclicOffset (kI D x) (D.visitCoord (xv D x)) (D.visitCoord v)
  else if D.compOf v = (tS D x).1 then
    (kI D x : ℝ) + Diagram.cyclicOffset (kJ D x) (D.visitCoord (D.underVisit x)) (D.visitCoord v)
  else D.visitCoord v

/-- The reconnect coordinate: `key` with the two erased occurrences exchanged.  `s₁` sends the last
retained occurrence before `xv` to `xv` itself, whose cyclic position on the merged/split cycle is
that of `τ xv` (and vice versa); the swap puts them there. -/
def rkey (v : D.Γ.Visit) : ℝ := key D x (Equiv.swap (xv D x) (D.underVisit x) v)

theorem rkey_of_smoothKeep (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) :
    rkey D x v = key D x v := by
  sorry

/-- `key` is injective on each `s₁`-cycle (on the circle of `s`: `cyclicOffset` is a bijection of
`[0,k_i)`; mixed case: the shift `k_i` separates the two circles; elsewhere `visitCoord_injOn`). -/
theorem rkey_injOn (v u : D.Γ.Visit) (hu : (D.record.reconnect (xv D x)).SameCycle u v)
    (he : rkey D x u = rkey D x v) : u = v := by
  sorry

/-- **`s₁` is the cyclic successor for `rkey` on each of its cycles.**  Away from `xv, τ xv`:
`s₁ v = succ v` and `nextVisit_no_between` transported by the rotation (`rexPL_rot_eq_cyclicOffset`,
`rexB_cycBetween_rot`), the other circle (mixed case) being shifted out of the way; at `xv`:
`s₁ xv = succ (τ xv)`, `rkey xv = key (τ xv)` and the retained occurrences after `τ xv` have larger
keys; at `τ xv`: symmetric. -/
theorem reconnect_no_between (v u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) :
    ¬ cycBetween (rkey D x v) (rkey D x u) (rkey D x (D.record.reconnect (xv D x) v)) := by
  sorry

/-- No retained occurrence of the cycle lies strictly between a retained `v` and its smoothed
successor (`firstReturn_no_between` applied to `s₁`, `SmoothKeep`, `rkey`). -/
theorem smoothSucc_no_between (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) (u : D.Γ.Visit)
    (hu : (D.record.reconnect (xv D x)).SameCycle u v) (hu' : D.record.SmoothKeep (xv D x) u) :
    ¬ cycBetween (key D x v) (key D x u)
      (key D x ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).1) := by
  have h := firstReturn_no_between (D.record.reconnect (xv D x)) (D.record.SmoothKeep (xv D x))
    (rkey D x) (rkey_injOn D x) (reconnect_no_between D x) ⟨v, hv⟩ u hu hu'
  rw [rkey_of_smoothKeep D x v hv, rkey_of_smoothKeep D x u hu'] at h
  have h3 : rkey D x ((firstReturn (D.record.reconnect (xv D x)) (D.record.SmoothKeep (xv D x))
      ⟨v, hv⟩).1) = key D x ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).1 :=
    rkey_of_smoothKeep D x _ ((D.record.smooth (xv D x)).succ ⟨v, hv⟩).2
  rw [h3] at h
  exact h

/-- Self case: the `s₁`-cycle of `τ xv` consists of `τ xv` and the occurrences of the circle met
strictly after `xv` and strictly before `τ xv` (the word `A` of `(x A y B)`).  Proof: the set on the
right is `s₁`-closed (`nextVisit_no_between` and cyclic trichotomy), contains `τ xv`, and its
complement in the circle is `s₁`-closed and contains `xv`; `reconnect_sameCycle_or` finishes. -/
theorem self_sameCycle_pair_iff (h : (sS D x).1 = (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = (sS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle w (D.underVisit x) ↔
      w = D.underVisit x ∨
        cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x)) := by
  sorry

/-- Untouched circles: the `s₁`-cycles are the old circles. -/
theorem sameCycle_of_comp_ne (v w : D.Γ.Visit) (hv : D.compOf v ≠ (sS D x).1)
    (hv' : D.compOf v ≠ (tS D x).1) :
    (D.record.reconnect (xv D x)).SameCycle v w ↔ D.compOf v = D.compOf w := by
  sorry

/-- A rotated strictly monotone coordinate on each component transports the oriented cyclic order
of a diagram (`rexB_cycBetween_rot`, then `cycBetween` is three strict inequalities). -/
theorem visitBetween_iff_of_rot_lt_iff (D₀ : Diagram) (κ : D₀.Γ.Visit → ℝ) (c₀ : Fin D₀.Γ.c → ℝ)
    (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((D₀.Γ.comp l).k : ℝ))
    (hlt : ∀ v w, D₀.compOf v = D₀.compOf w →
      (rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord v) <
        rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord w) ↔ κ v < κ w))
    (v u w : D₀.Γ.Visit) (hu : D₀.compOf u = D₀.compOf v) (hw : D₀.compOf w = D₀.compOf v) :
    D₀.VisitBetween v u w ↔ cycBetween (κ v) (κ u) (κ w) := by
  sorry

section RecordBridge

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-- The occurrence of `D` under an occurrence of `Γ₀`. -/
def origVisit (v : Γ₀.Visit) : D.Γ.Visit :=
  ⟨origCrossing D x M hε v.1, ⟨M.orig v.2.val, orig_mem_origCrossing D x M hε v.2.2⟩⟩

theorem origVisit_fst (v : Γ₀.Visit) : (origVisit D x M hε v).1 = origCrossing D x M hε v.1 := rfl

theorem origVisit_injective : Function.Injective (origVisit D x M hε) := by
  sorry

/-- Occurrences of `Γ₀` sit at crossings other than `x`: they are retained by `Record.smooth`. -/
theorem smoothKeep_origVisit (v : Γ₀.Visit) : D.record.SmoothKeep (xv D x) (origVisit D x M hε v) := by
  sorry

theorem exists_origVisit (w : D.Γ.Visit) (hw : D.record.SmoothKeep (xv D x) w) :
    ∃ v, origVisit D x M hε v = w := by
  sorry

/-- The occurrences of `D₀` are the retained occurrences of `D`. -/
def visitEquiv : Γ₀.Visit ≃ {w : D.Γ.Visit // D.record.SmoothKeep (xv D x) w} :=
  Equiv.ofBijective (fun v => ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    ⟨fun v w h => origVisit_injective D x M hε (congrArg Subtype.val h),
     fun w => by
      obtain ⟨v, hv⟩ := exists_origVisit D x M hε w.1 w.2
      exact ⟨v, Subtype.ext hv⟩⟩

theorem twin_origVisit (v : Γ₀.Visit) :
    D.twin (origVisit D x M hε v) = origVisit D x M hε ((toDiagram D x M hε).twin v) := by
  sorry

theorem overBit_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).overBit v = D.overBit (origVisit D x M hε v) := by
  sorry

theorem sign_origVisit (v : Γ₀.Visit) :
    (toDiagram D x M hε).sign v.1 = D.sign (origVisit D x M hε v).1 :=
  toDiagram_sign D x M hε v.1

/-- The traversal coordinate of an occurrence of `D₀` under `origVisit`: the original parameter is
the rescaled one (`crossingParam_toDiagram`), so `visitCoord (origVisit v) = label(orig).val +
origParam (param₀ v)`. -/
theorem visitCoord_origVisit (v : Γ₀.Visit) :
    D.visitCoord (origVisit D x M hε v) =
      ((M.orig v.2.val).2.val : ℝ) +
        (M.kind v.2.val).origParam ε ((toDiagram D x M hε).crossingParam v.1 v.2.2) := by
  sorry

/-- **Assembly of the record isomorphism** from a component classification `cls` and the
successor law. -/
def recordIsoOfCls (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Bijective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (hsucc : ∀ v : Γ₀.Visit, origVisit D x M hε ((toDiagram D x M hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1) :
    RecordIso (toDiagram D x M hε).record (D.record.smooth (xv D x)) where
  e := Equiv.ofBijective cls hcls
  Φ := visitEquiv D x M hε
  comp_eq v := (hcls_visit v).symm
  succ_eq v := Subtype.ext (hsucc v)
  pair_eq v := Subtype.ext (twin_origVisit D x M hε v).symm
  bit_eq v := (overBit_origVisit D x M hε v).symm
  sgn_eq v := (sign_origVisit D x M hε v).symm

/-- Same component of `D₀` iff same `s₁`-cycle of the original occurrences (from an injective
classification compatible with `origVisit`, via `Record.smooth_comp_eq_iff`). -/
theorem compOf_eq_iff_of_cls (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Injective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (v w : Γ₀.Visit) :
    (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w ↔
      (D.record.reconnect (xv D x)).SameCycle (origVisit D x M hε v) (origVisit D x M hε w) := by
  sorry

/-- **The successor law from a rotated monotone coordinate** (the one proof of the successor law,
shared by both cases; template `Diagram.restrictVisit_nextVisit`).  If, on every component of `D₀`,
the traversal coordinate rotated by `c₀` is a strictly increasing function of `key ∘ origVisit`,
then the successor of `D₀` is the smoothed successor.  Proof: if `v` is alone on its component both
sides are `v` (`nextVisit_eq_self`, first return to the only retained element of the cycle);
otherwise `cycNext_unique_on` in `D₀` with `p := same component as v`, `k := D₀.visitCoord`,
candidates `D₀.nextVisit v` (`nextVisit_no_between`, `nextVisit_ne_self`) and the `origVisit`-preimage
of `smoothSucc (origVisit v)` (same component by `compOf_eq_iff_of_cls` + `Record.succ_comp`; no
occurrence between by `smoothSucc_no_between` transported through `visitBetween_iff_of_rot_lt_iff`). -/
theorem succ_of_coord (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Injective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (c₀ : Fin Γ₀.c → ℝ) (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((Γ₀.comp l).k : ℝ))
    (hlt : ∀ v w : Γ₀.Visit, (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w →
      (rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord v) <
        rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord w) ↔
        key D x (origVisit D x M hε v) < key D x (origVisit D x M hε w)))
    (v : Γ₀.Visit) :
    origVisit D x M hε ((toDiagram D x M hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1 := by
  sorry

/-- The record isomorphism from a classification and a rotated monotone coordinate. -/
def recordIsoOfCoord (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)
    (hcls : Function.Bijective cls)
    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =
      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)
    (c₀ : Fin Γ₀.c → ℝ) (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((Γ₀.comp l).k : ℝ))
    (hlt : ∀ v w : Γ₀.Visit, (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w →
      (rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord v) <
        rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord w) ↔
        key D x (origVisit D x M hε v) < key D x (origVisit D x M hε w))) :
    RecordIso (toDiagram D x M hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCls D x M hε cls hcls hcls_visit
    (succ_of_coord D x M hε cls hcls.1 hcls_visit c₀ hc₀ hlt)

end RecordBridge

/-! ### 8a. Component classification and rotated coordinate, per case -/

/-- The `SmoothComps` class of an untouched component `i₀` of `D`: the reconnect-cycle of any of
its occurrences, or the crossing-free circle `i₀`. -/
def oldCls (i₀ : Fin D.Γ.c) : (D.record.smooth (xv D x)).comps :=
  if h : ∃ w : D.Γ.Visit, D.compOf w = i₀ then Sum.inl (Quotient.mk _ (Classical.choose h))
  else Sum.inr ⟨i₀, fun w hw => h ⟨w, hw⟩⟩

/-- On an untouched component `i₀ ∉ {i, j}` the class of every occurrence is `oldCls i₀`. -/
theorem oldCls_eq (i₀ : Fin D.Γ.c) (hi : i₀ ≠ (sS D x).1) (hj : i₀ ≠ (tS D x).1) (w : D.Γ.Visit)
    (hw : D.compOf w = i₀) : oldCls D x i₀ = Sum.inl (Quotient.mk _ w) := by
  sorry

section MixedRecord

/-- The class map of the mixed case: the merged component is the reconnect-cycle of `x`
(`= ⟦τx⟧`, `Record.reconnect_sameCycle_pair_of_mixed`). -/
def mixedCls : Fin ((othersM D x).card + 1) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
    (fun l => oldCls D x ((othersM D x).orderEmbOfFin rfl l))

/-- The rotation base of the mixed shadow: on the merged component the cut-end piece `[s⁺, P_i(a+1)]`
sits at the last label `N − 1` and is where the smoothed order starts; untouched components are not
rotated. -/
def mixedBase : Fin ((othersM D x).card + 1) → ℝ :=
  Fin.cases ((kI D x + kJ D x + 3 : ℕ) : ℝ) (fun _ => 0)

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 ≠ (tS D x).1)

omit hε in
theorem mixedBase_mem (l : Fin ((othersM D x).card + 1)) :
    0 ≤ mixedBase D x l ∧ mixedBase D x l < (((mixedShadow D x ε).comp l).k : ℝ) := by
  sorry

include h in
theorem mixedCls_bijective : Function.Bijective (mixedCls D x) := by
  sorry

theorem mixedCls_visit (v : (mixedShadow D x ε).Visit) :
    mixedCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (mixedModel D x ε h) hε v, smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩ := by
  sorry

/-- The smoothed coordinate on the merged component, block by block (`m = v.2.val.2.val` the label,
`θ = param₀`): old `i`-edges `m < k_i − 1 ↦ m + 1 + θ − τs`; `cutStartS ↦ k_i − τs + θ(τs − ε)`;
`cutEndT ↦ k_i + ε + θ(1 − τt − ε)`; old `j`-edges `↦ m − 1 + θ − τt`; `cutStartT ↦ k_i + k_j − τt +
θ(τt − ε)`; `cutEndS ↦ ε + θ(1 − τs − ε)`.  Each block is affine with positive slope, the blocks are
increasing in label order except the last, which is the smallest: hence the rotation by `N − 1`. -/
theorem mixed_key_lt_iff (v w : (mixedShadow D x ε).Visit)
    (hc : (toDiagram D x (mixedModel D x ε h) hε).compOf v =
      (toDiagram D x (mixedModel D x ε h) hε).compOf w) :
    (rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)
        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) <
      rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)
        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord w) ↔
      key D x (origVisit D x (mixedModel D x ε h) hε v) <
        key D x (origVisit D x (mixedModel D x ε h) hε w)) := by
  sorry

/-- The record bridge, mixed case. -/
def mixedRecordIso :
    RecordIso (toDiagram D x (mixedModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCoord D x (mixedModel D x ε h) hε (mixedCls D x) (mixedCls_bijective D x h)
    (mixedCls_visit D x hε h) (mixedBase D x) (mixedBase_mem D x) (mixed_key_lt_iff D x hε h)

end MixedRecord

section SelfRecord

/-- The class map of the self case: `A ↦ ⟦τx⟧` (occurrences after `x`, before `τx`),
`B ↦ ⟦x⟧`. -/
def selfCls : Fin ((othersS D x).card + 2) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (D.record.pair (xv D x))))
    (Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
      (fun l => oldCls D x ((othersS D x).orderEmbOfFin rfl l)))

/-- The rotation bases of the self shadow: on `A` the cut-end piece `[s⁺, P(a+1)]` sits at label
`d + 1`, on `B` the cut-end piece `[t⁺, P(b+1)]` at label `k − d + 1`. -/
def selfBase : Fin ((othersS D x).card + 2) → ℝ :=
  Fin.cases ((dd D x + 1 : ℕ) : ℝ) (Fin.cases ((kI D x - dd D x + 1 : ℕ) : ℝ) (fun _ => 0))

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 = (tS D x).1)

omit hε in
theorem selfBase_mem (l : Fin ((othersS D x).card + 2)) :
    0 ≤ selfBase D x l ∧ selfBase D x l < (((selfShadow D x ε h).comp l).k : ℝ) := by
  sorry

include h in
theorem selfCls_bijective : Function.Bijective (selfCls D x) := by
  sorry

/-- `A`'s occurrences are on the `s₁`-cycle of `τ xv` and `B`'s on that of `xv`
(`self_sameCycle_pair_iff`, `reconnect_sameCycle_or`, `smooth_comps_ne_of_self`). -/
theorem selfCls_visit (v : (selfShadow D x ε h).Visit) :
    selfCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (selfModel D x ε h) hε v, smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩ := by
  sorry

/-- The smoothed coordinate on `A` (labels `m`): old edges `m < d − 1 ↦ m + 1 + θ − τs`;
`cutStartT ↦ d − τs + θ(τt − ε)`; `cutEndS ↦ ε + θ(1 − τs − ε)` (smallest block, rotation by `d + 1`);
on `B`: old edges `↦ m + d + 1 + θ − τs`; `cutStartS ↦ k − τs + θ(τs − ε)`; `cutEndT ↦ d − τs + τt +
ε + θ(1 − τt − ε)` (smallest block, rotation by `k − d + 1`). -/
theorem self_key_lt_iff (v w : (selfShadow D x ε h).Visit)
    (hc : (toDiagram D x (selfModel D x ε h) hε).compOf v =
      (toDiagram D x (selfModel D x ε h) hε).compOf w) :
    (rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)
        ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) <
      rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)
        ((toDiagram D x (selfModel D x ε h) hε).visitCoord w) ↔
      key D x (origVisit D x (selfModel D x ε h) hε v) <
        key D x (origVisit D x (selfModel D x ε h) hε w)) := by
  sorry

/-- The record bridge, self case. -/
def selfRecordIso :
    RecordIso (toDiagram D x (selfModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCoord D x (selfModel D x ε h) hε (selfCls D x) (selfCls_bijective D x h)
    (selfCls_visit D x hε h) (selfBase D x) (selfBase_mem D x h) (self_key_lt_iff D x hε h)

end SelfRecord

/-- **The record bridge for the construction.** -/
theorem smoothDiagram_record (hε : SmallEps D x ε) :
    Nonempty (RecordIso (smoothDiagram D x ε hε).record (D.record.smooth (D.overVisit x))) := by
  unfold smoothDiagram
  split_ifs with h
  · exact ⟨selfRecordIso D x hε h⟩
  · exact ⟨mixedRecordIso D x hε h⟩

end Smoothing

/-! ## 9. The goal theorems (namespace `SM.Link`) -/

open Smoothing

/-- **exists_smoothing** (design file, section skein_and_moves; sm-3:1084-1103): every crossing of
every diagram admits an oriented smoothing — the ε-reconnection `smoothDiagram`. -/
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ :=
  ⟨smoothDiagram D x (eps D x) (eps_small D x), isOrientedSmoothing_smoothDiagram D x _ (eps_small D x)⟩

/-- **smoothing_record, constructive form**: the smoothing produced by `exists_smoothing` has the
record `D.record.smooth (overVisit x)` (sm-3:1090-1103, the cycle rewriting
`(x A y B) ↦ (x B), (y A)` / `(x A), (y B) ↦ (x B y A)`).  This is the form the (N, b) inductions
of rp:record-polynomial and lp:core consume: it yields `c(D₀) = c ± 1 ≥ 1`
(`Record.componentCount_smooth`) and `N(D₀) = N − 1` (`IsOrientedSmoothing.card_crossing`). -/
theorem exists_smoothing_record (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) :=
  ⟨smoothDiagram D x (eps D x) (eps_small D x), isOrientedSmoothing_smoothDiagram D x _ (eps_small D x),
    smoothDiagram_record D x (eps D x) (eps_small D x)⟩

/-- The same for the under occurrence, or any occurrence `v` of `x` (`Record.smoothPairIso`). -/
theorem exists_smoothing_record_visit (D : Diagram) (x : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth v)) := by
  obtain ⟨D₀, hD₀, ⟨ι⟩⟩ := exists_smoothing_record D x
  refine ⟨D₀, hD₀, ?_⟩
  have h := D.visit_eq_over_or_under v
  rw [hv] at h
  rcases h with rfl | rfl
  · exact ⟨ι⟩
  · exact ⟨ι.trans (D.record.smoothPairIso (D.overVisit x)).symm⟩

/-- The `SmoothingRecordClause` of LinkMoves holds for the constructed smoothing. -/
theorem smoothingRecordClause_smoothDiagram (D : Diagram) (x : D.Γ.Crossing) :
    SmoothingRecordClause Diagram.record (fun _ v => v) D x (smoothDiagram D x (eps D x) (eps_small D x)) :=
  smoothDiagram_record D x (eps D x) (eps_small D x)

open scoped Classical in
/-- Consumers' counts: the constructed smoothing has `c ± 1` components and `N − 1` crossings. -/
theorem exists_smoothing_counts (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) ∧
      D₀.componentCount = (if D.record.IsSelfCrossing (D.overVisit x) then D.componentCount + 1
        else D.componentCount - 1) ∧
      1 ≤ D₀.componentCount ∧
      Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing := by
  obtain ⟨D₀, hD₀, ⟨ι⟩⟩ := exists_smoothing_record D x
  refine ⟨D₀, hD₀, ⟨ι⟩, ?_, D₀.componentCount_pos, hD₀.card_crossing⟩
  rw [← D₀.record_componentCount, ι.componentCount_eq, D.record.componentCount_smooth,
    D.record_componentCount]

end

end SM.Link
