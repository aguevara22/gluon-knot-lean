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

/-! U4 helpers (general): `det` under rescaling, traversal points `⟨e.1, (e.2, θ)⟩` built from a
strand and a parameter, and congruence of `crossingParam`. -/

theorem det_smul_smul (a b : Plane) (l m : ℝ) : det (l • a) (m • b) = (l * m) * det a b := by
  simp only [det, Prod.smul_fst, Prod.smul_snd, smul_eq_mul]; ring

theorem Shadow.mk_eq_mk_iff {Γ : Shadow} (e e' : Γ.Strand) (θ θ' : Set.Ico (0:ℝ) 1) :
    (⟨e.1, (e.2, θ)⟩ : Γ.Pt) = ⟨e'.1, (e'.2, θ')⟩ ↔ e = e' ∧ θ = θ' := by
  obtain ⟨i, m⟩ := e
  obtain ⟨i', m'⟩ := e'
  constructor
  · intro h
    rw [Sigma.mk.inj_iff] at h
    obtain ⟨rfl, h2⟩ := h
    have h3 := eq_of_heq h2
    rw [Prod.mk.injEq] at h3
    obtain ⟨rfl, rfl⟩ := h3
    exact ⟨rfl, rfl⟩
  · rintro ⟨h1, rfl⟩
    rw [Sigma.mk.inj_iff] at h1
    obtain ⟨rfl, h2⟩ := h1
    rw [eq_of_heq h2]

theorem mem_sphere_of_mem_closedBall_not_mem_ball {c q : Plane} {r : ℝ}
    (h1 : q ∈ Metric.closedBall c r) (h2 : q ∉ Metric.ball c r) : q ∈ Metric.sphere c r :=
  Metric.mem_sphere.mpr (le_antisymm (Metric.mem_closedBall.mp h1)
    (not_lt.mp (fun h => h2 (Metric.mem_ball.mpr h))))

theorem Diagram.crossingParam_congr (D : Diagram) {y y' : D.Γ.Crossing} {s s' : D.Γ.Strand}
    (hy : y = y') (hs : s = s') (h : s ∈ y.val) (h' : s' ∈ y'.val) :
    D.crossingParam y h = D.crossingParam y' h' := by
  subst hy; subst hs; rfl

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

/-! U4 helpers: kind-level parameter arithmetic (`origParam`/`liftParam` are inverse affine maps
on the non-arc kinds; directions of non-arc kinds are positive multiples of the original
directions; two non-arc kinds over the same strand with a common rescaled parameter coincide). -/

theorem liftParam_origParam (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) (θ : ℝ) : κ.liftParam ε (κ.origParam ε θ) = θ := by
  have h1 : τs D x - ε ≠ 0 := by linarith [hε.lt_τs]
  have h2 : 1 - τs D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τs]
  have h3 : τt D x - ε ≠ 0 := by linarith [hε.lt_τt]
  have h4 : 1 - τt D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τt]
  cases κ with
  | old e => rfl
  | cutStartS => simp only [liftParam, origParam]; rw [div_eq_iff h1]
  | cutEndS => simp only [liftParam, origParam]; rw [div_eq_iff h2]; ring
  | cutStartT => simp only [liftParam, origParam]; rw [div_eq_iff h3]
  | cutEndT => simp only [liftParam, origParam]; rw [div_eq_iff h4]; ring
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem origParam_liftParam (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) (θ : ℝ) : κ.origParam ε (κ.liftParam ε θ) = θ := by
  have h1 : τs D x - ε ≠ 0 := by linarith [hε.lt_τs]
  have h2 : 1 - τs D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τs]
  have h3 : τt D x - ε ≠ 0 := by linarith [hε.lt_τt]
  have h4 : 1 - τt D x - ε ≠ 0 := by linarith [hε.lt_one_sub_τt]
  cases κ with
  | old e => rfl
  | cutStartS => simp only [liftParam, origParam]; exact div_mul_cancel₀ θ h1
  | cutEndS => simp only [liftParam, origParam]; rw [div_mul_cancel₀ _ h2]; ring
  | cutStartT => simp only [liftParam, origParam]; exact div_mul_cancel₀ θ h3
  | cutEndT => simp only [liftParam, origParam]; rw [div_mul_cancel₀ _ h4]; ring
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem dir_eq_smul_orig (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)
    (hκ' : κ ≠ arcTS) : ∃ l : ℝ, 0 < l ∧ κ.dir ε = l • D.Γ.dir κ.orig := by
  cases κ with
  | old e => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartS => exact ⟨τs D x - ε, sub_pos.mpr hε.lt_τs, rfl⟩
  | cutEndS => exact ⟨1 - τs D x - ε, by linarith [hε.lt_one_sub_τs], rfl⟩
  | cutStartT => exact ⟨τt D x - ε, sub_pos.mpr hε.lt_τt, rfl⟩
  | cutEndT => exact ⟨1 - τt D x - ε, by linarith [hε.lt_one_sub_τt], rfl⟩
  | arcST => exact absurd rfl hκ
  | arcTS => exact absurd rfl hκ'

theorem origParam_mem_Ico (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) {θ : ℝ} (h0 : 0 ≤ θ)
    (h1 : θ < 1) : κ.origParam ε θ ∈ Set.Ico (0:ℝ) 1 := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt
  have := hε.lt_one_sub_τt
  have := τs_pos D x; have := τs_lt_one D x; have := τt_pos D x; have := τt_lt_one D x
  cases κ <;> simp only [origParam, Set.mem_Ico]
  · exact ⟨h0, h1⟩
  · exact ⟨mul_nonneg h0 (by linarith), by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨mul_nonneg h0 (by linarith), by nlinarith⟩
  · exact ⟨by nlinarith, by nlinarith⟩
  · exact ⟨by linarith, by linarith⟩
  · exact ⟨by linarith, by linarith⟩

theorem origParam_zero (ε : ℝ) (κ : StrandKind D x) (h1 : κ ≠ cutEndS) (h2 : κ ≠ cutEndT)
    (h3 : κ ≠ arcST) (h4 : κ ≠ arcTS) : κ.origParam ε 0 = 0 := by
  cases κ with
  | old e => rfl
  | cutStartS => exact zero_mul _
  | cutStartT => exact zero_mul _
  | cutEndS => exact absurd rfl h1
  | cutEndT => exact absurd rfl h2
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

theorem origParam_ne_zero (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (h3 : κ ≠ arcST)
    (h4 : κ ≠ arcTS) {θ : ℝ} (h0 : 0 ≤ θ) (hθ : θ ≠ 0) : κ.origParam ε θ ≠ 0 := by
  have := hε.pos; have := hε.lt_τs; have := hε.lt_one_sub_τs; have := hε.lt_τt
  have := hε.lt_one_sub_τt
  have hθ' : 0 < θ := lt_of_le_of_ne h0 (Ne.symm hθ)
  cases κ with
  | old e => exact hθ
  | cutStartS => exact (mul_pos hθ' (by linarith)).ne'
  | cutEndS => exact (add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg h0 (by linarith))).ne'
  | cutStartT => exact (mul_pos hθ' (by linarith)).ne'
  | cutEndT => exact (add_pos_of_pos_of_nonneg (by linarith) (mul_nonneg h0 (by linarith))).ne'
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

/-- The direction of the predecessor of a kind whose tail is an old vertex is a positive multiple
of the direction of the preceding strand of `D`. -/
theorem dir_pred_eq_smul (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)
    (h1 : κ ≠ cutEndS) (h2 : κ ≠ cutEndT) (h3 : κ ≠ arcST) (h4 : κ ≠ arcTS) :
    ∃ l : ℝ, 0 < l ∧ κ.pred.dir ε = l • D.Γ.dir ⟨κ.orig.1, κ.orig.2 - 1⟩ := by
  cases κ with
  | old e =>
    simp only [pred, orig]
    split_ifs with hs ht
    · subst hs
      refine ⟨1 - τs D x - ε, by linarith [hε.lt_one_sub_τs], ?_⟩
      show (1 - τs D x - ε) • es D x = (1 - τs D x - ε) • D.Γ.dir ⟨(sS D x).1, (sS D x).2 + 1 - 1⟩
      rw [add_sub_cancel_right]
      try rfl
    · subst ht
      refine ⟨1 - τt D x - ε, by linarith [hε.lt_one_sub_τt], ?_⟩
      show (1 - τt D x - ε) • et D x = (1 - τt D x - ε) • D.Γ.dir ⟨(tS D x).1, (tS D x).2 + 1 - 1⟩
      rw [add_sub_cancel_right]
      try rfl
    · exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartS => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutStartT => exact ⟨1, one_pos, (one_smul ℝ _).symm⟩
  | cutEndS => exact absurd rfl h1
  | cutEndT => exact absurd rfl h2
  | arcST => exact absurd rfl h3
  | arcTS => exact absurd rfl h4

theorem eq_of_orig_eq_of_origParam_eq (ε : ℝ) (hε : SmallEps D x ε) {κ κ' : StrandKind D x}
    (hκ : κ ≠ arcST ∧ κ ≠ arcTS) (hκ' : κ' ≠ arcST ∧ κ' ≠ arcTS) (ho : κ.Occurs) (ho' : κ'.Occurs)
    (horig : κ.orig = κ'.orig) {θ θ' : ℝ} (h0 : 0 ≤ θ) (h1 : θ < 1) (h0' : 0 ≤ θ') (h1' : θ' < 1)
    (hp : κ.origParam ε θ = κ'.origParam ε θ') : κ = κ' := by
  have hst := sS_ne_tS D x
  have hε1 := hε.pos; have hε2 := hε.lt_τs; have hε3 := hε.lt_one_sub_τs
  have hε4 := hε.lt_τt; have hε5 := hε.lt_one_sub_τt
  have m1 := mul_pos (sub_pos.mpr h1) (sub_pos.mpr hε2)
  have m2 := mul_pos (sub_pos.mpr h1') (sub_pos.mpr hε2)
  have m3 := mul_pos (sub_pos.mpr h1) (sub_pos.mpr hε4)
  have m4 := mul_pos (sub_pos.mpr h1') (sub_pos.mpr hε4)
  have m5 := mul_nonneg h0 (sub_pos.mpr hε3).le
  have m6 := mul_nonneg h0' (sub_pos.mpr hε3).le
  have m7 := mul_nonneg h0 (sub_pos.mpr hε5).le
  have m8 := mul_nonneg h0' (sub_pos.mpr hε5).le
  cases κ <;> cases κ' <;>
    try simp only [orig, origParam, Occurs, ne_eq, old.injEq] at horig hp ho ho' ⊢
  all_goals first
  | rfl
  | exact horig
  | exact absurd horig hst
  | exact absurd horig.symm hst
  | exact absurd horig ho.1
  | exact absurd horig ho.2
  | exact absurd horig.symm ho'.1
  | exact absurd horig.symm ho'.2
  | exact absurd rfl hκ.1
  | exact absurd rfl hκ.2
  | exact absurd rfl hκ'.1
  | exact absurd rfl hκ'.2
  | nlinarith

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

/-! U4 helpers at the model level: evaluation of `⟨u.1, (u.2, θ)⟩` through the kind of `u`; arcs
evaluate into the open disc, so strands through outside points and through crossings are not
arcs; the pair (original strand, rescaled parameter) determines an outside traversal point. -/

omit hε in
theorem eval_mk' (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ = (M.kind u).tail ε + θ.val • (M.kind u).dir ε :=
  M.eval_eq ⟨u.1, (u.2, θ)⟩

omit hε in
theorem eval_eq_edgePt (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) (h1 : M.kind u ≠ StrandKind.arcST)
    (h2 : M.kind u ≠ StrandKind.arcTS) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ = D.Γ.edgePt (M.orig u) ((M.kind u).origParam ε θ.val) := by
  rw [eval_mk' D x M u θ, StrandKind.tail_add_smul_dir ε _ h1 h2]; rfl

theorem eval_arc_mem_ball (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1)
    (h : M.kind u = StrandKind.arcST ∨ M.kind u = StrandKind.arcTS) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) := by
  have hmem : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ (M.kind u).seg ε :=
    ⟨θ.val, θ.2.1, θ.2.2.le, eval_mk' D x M u θ⟩
  exact Metric.ball_subset_ball (arc_lt_discRadius D x ε hε).le
    (StrandKind.seg_arc_subset_ball ε hε _ h hmem)

theorem kind_ne_arc_of_not_mem_ball (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1)
    (h : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∉ Metric.ball (pt D x) (discRadius D x ε)) :
    M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS :=
  ⟨fun h' => h (eval_arc_mem_ball D x M hε u θ (Or.inl h')),
   fun h' => h (eval_arc_mem_ball D x M hε u θ (Or.inr h'))⟩

theorem kind_ne_arc_of_not_mem_interior (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    M.kind ⟨q.1, q.2.1⟩ ≠ StrandKind.arcST ∧ M.kind ⟨q.1, q.2.1⟩ ≠ StrandKind.arcTS := by
  rw [interior_disc D x ε hε] at hq
  exact kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hq

theorem kind_ne_arc_of_mem (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS := by
  have hmem : Γ₀.crossingPoint y ∈ (M.kind u).seg ε := by
    rw [← M.seg_eq]; exact Γ₀.crossingPoint_mem y hu
  have hnot : Γ₀.crossingPoint y ∉ disc D x ε := by
    rw [crossingPoint_origCrossing D x M hε y]
    exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)
  have key : ¬ (M.kind u = StrandKind.arcST ∨ M.kind u = StrandKind.arcTS) := fun h =>
    hnot (Metric.ball_subset_closedBall (Metric.ball_subset_ball (arc_lt_discRadius D x ε hε).le
      (StrandKind.seg_arc_subset_ball ε hε _ h hmem)))
  exact ⟨fun h => key (Or.inl h), fun h => key (Or.inr h)⟩

theorem eq_of_orig_eq (u u' : Γ₀.Strand) (θ θ' : Set.Ico (0:ℝ) 1)
    (hκ : M.kind u ≠ StrandKind.arcST ∧ M.kind u ≠ StrandKind.arcTS)
    (hκ' : M.kind u' ≠ StrandKind.arcST ∧ M.kind u' ≠ StrandKind.arcTS)
    (horig : M.orig u = M.orig u')
    (hp : (M.kind u).origParam ε θ.val = (M.kind u').origParam ε θ'.val) : u = u' ∧ θ = θ' := by
  have hk : M.kind u = M.kind u' :=
    StrandKind.eq_of_orig_eq_of_origParam_eq ε hε hκ hκ' (M.kind_occurs u) (M.kind_occurs u')
      horig θ.2.1 θ.2.2 θ'.2.1 θ'.2.2 hp
  have hu : u = u' := M.kind_injective hk
  subst hu
  refine ⟨rfl, Subtype.ext ?_⟩
  have := congrArg ((M.kind u).liftParam ε) hp
  rwa [StrandKind.liftParam_origParam ε hε _ hκ.1 hκ.2,
    StrandKind.liftParam_origParam ε hε _ hκ.1 hκ.2] at this

/-- The traversal point of `D` under a traversal point of `Γ₀` outside the open disc: the original
strand at the rescaled parameter (the body of `origPt` before the clamp). -/
theorem exists_pt_of_not_mem_ball (q : Γ₀.Pt)
    (hq : Γ₀.eval q ∉ Metric.ball (pt D x) (discRadius D x ε)) :
    ∃ p : D.Γ.Pt, D.Γ.eval p = Γ₀.eval q ∧ (⟨p.1, p.2.1⟩ : D.Γ.Strand) = M.orig ⟨q.1, q.2.1⟩ ∧
      p.2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hq
  exact ⟨⟨(M.orig ⟨q.1, q.2.1⟩).1, ((M.orig ⟨q.1, q.2.1⟩).2,
    ⟨(M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val,
      StrandKind.origParam_mem_Ico ε hε _ q.2.2.2.1 q.2.2.2.2⟩)⟩,
    (eval_eq_edgePt D x M ⟨q.1, q.2.1⟩ q.2.2 h1 h2).symm, rfl, rfl⟩

omit hε in
/-- Every component of `Γ₀` has a strand whose tail is a vertex of `D` (at most two predecessor
steps from any strand). -/
theorem exists_tail_old (i : Fin Γ₀.c) :
    ∃ (m : ZMod (Γ₀.comp i).k) (e : D.Γ.Strand), Γ₀.tail ⟨i, m⟩ = D.Γ.tail e := by
  have key : ∀ m : ZMod (Γ₀.comp i).k,
      ((∃ e, M.kind ⟨i, m⟩ = StrandKind.old e) ∨ M.kind ⟨i, m⟩ = StrandKind.cutStartS ∨
        M.kind ⟨i, m⟩ = StrandKind.cutStartT) → ∃ e, Γ₀.tail ⟨i, m⟩ = D.Γ.tail e := by
    intro m h
    rw [M.tail_eq]
    rcases h with ⟨e, he⟩ | he | he <;> rw [he]
    · exact ⟨e, rfl⟩
    · exact ⟨sS D x, rfl⟩
    · exact ⟨tS D x, rfl⟩
  have hp1 := M.kind_pred ⟨i, 0⟩
  have hp2 := M.kind_pred ⟨i, 0 - 1⟩
  dsimp only at hp1 hp2
  rcases hk : M.kind ⟨i, 0⟩ with e | _ | _ | _ | _ | _ | _
  · exact ⟨0, key 0 (Or.inl ⟨e, hk⟩)⟩
  · exact ⟨0, key 0 (Or.inr (Or.inl hk))⟩
  · rw [hk] at hp1; rw [hp1] at hp2
    exact ⟨0 - 1 - 1, key _ (Or.inr (Or.inr hp2))⟩
  · exact ⟨0, key 0 (Or.inr (Or.inr hk))⟩
  · rw [hk] at hp1; rw [hp1] at hp2
    exact ⟨0 - 1 - 1, key _ (Or.inr (Or.inl hp2))⟩
  · rw [hk] at hp1
    exact ⟨0 - 1, key _ (Or.inr (Or.inl hp1))⟩
  · rw [hk] at hp1
    exact ⟨0 - 1, key _ (Or.inr (Or.inr hp1))⟩

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
  unfold overStrand₀
  split_ifs with h
  · exact h
  · have h1 : M.orig y.fst = D.underStrand (origCrossing D x M hε y) :=
      D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing D x M hε y.fst_mem) h
    apply D.eq_over_of_mem_of_ne _ (orig_mem_origCrossing D x M hε y.snd_mem)
    intro h2
    exact Γ₀.other_ne y y.fst_mem
      (orig_injOn_crossing D x M hε y y.snd_mem y.fst_mem (h2.trans h1.symm))

/-- **The smoothed diagram** on a splice model. -/
def toDiagram : Diagram where
  Γ := Γ₀
  generic := generic D x M hε
  overStrand := overStrand₀ D x M hε
  over_mem := overStrand₀_mem D x M hε

@[simp] theorem toDiagram_Γ : (toDiagram D x M hε).Γ = Γ₀ := rfl

theorem toDiagram_underStrand_orig (y : Γ₀.Crossing) :
    M.orig ((toDiagram D x M hε).underStrand y) = D.underStrand (origCrossing D x M hε y) := by
  have hmem : (toDiagram D x M hε).underStrand y ∈ y.val := (toDiagram D x M hε).under_mem y
  have hne : (toDiagram D x M hε).underStrand y ≠ overStrand₀ D x M hε y :=
    (toDiagram D x M hε).under_ne_over y
  apply D.eq_under_of_mem_of_ne _ (orig_mem_origCrossing D x M hε hmem)
  intro h
  exact hne (orig_injOn_crossing D x M hε y hmem (overStrand₀_mem D x M hε y)
    (h.trans (orig_overStrand₀ D x M hε y).symm))

/-- Signs are inherited (directions of cut pieces are positive multiples of the originals). -/
theorem toDiagram_sign (y : Γ₀.Crossing) :
    (toDiagram D x M hε).sign y = D.sign (origCrossing D x M hε y) := by
  have key : ∀ u u' : Γ₀.Strand, u ∈ y.val → u' ∈ y.val →
      M.orig u = D.overStrand (origCrossing D x M hε y) →
      M.orig u' = D.underStrand (origCrossing D x M hε y) →
      SignType.sign (det (Γ₀.dir u) (Γ₀.dir u')) = D.sign (origCrossing D x M hε y) := by
    intro u u' hu hu' ho ho'
    obtain ⟨l, hl, hdl⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind u)
      (kind_ne_arc_of_mem D x M hε y hu).1 (kind_ne_arc_of_mem D x M hε y hu).2
    obtain ⟨m, hm, hdm⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind u')
      (kind_ne_arc_of_mem D x M hε y hu').1 (kind_ne_arc_of_mem D x M hε y hu').2
    unfold Diagram.sign
    rw [M.dir_eq u, M.dir_eq u', hdl, hdm, det_smul_smul, sign_mul, sign_pos (mul_pos hl hm),
      one_mul, ← ho, ← ho']
    rfl
  exact key _ _ (overStrand₀_mem D x M hε y) ((toDiagram D x M hε).under_mem y)
    (orig_overStrand₀ D x M hε y) (toDiagram_underStrand_orig D x M hε y)

/-- The crossing parameter of a strand of `Γ₀` through `y` is the rescaled parameter of `D`. -/
theorem crossingParam_toDiagram (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :
    (toDiagram D x M hε).crossingParam y hu =
      (M.kind u).liftParam ε (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε y hu
  have hs : Γ₀.crossingPoint y =
      edgePoint (Γ₀.comp u.1).P u.2 ((toDiagram D x M hε).crossingParam y hu) :=
    ((toDiagram D x M hε).crossingParam_spec y hu).2.2
  have hD := D.crossingParam_spec (origCrossing D x M hε y) (orig_mem_origCrossing D x M hε hu)
  have key : D.Γ.edgePt (M.orig u)
      ((M.kind u).origParam ε ((toDiagram D x M hε).crossingParam y hu)) =
      D.Γ.edgePt (M.orig u) (D.crossingParam (origCrossing D x M hε y)
        (orig_mem_origCrossing D x M hε hu)) := by
    show edgePoint (D.Γ.comp (M.kind u).orig.1).P (M.kind u).orig.2 _ =
      edgePoint (D.Γ.comp (M.orig u).1).P (M.orig u).2 _
    rw [← StrandKind.tail_add_smul_dir ε _ h1 h2, ← M.tail_eq, ← M.dir_eq, ← hD.2.2,
      ← crossingPoint_origCrossing D x M hε y, hs]
    rfl
  have := D.generic.edgePt_injective _ key
  rw [← this, StrandKind.liftParam_origParam ε hε _ h1 h2]

/-! ### 6d. Cleanness of `D₀` and its two arcs inside the disc -/

/-- No crossing point of `Γ₀` lies in the closed disc. -/
theorem crossingPoint_not_mem_disc (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ disc D x ε := by
  rw [crossingPoint_origCrossing D x M hε y]
  exact crossingPoint_ne_not_mem_disc D x ε hε (origCrossing_ne D x M hε y)

theorem no_inner_toDiagram (y : Γ₀.Crossing) : Γ₀.crossingPoint y ∉ interior (disc D x ε) :=
  fun h => crossingPoint_not_mem_disc D x M hε y (interior_subset h)

/-- U4 helper: injectivity of `Γ₀.eval` on the frontier of the disc (through `clean_D` and the
injectivity of the pair (original strand, rescaled parameter)). -/
theorem frontier_injOn_toDiagram :
    Set.InjOn Γ₀.eval {p | Γ₀.eval p ∈ frontier (disc D x ε)} := by
    intro q hq q' hq' heq
    simp only [Set.mem_setOf_eq, frontier_disc D x ε hε] at hq hq'
    have hnb : Γ₀.eval q ∉ Metric.ball (pt D x) (discRadius D x ε) := fun h =>
      (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hq)
    have hnb' : Γ₀.eval q' ∉ Metric.ball (pt D x) (discRadius D x ε) := fun h =>
      (Metric.mem_ball.mp h).ne (Metric.mem_sphere.mp hq')
    obtain ⟨p, hp1, hp2, hp3⟩ := exists_pt_of_not_mem_ball D x M hε q hnb
    obtain ⟨p', hp1', hp2', hp3'⟩ := exists_pt_of_not_mem_ball D x M hε q' hnb'
    have hpp : p = p' := (clean_D D x hε).frontier_injOn
      (by show D.Γ.eval p ∈ frontier (disc D x ε); rw [hp1, frontier_disc D x ε hε]; exact hq)
      (by show D.Γ.eval p' ∈ frontier (disc D x ε); rw [hp1', frontier_disc D x ε hε]; exact hq')
      (by rw [hp1, hp1']; exact heq)
    subst hpp
    obtain ⟨hu, hθ⟩ := eq_of_orig_eq D x M hε ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2
      (kind_ne_arc_of_not_mem_ball D x M hε ⟨q.1, q.2.1⟩ q.2.2 hnb)
      (kind_ne_arc_of_not_mem_ball D x M hε ⟨q'.1, q'.2.1⟩ q'.2.2 hnb') (hp2.symm.trans hp2')
      (hp3.symm.trans hp3')
    exact (Shadow.mk_eq_mk_iff ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2).mpr ⟨hu, hθ⟩

/-- U4 helper: every component of `Γ₀` leaves the disc (at a vertex of `D`). -/
theorem exists_eval_not_mem_disc (i : Fin Γ₀.c) :
    ∃ p : TraversalPoint (Γ₀.comp i).k, Γ₀.eval ⟨i, p⟩ ∉ disc D x ε := by
  obtain ⟨m, e, he⟩ := exists_tail_old D x M i
  refine ⟨(m, ⟨0, le_rfl, zero_lt_one⟩), ?_⟩
  have h0 : Γ₀.eval ⟨i, (m, ⟨0, le_rfl, zero_lt_one⟩)⟩ = Γ₀.tail ⟨i, m⟩ := by
    show edgePoint (Γ₀.comp i).P m (0:ℝ) = (Γ₀.comp i).P m
    simp [edgePoint]
  rw [h0, he]
  exact tail_not_mem_disc D x ε hε e

theorem clean_toDiagram : Clean (disc D x ε) (toDiagram D x M hε) where
  frontier_injOn := frontier_injOn_toDiagram D x M hε
  exits := exists_eval_not_mem_disc D x M hε

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
  apply M.kind_injective
  rw [M.kind_strandOf]
  have h1 := M.kind_succ (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
  have h2 := M.kind_succ ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
    (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩
  rw [M.kind_strandOf] at h1
  dsimp only at h2
  rw [h1] at h2
  rw [← one_add_one_eq_two, ← add_assoc]
  exact h2.symm

omit hε in
theorem strandOf_cutEndS_eq :
    M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS =
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ := by
  apply M.kind_injective
  rw [M.kind_strandOf]
  have h1 := M.kind_succ (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
  have h2 := M.kind_succ ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
    (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩
  rw [M.kind_strandOf] at h1
  dsimp only at h2
  rw [h1] at h2
  rw [← one_add_one_eq_two, ← add_assoc]
  exact h2.symm

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

/-! U4 helpers for the two smoothing arcs of `D₀`: the kinds of the three strands of each arc,
per-kind membership of `⟨u.1, (u.2, θ)⟩` in the disc / open disc, and the classification of the
points of `arcST₀` / `arcTS₀` by kind and parameter. -/

omit hε in
theorem kind_cutStartS_add_one :
    M.kind ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
      (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩ = StrandKind.arcST := by
  rw [M.kind_succ, M.kind_strandOf]; rfl

omit hε in
theorem kind_cutStartS_add_two :
    M.kind ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
      (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ = StrandKind.cutEndT := by
  rw [← strandOf_cutEndT_eq D x M, M.kind_strandOf]

omit hε in
theorem kind_cutStartT_add_one :
    M.kind ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
      (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩ = StrandKind.arcTS := by
  rw [M.kind_succ, M.kind_strandOf]; rfl

omit hε in
theorem kind_cutStartT_add_two :
    M.kind ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
      (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ = StrandKind.cutEndS := by
  rw [← strandOf_cutEndS_eq D x M, M.kind_strandOf]

omit hε in
theorem eq_strandOf_of_kind {u : Γ₀.Strand} {κ : StrandKind D x} (hκ : κ.Occurs)
    (h : M.kind u = κ) : u = M.strandOf κ hκ :=
  M.kind_injective (by rw [h, M.kind_strandOf])

theorem eval_old_not_mem_disc (u : Γ₀.Strand) (e : D.Γ.Strand) (hu : M.kind u = StrandKind.old e)
    (θ : Set.Ico (0:ℝ) 1) : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∉ disc D x ε := by
  intro hmem
  have hseg : Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ D.Γ.seg e := by
    rw [← StrandKind.seg_old ε e, ← hu]
    exact ⟨θ.val, θ.2.1, θ.2.2.le, eval_mk' D x M u θ⟩
  have hocc := M.kind_occurs u
  rw [hu] at hocc
  rcases mem_seg_of_mem_disc D x ε hε hseg hmem with h | h
  · exact hocc.1 (by rw [h])
  · exact hocc.2 (by rw [h])

theorem eval_cutStartS_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ₀sIn D x ε ≤ θ.val := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θ.val * (τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_disc_iff D x ε hε]
  unfold θ₀sIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 := (θsIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_le_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_le_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartS_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ₀sIn D x ε < θ.val := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θ.val * (τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_ball_iff D x ε hε]
  unfold θ₀sIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
  have h2 := (θsIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_lt_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_lt_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartT_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ₀tIn D x ε ≤ θ.val := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θ.val * (τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_disc_iff D x ε hε]
  unfold θ₀tIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h2 := (θtIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_le_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_le_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutStartT_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutStartT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ₀tIn D x ε < θ.val := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θ.val * (τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_ball_iff D x ε hε]
  unfold θ₀tIn
  simp only [StrandKind.liftParam]
  have hpos : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
  have h2 := (θtIn_lt_cut D x ε hε).2
  have h3 := mul_lt_mul_of_pos_right θ.2.2 hpos
  have h4 := hε.pos
  constructor
  · rintro ⟨h1, -⟩; exact (div_lt_iff₀ hpos).mpr h1
  · intro h; exact ⟨(div_lt_iff₀ hpos).mp h, by linarith⟩

theorem eval_cutEndT_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ.val ≤ θ₀tOut D x ε := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2
    (τt D x + ε + θ.val * (1 - τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_disc_iff D x ε hε]
  unfold θ₀tOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  have h2 := (θtIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [le_div_iff₀ hpos]; linarith
  · intro h; rw [le_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndT_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndT)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ.val < θ₀tOut D x ε := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2
    (τt D x + ε + θ.val * (1 - τt D x - ε)) ∈ _ ↔ _
  rw [edgePoint_t_mem_ball_iff D x ε hε]
  unfold θ₀tOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
  have h2 := (θtIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [lt_div_iff₀ hpos]; linarith
  · intro h; rw [lt_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndS_mem_disc_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔ θ.val ≤ θ₀sOut D x ε := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2
    (τs D x + ε + θ.val * (1 - τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_disc_iff D x ε hε]
  unfold θ₀sOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h2 := (θsIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [le_div_iff₀ hpos]; linarith
  · intro h; rw [le_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem eval_cutEndS_mem_ball_iff (u : Γ₀.Strand) (hu : M.kind u = StrandKind.cutEndS)
    (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔ θ.val < θ₀sOut D x ε := by
  rw [eval_eq_edgePt D x M u θ (by rw [hu]; nofun) (by rw [hu]; nofun), SpliceModel.orig, hu]
  show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2
    (τs D x + ε + θ.val * (1 - τs D x - ε)) ∈ _ ↔ _
  rw [edgePoint_s_mem_ball_iff D x ε hε]
  unfold θ₀sOut
  simp only [StrandKind.liftParam]
  have hpos : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
  have h2 := (θsIn_lt_cut D x ε hε).1
  have h3 := mul_nonneg θ.2.1 hpos.le
  have h4 := hε.pos
  constructor
  · rintro ⟨-, h1⟩; rw [lt_div_iff₀ hpos]; linarith
  · intro h; rw [lt_div_iff₀ hpos] at h; exact ⟨by linarith, by linarith⟩

theorem inner_arcST₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcST₀ D x M hε).Inner ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartS ∧ θ₀sIn D x ε < θ.val) ∨ M.kind u = StrandKind.arcST ∨
        (M.kind u = StrandKind.cutEndT ∧ θ.val < θ₀tOut D x ε) := by
  have hval := strandOf_cutStartS_val D x M
  constructor
  · rintro ⟨r, hb, hp⟩
    obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
      ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1, r.1⟩ θ r.2).mp hp
    rcases (traversalBetween_span_two _ hval _ _ r).mp hb with ⟨hr, hlt⟩ | hr | ⟨hr, hlt⟩
    · left
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
    · right; left
      rw [hr] at hu
      rw [hu]; exact kind_cutStartS_add_one D x M
    · right; right
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact kind_cutStartS_add_two D x M
  · rintro (⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩)
    · have hu := eq_strandOf_of_kind D x M StrandKind.occurs_cutStartS hk
      subst hu
      exact ⟨((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2, θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inl ⟨rfl, hlt⟩), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartS_add_one D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 1 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inl rfl)), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartS_add_two D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inr ⟨rfl, hlt⟩)), rfl⟩

theorem mem_arcST₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcST₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartS ∧ θ₀sIn D x ε ≤ θ.val) ∨ M.kind u = StrandKind.arcST ∨
        (M.kind u = StrandKind.cutEndT ∧ θ.val ≤ θ₀tOut D x ε) := by
  constructor
  · rintro (h | h | h)
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS) θ
        ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩).mp h
      left
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
          (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ θ
        ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩).mp h
      right; right
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact kind_cutStartS_add_two D x M
    · rcases (inner_arcST₀_iff D x M hε u θ).mp h with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
      · exact Or.inl ⟨hk, hlt.le⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨hk, hlt.le⟩)
  · rintro (⟨hk, hle⟩ | hk | ⟨hk, hle⟩)
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inl ⟨hk, hlt⟩)).mem
      · left
        exact (Shadow.mk_eq_mk_iff u (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
          θ ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩).mpr
          ⟨eq_strandOf_of_kind D x M _ hk, Subtype.ext heq.symm⟩
    · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inr (Or.inl hk))).mem
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcST₀_iff D x M hε u θ).mpr (Or.inr (Or.inr ⟨hk, hlt⟩))).mem
      · right; left
        exact (Shadow.mk_eq_mk_iff u
          ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,
            (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩ θ
          ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩).mpr
          ⟨M.kind_injective (by rw [hk, kind_cutStartS_add_two D x M]), Subtype.ext heq⟩

theorem eval_arcST₀_startPt : Γ₀.eval (arcST₀ D x M hε).startPt =
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θsIn D x ε) := by
  have h := eval_eq_edgePt D x M (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS)
    ⟨θ₀sIn D x ε, (θ₀_mem D x ε hε).1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutStartS (θ₀sIn D x ε) = θsIn D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem eval_arcST₀_stopPt : Γ₀.eval (arcST₀ D x M hε).stopPt =
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θtOut D x ε) := by
  have h := eval_eq_edgePt D x M (M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT)
    ⟨θ₀tOut D x ε, (θ₀_mem D x ε hε).2.2.2⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf, strandOf_cutEndT_eq D x M] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutEndT (θ₀tOut D x ε) = θtOut D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem isArc_arcST₀ : Γ₀.IsArc (disc D x ε) (arcST₀ D x M hε) where
  start_ne_stop := by
    intro h
    have h1 : (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 =
        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2 := congrArg Prod.fst h
    have h2 := left_eq_add.mp h1
    have hv := strandOf_cutStartS_val D x M
    have h3 : (2 : ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartS
        StrandKind.occurs_cutStartS).1).k).val = 2 := by
      rw [ZMod.val_two_eq_two_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [h2, ZMod.val_zero] at h3
    exact absurd h3 (by norm_num)
  start_frontier := by
    rw [frontier_disc D x ε hε, eval_arcST₀_startPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_s_mem_disc_iff D x ε hε _).mpr ⟨le_rfl, (θsIn_lt_θsOut D x ε hε).le⟩)
      (fun h => lt_irrefl _ ((edgePoint_s_mem_ball_iff D x ε hε _).mp h).1)
  stop_frontier := by
    rw [frontier_disc D x ε hε, eval_arcST₀_stopPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_t_mem_disc_iff D x ε hε _).mpr ⟨(θtIn_lt_θtOut D x ε hε).le, le_rfl⟩)
      (fun h => lt_irrefl _ ((edgePoint_t_mem_ball_iff D x ε hε _).mp h).2)
  inner_interior := by
    intro p hp
    rw [interior_disc D x ε hε]
    rcases (inner_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hp with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
    · exact (eval_cutStartS_mem_ball_iff D x M hε _ hk _).mpr hlt
    · exact eval_arc_mem_ball D x M hε _ _ (Or.inl hk)
    · exact (eval_cutEndT_mem_ball_iff D x M hε _ hk _).mpr hlt

theorem inner_arcTS₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcTS₀ D x M hε).Inner ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartT ∧ θ₀tIn D x ε < θ.val) ∨ M.kind u = StrandKind.arcTS ∨
        (M.kind u = StrandKind.cutEndS ∧ θ.val < θ₀sOut D x ε) := by
  have hval := strandOf_cutStartT_val D x M
  constructor
  · rintro ⟨r, hb, hp⟩
    obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1, r.1⟩ θ r.2).mp hp
    rcases (traversalBetween_span_two _ hval _ _ r).mp hb with ⟨hr, hlt⟩ | hr | ⟨hr, hlt⟩
    · left
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
    · right; left
      rw [hr] at hu
      rw [hu]; exact kind_cutStartT_add_one D x M
    · right; right
      rw [hr] at hu
      refine ⟨?_, by subst hθ; exact hlt⟩
      rw [hu]; exact kind_cutStartT_add_two D x M
  · rintro (⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩)
    · have hu := eq_strandOf_of_kind D x M StrandKind.occurs_cutStartT hk
      subst hu
      exact ⟨((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2, θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inl ⟨rfl, hlt⟩), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartT_add_one D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 1 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inl rfl)), rfl⟩
    · have hu : u = ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ :=
        M.kind_injective (by rw [hk, kind_cutStartT_add_two D x M])
      subst hu
      exact ⟨(((M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2 :
          ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1).k), θ),
        (traversalBetween_span_two _ hval _ _ _).mpr (Or.inr (Or.inr ⟨rfl, hlt⟩)), rfl⟩

theorem mem_arcTS₀_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    (arcTS₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ↔
      (M.kind u = StrandKind.cutStartT ∧ θ₀tIn D x ε ≤ θ.val) ∨ M.kind u = StrandKind.arcTS ∨
        (M.kind u = StrandKind.cutEndS ∧ θ.val ≤ θ₀sOut D x ε) := by
  constructor
  · rintro (h | h | h)
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT) θ
        ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩).mp h
      left
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
    · obtain ⟨hu, hθ⟩ := (Shadow.mk_eq_mk_iff u
        ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
          (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ θ
        ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩).mp h
      right; right
      refine ⟨?_, by subst hθ; exact le_rfl⟩
      rw [hu]; exact kind_cutStartT_add_two D x M
    · rcases (inner_arcTS₀_iff D x M hε u θ).mp h with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
      · exact Or.inl ⟨hk, hlt.le⟩
      · exact Or.inr (Or.inl hk)
      · exact Or.inr (Or.inr ⟨hk, hlt.le⟩)
  · rintro (⟨hk, hle⟩ | hk | ⟨hk, hle⟩)
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inl ⟨hk, hlt⟩)).mem
      · left
        exact (Shadow.mk_eq_mk_iff u (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
          θ ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩).mpr
          ⟨eq_strandOf_of_kind D x M _ hk, Subtype.ext heq.symm⟩
    · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inr (Or.inl hk))).mem
    · rcases hle.lt_or_eq with hlt | heq
      · exact ((inner_arcTS₀_iff D x M hε u θ).mpr (Or.inr (Or.inr ⟨hk, hlt⟩))).mem
      · right; left
        exact (Shadow.mk_eq_mk_iff u
          ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,
            (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩ θ
          ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩).mpr
          ⟨M.kind_injective (by rw [hk, kind_cutStartT_add_two D x M]), Subtype.ext heq⟩

theorem eval_arcTS₀_startPt : Γ₀.eval (arcTS₀ D x M hε).startPt =
    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (θtIn D x ε) := by
  have h := eval_eq_edgePt D x M (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT)
    ⟨θ₀tIn D x ε, (θ₀_mem D x ε hε).2.2.1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutStartT (θ₀tIn D x ε) = θtIn D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem eval_arcTS₀_stopPt : Γ₀.eval (arcTS₀ D x M hε).stopPt =
    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (θsOut D x ε) := by
  have h := eval_eq_edgePt D x M (M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS)
    ⟨θ₀sOut D x ε, (θ₀_mem D x ε hε).2.1⟩ (by rw [M.kind_strandOf]; nofun)
    (by rw [M.kind_strandOf]; nofun)
  rw [SpliceModel.orig, M.kind_strandOf, strandOf_cutEndS_eq D x M] at h
  dsimp only at h
  have h2 : StrandKind.origParam ε StrandKind.cutEndS (θ₀sOut D x ε) = θsOut D x ε :=
    StrandKind.origParam_liftParam ε hε _ (by nofun) (by nofun) _
  rw [h2] at h
  exact h

theorem isArc_arcTS₀ : Γ₀.IsArc (disc D x ε) (arcTS₀ D x M hε) where
  start_ne_stop := by
    intro h
    have h1 : (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 =
        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2 := congrArg Prod.fst h
    have h2 := left_eq_add.mp h1
    have hv := strandOf_cutStartT_val D x M
    have h3 : (2 : ZMod (Γ₀.comp (M.strandOf StrandKind.cutStartT
        StrandKind.occurs_cutStartT).1).k).val = 2 := by
      rw [ZMod.val_two_eq_two_mod]; exact Nat.mod_eq_of_lt (by omega)
    rw [h2, ZMod.val_zero] at h3
    exact absurd h3 (by norm_num)
  start_frontier := by
    rw [frontier_disc D x ε hε, eval_arcTS₀_startPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_t_mem_disc_iff D x ε hε _).mpr ⟨le_rfl, (θtIn_lt_θtOut D x ε hε).le⟩)
      (fun h => lt_irrefl _ ((edgePoint_t_mem_ball_iff D x ε hε _).mp h).1)
  stop_frontier := by
    rw [frontier_disc D x ε hε, eval_arcTS₀_stopPt D x M hε]
    exact mem_sphere_of_mem_closedBall_not_mem_ball
      ((edgePoint_s_mem_disc_iff D x ε hε _).mpr ⟨(θsIn_lt_θsOut D x ε hε).le, le_rfl⟩)
      (fun h => lt_irrefl _ ((edgePoint_s_mem_ball_iff D x ε hε _).mp h).2)
  inner_interior := by
    intro p hp
    rw [interior_disc D x ε hε]
    rcases (inner_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hp with ⟨hk, hlt⟩ | hk | ⟨hk, hlt⟩
    · exact (eval_cutStartT_mem_ball_iff D x M hε _ hk _).mpr hlt
    · exact eval_arc_mem_ball D x M hε _ _ (Or.inr hk)
    · exact (eval_cutEndS_mem_ball_iff D x M hε _ hk _).mpr hlt

theorem eval_mem_disc_iff (u : Γ₀.Strand) (θ : Set.Ico (0:ℝ) 1) :
    Γ₀.eval ⟨u.1, (u.2, θ)⟩ ∈ disc D x ε ↔
      (arcST₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ ∨ (arcTS₀ D x M hε).Mem ⟨u.1, (u.2, θ)⟩ := by
  rw [mem_arcST₀_iff D x M hε, mem_arcTS₀_iff D x M hε]
  rcases hk : M.kind u with e | _ | _ | _ | _ | _ | _
  · exact iff_of_false (eval_old_not_mem_disc D x M hε u e hk θ) (by simp)
  · rw [eval_cutStartS_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutEndS_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutStartT_mem_disc_iff D x M hε u hk θ]; simp
  · rw [eval_cutEndT_mem_disc_iff D x M hε u hk θ]; simp
  · exact iff_of_true (Metric.ball_subset_closedBall (eval_arc_mem_ball D x M hε u θ (Or.inl hk)))
      (by simp)
  · exact iff_of_true (Metric.ball_subset_closedBall (eval_arc_mem_ball D x M hε u θ (Or.inr hk)))
      (by simp)

theorem arcST₀_ne_arcTS₀ : arcST₀ D x M hε ≠ arcTS₀ D x M hε := by
  intro h
  have h1 : M.kind (Γ₀.strandOf (arcST₀ D x M hε).startPt) =
      M.kind (Γ₀.strandOf (arcTS₀ D x M hε).startPt) := by rw [h]
  have h2 : M.kind (Γ₀.strandOf (arcST₀ D x M hε).startPt) = StrandKind.cutStartS :=
    M.kind_strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS
  have h3 : M.kind (Γ₀.strandOf (arcTS₀ D x M hε).startPt) = StrandKind.cutStartT :=
    M.kind_strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT
  rw [h2, h3] at h1
  cases h1

theorem arcCover_toDiagram : Γ₀.ArcCover (disc D x ε) {arcST₀ D x M hε, arcTS₀ D x M hε} where
  isArc := by
    intro a ha
    rcases ha with rfl | rfl
    · exact isArc_arcST₀ D x M hε
    · exact isArc_arcTS₀ D x M hε
  mem_iff := by
    intro p
    have key := eval_mem_disc_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2
    constructor
    · intro h
      rcases key.mp h with h' | h'
      · exact ⟨_, Or.inl rfl, h'⟩
      · exact ⟨_, Or.inr rfl, h'⟩
    · rintro ⟨a, ha, hm⟩
      rcases ha with rfl | rfl
      · exact key.mpr (Or.inl hm)
      · exact key.mpr (Or.inr hm)
  disjoint := by
    intro a ha b hb hab p hpa hpb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact hab rfl
    · have h1 := (mem_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpa
      have h2 := (mem_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpb
      rcases h1 with ⟨h1, -⟩ | h1 | ⟨h1, -⟩ <;> rcases h2 with ⟨h2, -⟩ | h2 | ⟨h2, -⟩ <;>
        rw [h1] at h2 <;> cases h2
    · have h1 := (mem_arcTS₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpa
      have h2 := (mem_arcST₀_iff D x M hε ⟨p.1, p.2.1⟩ p.2.2).mp hpb
      rcases h1 with ⟨h1, -⟩ | h1 | ⟨h1, -⟩ <;> rcases h2 with ⟨h2, -⟩ | h2 | ⟨h2, -⟩ <;>
        rw [h1] at h2 <;> cases h2
    · exact hab rfl

theorem arcST₀_start : Γ₀.eval (arcST₀ D x M hε).startPt = D.Γ.eval (arcS D x hε).startPt :=
  eval_arcST₀_startPt D x M hε
theorem arcST₀_stop : Γ₀.eval (arcST₀ D x M hε).stopPt = D.Γ.eval (arcT D x hε).stopPt :=
  eval_arcST₀_stopPt D x M hε
theorem arcTS₀_start : Γ₀.eval (arcTS₀ D x M hε).startPt = D.Γ.eval (arcT D x hε).startPt :=
  eval_arcTS₀_startPt D x M hε
theorem arcTS₀_stop : Γ₀.eval (arcTS₀ D x M hε).stopPt = D.Γ.eval (arcS D x hε).stopPt :=
  eval_arcTS₀_stopPt D x M hε

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
    κ.origParam ε θ.val ∈ Set.Ico (0:ℝ) 1 :=
  StrandKind.origParam_mem_Ico ε hε κ θ.2.1 θ.2.2

theorem origPt_param (q : Γ₀.Pt) :
    (origPt D x M q).2.2.val = (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val :=
  clampIco_val_of_mem (origParam_mem D x M hε _ _)

/-- Outside the open disc, `origPt` traces the same point. -/
theorem eval_origPt (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) = Γ₀.eval q := by
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε q hq
  have h : Γ₀.eval q =
      D.Γ.edgePt (M.orig ⟨q.1, q.2.1⟩) ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val) :=
    eval_eq_edgePt D x M ⟨q.1, q.2.1⟩ q.2.2 h1 h2
  show D.Γ.edgePt (M.orig ⟨q.1, q.2.1⟩) (origPt D x M q).2.2.val = Γ₀.eval q
  rw [origPt_param D x M hε q]
  exact h.symm

theorem origPt_outside (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :
    D.Γ.eval (origPt D x M q) ∉ interior (disc D x ε) := by
  rw [eval_origPt D x M hε q hq]; exact hq

/-- U4 helper: a point of `D` on the original strand of a non-arc kind, at a parameter whose lift
is in `[0,1)`, is `origPt` of the corresponding point of `Γ₀`. -/
theorem exists_lift (κ : StrandKind D x) (hκo : κ.Occurs) (h1 : κ ≠ StrandKind.arcST)
    (h2 : κ ≠ StrandKind.arcTS) (e : D.Γ.Strand) (he : κ.orig = e) (θD : Set.Ico (0:ℝ) 1)
    (hl : 0 ≤ κ.liftParam ε θD.val ∧ κ.liftParam ε θD.val < 1) :
    ∃ q : Γ₀.Pt, origPt D x M q = ⟨e.1, (e.2, θD)⟩ ∧
      Γ₀.eval q = D.Γ.eval ⟨e.1, (e.2, θD)⟩ := by
  subst he
  refine ⟨⟨(M.strandOf κ hκo).1, ((M.strandOf κ hκo).2, ⟨κ.liftParam ε θD.val, hl⟩)⟩, ?_, ?_⟩
  · show (⟨(M.orig (M.strandOf κ hκo)).1, ((M.orig (M.strandOf κ hκo)).2,
      clampIco ((M.kind (M.strandOf κ hκo)).origParam ε (κ.liftParam ε θD.val)))⟩ : D.Γ.Pt) = _
    rw [SpliceModel.orig, M.kind_strandOf, StrandKind.origParam_liftParam ε hε κ h1 h2,
      clampIco_val_of_mem' θD]
  · rw [eval_eq_edgePt D x M _ _ (by rw [M.kind_strandOf]; exact h1)
      (by rw [M.kind_strandOf]; exact h2), SpliceModel.orig, M.kind_strandOf]
    dsimp only
    rw [StrandKind.origParam_liftParam ε hε κ h1 h2]
    rfl

/-- U4 helper: surjectivity of `origPt` onto the outside points of `D`. -/
theorem exists_origPt_eq (p : D.Γ.Pt) (hp : D.Γ.eval p ∉ interior (disc D x ε)) :
    ∃ q : Γ₀.Pt, origPt D x M q = p ∧ Γ₀.eval q = D.Γ.eval p := by
  rw [interior_disc D x ε hε] at hp
  have hIn := θsIn_lt_cut D x ε hε
  have htIn := θtIn_lt_cut D x ε hε
  by_cases hs : (⟨p.1, p.2.1⟩ : D.Γ.Strand) = sS D x
  · have hp' : edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 p.2.2.val ∉
        Metric.ball (pt D x) (discRadius D x ε) := by
      rw [← hs]; exact hp
    rw [edgePoint_s_mem_ball_iff D x ε hε, not_and_or, not_lt, not_lt] at hp'
    have hpos1 : 0 < τs D x - ε := sub_pos.mpr hε.lt_τs
    have hpos2 : 0 < 1 - τs D x - ε := by linarith [hε.lt_one_sub_τs]
    rcases hp' with h | h
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutStartS
        StrandKind.occurs_cutStartS (by nofun) (by nofun) _ hs.symm p.2.2
        ⟨div_nonneg p.2.2.2.1 hpos1.le, (div_lt_one hpos1).mpr (by linarith)⟩
      exact ⟨q, hq1, hq2⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutEndS
        StrandKind.occurs_cutEndS (by nofun) (by nofun) _ hs.symm p.2.2
        ⟨div_nonneg (by linarith) hpos2.le, (div_lt_one hpos2).mpr (by linarith [p.2.2.2.2])⟩
      exact ⟨q, hq1, hq2⟩
  · by_cases ht : (⟨p.1, p.2.1⟩ : D.Γ.Strand) = tS D x
    · have hp' : edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 p.2.2.val ∉
          Metric.ball (pt D x) (discRadius D x ε) := by
        rw [← ht]; exact hp
      rw [edgePoint_t_mem_ball_iff D x ε hε, not_and_or, not_lt, not_lt] at hp'
      have hpos1 : 0 < τt D x - ε := sub_pos.mpr hε.lt_τt
      have hpos2 : 0 < 1 - τt D x - ε := by linarith [hε.lt_one_sub_τt]
      rcases hp' with h | h
      · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutStartT
          StrandKind.occurs_cutStartT (by nofun) (by nofun) _ ht.symm p.2.2
          ⟨div_nonneg p.2.2.2.1 hpos1.le, (div_lt_one hpos1).mpr (by linarith)⟩
        exact ⟨q, hq1, hq2⟩
      · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε StrandKind.cutEndT
          StrandKind.occurs_cutEndT (by nofun) (by nofun) _ ht.symm p.2.2
          ⟨div_nonneg (by linarith) hpos2.le, (div_lt_one hpos2).mpr (by linarith [p.2.2.2.2])⟩
        exact ⟨q, hq1, hq2⟩
    · obtain ⟨q, hq1, hq2⟩ := exists_lift D x M hε (StrandKind.old ⟨p.1, p.2.1⟩)
        (StrandKind.occurs_old hs ht) (by nofun) (by nofun) _ rfl p.2.2 ⟨p.2.2.2.1, p.2.2.2.2⟩
      exact ⟨q, hq1, hq2⟩

/-- `origPt` is a bijection from the outside traversal points of `Γ₀` onto those of `D`. -/
theorem origPt_bijective :
    Function.Bijective (fun q : Γ₀.Outside (disc D x ε) =>
      (⟨origPt D x M q.1, origPt_outside D x M hε q.1 q.2⟩ : D.Γ.Outside (disc D x ε))) := by
  constructor
  · rintro ⟨q, hq⟩ ⟨q', hq'⟩ h
    have h' : origPt D x M q = origPt D x M q' := congrArg Subtype.val h
    obtain ⟨horig, hcl⟩ :=
      (Shadow.mk_eq_mk_iff (M.orig ⟨q.1, q.2.1⟩) (M.orig ⟨q'.1, q'.2.1⟩) _ _).mp h'
    have hp : (M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val =
        (M.kind ⟨q'.1, q'.2.1⟩).origParam ε q'.2.2.val := by
      rw [← origPt_param D x M hε q, ← origPt_param D x M hε q']
      exact congrArg Subtype.val hcl
    obtain ⟨hu, hθ⟩ := eq_of_orig_eq D x M hε ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2
      (kind_ne_arc_of_not_mem_interior D x M hε q hq)
      (kind_ne_arc_of_not_mem_interior D x M hε q' hq') horig hp
    exact Subtype.ext ((Shadow.mk_eq_mk_iff ⟨q.1, q.2.1⟩ ⟨q'.1, q'.2.1⟩ q.2.2 q'.2.2).mpr ⟨hu, hθ⟩)
  · rintro ⟨p, hp⟩
    obtain ⟨q, hq1, hq2⟩ := exists_origPt_eq D x M hε p hp
    exact ⟨⟨q, by rw [hq2]; exact hp⟩, Subtype.ext hq1⟩

/-- The outside correspondence `φ`. -/
def outsideEquiv : D.Γ.Outside (disc D x ε) ≃ Γ₀.Outside (disc D x ε) :=
  (Equiv.ofBijective _ (origPt_bijective D x M hε)).symm

/-- U4 helper: `origPt` inverts `outsideEquiv` (`Equiv.ofBijective_apply_symm_apply`). -/
theorem origPt_outsideEquiv (q : D.Γ.Outside (disc D x ε)) :
    origPt D x M (outsideEquiv D x M hε q).1 = q.1 :=
  congrArg Subtype.val (Equiv.ofBijective_apply_symm_apply _ (origPt_bijective D x M hε) q)

theorem outsideEquiv_eval (q : D.Γ.Outside (disc D x ε)) :
    Γ₀.eval (outsideEquiv D x M hε q).1 = D.Γ.eval q.1 := by
  rw [← eval_origPt D x M hε _ (outsideEquiv D x M hε q).2, origPt_outsideEquiv D x M hε q]

theorem outsideEquiv_dir_pos (q : D.Γ.Outside (disc D x ε)) (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧
      Γ₀.dir (Γ₀.strandOf (outsideEquiv D x M hε q).1) = l • D.Γ.dir (D.Γ.strandOf q.1) := by
  have hφ := origPt_outsideEquiv D x M hε q
  have hout := (outsideEquiv D x M hε q).2
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε _ hout
  obtain ⟨l, hl, hdir⟩ := StrandKind.dir_eq_smul_orig ε hε _ h1 h2
  refine ⟨l, hl, ?_⟩
  rw [← hφ]
  show Γ₀.dir ⟨(outsideEquiv D x M hε q).1.1, (outsideEquiv D x M hε q).1.2.1⟩ =
    l • D.Γ.dir (M.orig ⟨(outsideEquiv D x M hε q).1.1, (outsideEquiv D x M hε q).1.2.1⟩)
  rw [M.dir_eq]
  exact hdir

/-- U4 helper: the arriving direction at a point of `Γ₀` strictly outside the disc is a positive
multiple of the arriving direction at its `origPt`. -/
theorem dir_strandBefore_origPt (q : Γ₀.Pt) (hout : Γ₀.eval q ∉ interior (disc D x ε))
    (hq : Γ₀.eval q ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore q) =
      l • D.Γ.dir (D.Γ.strandBefore (origPt D x M q)) := by
  obtain ⟨i, m, θ⟩ := q
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_not_mem_interior D x M hε ⟨i, (m, θ)⟩ hout
  dsimp only at h1 h2
  have hparam : (origPt D x M ⟨i, (m, θ)⟩).2.2.val = (M.kind ⟨i, m⟩).origParam ε θ.val :=
    origPt_param D x M hε ⟨i, (m, θ)⟩
  have hev := eval_eq_edgePt D x M ⟨i, m⟩ θ h1 h2
  dsimp only at hev
  by_cases hθ : θ.val = 0
  · have hne1 : M.kind ⟨i, m⟩ ≠ StrandKind.cutEndS := by
      intro hk
      apply hq
      rw [SpliceModel.orig, hk] at hev
      rw [hev, hθ]
      show edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x + ε + 0 * (1 - τs D x - ε)) ∈ _
      rw [edgePoint_s_mem_disc_iff D x ε hε, zero_mul, add_zero]
      have := θsIn_lt_cut D x ε hε
      have := hε.pos
      exact ⟨by linarith, by linarith⟩
    have hne2 : M.kind ⟨i, m⟩ ≠ StrandKind.cutEndT := by
      intro hk
      apply hq
      rw [SpliceModel.orig, hk] at hev
      rw [hev, hθ]
      show edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x + ε + 0 * (1 - τt D x - ε)) ∈ _
      rw [edgePoint_t_mem_disc_iff D x ε hε, zero_mul, add_zero]
      have := θtIn_lt_cut D x ε hε
      have := hε.pos
      exact ⟨by linarith, by linarith⟩
    have hz : (origPt D x M ⟨i, (m, θ)⟩).2.2.val = 0 := by
      rw [hparam, hθ]; exact StrandKind.origParam_zero ε _ hne1 hne2 h1 h2
    rw [Γ₀.strandBefore_of_zero _ hθ, D.Γ.strandBefore_of_zero _ hz]
    dsimp only
    obtain ⟨l, hl, hd⟩ := StrandKind.dir_pred_eq_smul ε hε (M.kind ⟨i, m⟩) hne1 hne2 h1 h2
    refine ⟨l, hl, ?_⟩
    have hp := M.kind_pred ⟨i, m⟩
    dsimp only at hp
    rw [M.dir_eq, hp]
    exact hd
  · have hz : (origPt D x M ⟨i, (m, θ)⟩).2.2.val ≠ 0 := by
      rw [hparam]; exact StrandKind.origParam_ne_zero ε hε _ h1 h2 θ.2.1 hθ
    rw [Γ₀.strandBefore_of_ne_zero _ hθ, D.Γ.strandBefore_of_ne_zero _ hz]
    obtain ⟨l, hl, hd⟩ := StrandKind.dir_eq_smul_orig ε hε (M.kind ⟨i, m⟩) h1 h2
    refine ⟨l, hl, ?_⟩
    show Γ₀.dir ⟨i, m⟩ = l • D.Γ.dir (M.orig ⟨i, m⟩)
    rw [M.dir_eq]
    exact hd

theorem outsideEquiv_dir_pos_before (q : D.Γ.Outside (disc D x ε))
    (hq : D.Γ.eval q.1 ∉ disc D x ε) :
    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore (outsideEquiv D x M hε q).1) =
      l • D.Γ.dir (D.Γ.strandBefore q.1) := by
  have hφ := origPt_outsideEquiv D x M hε q
  have hout := (outsideEquiv D x M hε q).2
  rw [← hφ] at hq ⊢
  rw [eval_origPt D x M hε _ hout] at hq
  exact dir_strandBefore_origPt D x M hε _ hout hq

/-- The outer crossings of `D` are the crossings other than `x`; all crossings of `D₀` are outer. -/
def outerEquiv : D.OuterCrossing (disc D x ε) ≃ (toDiagram D x M hε).OuterCrossing (disc D x ε) :=
  ((Equiv.subtypeEquivRight (fun y => by
      show D.Γ.crossingPoint y ∉ interior (disc D x ε) ↔ y ≠ x
      rw [inner_iff_D D x hε])).trans (crossingEquiv D x M hε).symm).trans
    (Equiv.subtypeUnivEquiv (no_inner_toDiagram D x M hε)).symm

theorem outsideEquiv_outerOverPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerOverPt y) =
      (toDiagram D x M hε).outerOverPt (outerEquiv D x M hε y) := by
  have hy : y.1 ≠ x := fun h => y.2 ((inner_iff_D D x hε y.1).mpr h)
  have horig : origCrossing D x M hε (outerEquiv D x M hε y).1 = y.1 :=
    origCrossing_liftCrossing D x M hε y.1 hy
  have hmem := overStrand₀_mem D x M hε (outerEquiv D x M hε y).1
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε _ hmem
  have hs : M.orig (overStrand₀ D x M hε (outerEquiv D x M hε y).1) = D.overStrand y.1 := by
    rw [orig_overStrand₀ D x M hε (outerEquiv D x M hε y).1, horig]
  unfold outsideEquiv
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show D.visitPt (D.overVisit y.1) = origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))
  refine (Shadow.mk_eq_mk_iff (D.overStrand y.1)
    (M.orig (overStrand₀ D x M hε (outerEquiv D x M hε y).1)) _ _).mpr ⟨hs.symm, Subtype.ext ?_⟩
  show D.crossingParam y.1 (D.over_mem y.1) = (origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))).2.2.val
  rw [origPt_param D x M hε
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).overVisit (outerEquiv D x M hε y).1))]
  show D.crossingParam y.1 (D.over_mem y.1) =
    (M.kind (overStrand₀ D x M hε (outerEquiv D x M hε y).1)).origParam ε
      ((toDiagram D x M hε).crossingParam (outerEquiv D x M hε y).1 hmem)
  rw [crossingParam_toDiagram D x M hε (outerEquiv D x M hε y).1 hmem,
    StrandKind.origParam_liftParam ε hε _ h1 h2]
  exact D.crossingParam_congr horig.symm hs.symm _ _

theorem outsideEquiv_outerUnderPt (y : D.OuterCrossing (disc D x ε)) :
    outsideEquiv D x M hε (D.outerUnderPt y) =
      (toDiagram D x M hε).outerUnderPt (outerEquiv D x M hε y) := by
  have hy : y.1 ≠ x := fun h => y.2 ((inner_iff_D D x hε y.1).mpr h)
  have horig : origCrossing D x M hε (outerEquiv D x M hε y).1 = y.1 :=
    origCrossing_liftCrossing D x M hε y.1 hy
  have hmem : (toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1 ∈
      (outerEquiv D x M hε y).1.val := (toDiagram D x M hε).under_mem _
  obtain ⟨h1, h2⟩ := kind_ne_arc_of_mem D x M hε _ hmem
  have hs : M.orig ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1) =
      D.underStrand y.1 := by
    rw [toDiagram_underStrand_orig D x M hε (outerEquiv D x M hε y).1, horig]
  unfold outsideEquiv
  refine (Equiv.symm_apply_eq _).mpr ?_
  apply Subtype.ext
  show D.visitPt (D.underVisit y.1) = origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))
  refine (Shadow.mk_eq_mk_iff (D.underStrand y.1)
    (M.orig ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1)) _ _).mpr
    ⟨hs.symm, Subtype.ext ?_⟩
  show D.crossingParam y.1 (D.under_mem y.1) = (origPt D x M
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))).2.2.val
  rw [origPt_param D x M hε
    ((toDiagram D x M hε).visitPt ((toDiagram D x M hε).underVisit (outerEquiv D x M hε y).1))]
  show D.crossingParam y.1 (D.under_mem y.1) =
    (M.kind ((toDiagram D x M hε).underStrand (outerEquiv D x M hε y).1)).origParam ε
      ((toDiagram D x M hε).crossingParam (outerEquiv D x M hε y).1 hmem)
  rw [crossingParam_toDiagram D x M hε (outerEquiv D x M hε y).1 hmem,
    StrandKind.origParam_liftParam ε hε _ h1 h2]
  exact D.crossingParam_congr horig.symm hs.symm _ _

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
  sorry

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

/-- The mixed shadow is a splice model (index arithmetic on `ZMod.val`). -/
def mixedModel (h : (sS D x).1 ≠ (tS D x).1) : SpliceModel D x ε (mixedShadow D x ε) where
  kind := mixedKind D x ε
  kind_injective := by
    sorry
  kind_surj := by
    sorry
  kind_occurs := by
    sorry
  kind_pred := by
    sorry
  tail_eq := by
    sorry
  dir_eq := by
    sorry
  cut_val := by
    sorry

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

theorem two_le_dd (h : (sS D x).1 = (tS D x).1) : 2 ≤ dd D x := by
  sorry

theorem dd_add_two_le (h : (sS D x).1 = (tS D x).1) : dd D x + 2 ≤ kI D x := by
  sorry

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
  sorry

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

/-- The self shadow is a splice model. -/
def selfModel (h : (sS D x).1 = (tS D x).1) : SpliceModel D x ε (selfShadow D x ε h) where
  kind := selfKind D x ε h
  kind_injective := by
    sorry
  kind_surj := by
    sorry
  kind_occurs := by
    sorry
  kind_pred := by
    sorry
  tail_eq := by
    sorry
  dir_eq := by
    sorry
  cut_val := by
    sorry

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
