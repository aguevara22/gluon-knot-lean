import SM.LinkDiagramRecord
import SM.LinkMoves
import SM.LinkRecordExtras
import SM.LinkDiagramExtras
import SM.LinkRecordExtension

/-! # Skeleton A — the oriented smoothing `exists_smoothing` / `smoothing_record`
(Chapter-3 representation layer; lane sm-3:1084-1103).  Draft 2026-09-13, architect tag A.

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

/-- Closed edge segments are closed sets (continuous image of `[0,1]`). -/
theorem isClosed_seg (Γ : Shadow) (e : Γ.Strand) : IsClosed (Γ.seg e) := by
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

omit M hε in
/-- Two adjacent strands of a generic shadow meet only at their common vertex (independent
directions meet once; positively collinear consecutive edges only touch). -/
theorem seg_inter_succ (Γ : Shadow) (hΓ : Γ.Generic) (u : Γ.Strand) :
    Γ.seg u ∩ Γ.seg ⟨u.1, u.2 + 1⟩ = {Γ.head u} := by
  sorry

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
    ⟨max 0 (min ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val) (1 / 2)),
      le_max_left _ _, by
        have : min ((M.kind ⟨q.1, q.2.1⟩).origParam ε q.2.2.val) (1 / 2) ≤ 1 / 2 := min_le_right _ _
        rw [max_lt_iff]; constructor <;> linarith⟩)⟩

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
`Record.SmoothComps` of `D.record` at the over occurrence; and the successor of `D₀` is the first
return of the reconnected successor (`Record.smoothSucc`).  The last two facts are the per-case
statements `*_cls_visit` and `*_succ`, proved from the explicit traversal coordinates. -/

section RecordBridge

variable {ε} {Γ₀ : Shadow} (M : SpliceModel D x ε Γ₀) (hε : SmallEps D x ε)
include M hε

/-- The over occurrence of `x`, the erased occurrence of `Record.smooth`. -/
abbrev xv : D.Γ.Visit := D.overVisit x

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

end RecordBridge

/-! ### 8a. Component classification and successor law, per case -/

/-- The `SmoothComps` class of an untouched component `i₀` of `D`: the reconnect-cycle of any of
its occurrences, or the crossing-free circle `i₀`. -/
def oldCls (i₀ : Fin D.Γ.c) : (D.record.smooth (xv D x)).comps :=
  if h : ∃ w : D.Γ.Visit, D.compOf w = i₀ then Sum.inl (Quotient.mk _ (Classical.choose h))
  else Sum.inr ⟨i₀, fun w hw => h ⟨w, hw⟩⟩

section MixedRecord

/-- The class map of the mixed case: the merged component is the reconnect-cycle of `x`
(`= ⟦τx⟧`, `Record.reconnect_sameCycle_pair_of_mixed`). -/
def mixedCls : Fin ((othersM D x).card + 1) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
    (fun l => oldCls D x ((othersM D x).orderEmbOfFin rfl l))

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 ≠ (tS D x).1)

include h in
theorem mixedCls_bijective : Function.Bijective (mixedCls D x) := by
  sorry

theorem mixedCls_visit (v : (mixedShadow D x ε).Visit) :
    mixedCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (mixedModel D x ε h) hε v, smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩ := by
  sorry

/-- The traversal coordinate of an occurrence of the merged component, in terms of the coordinate
of its original occurrence in `D`: on `[0, k_i)` old edges of `i` after `a` come first
(`coord − (a.val+1)`, wrapping), the cut piece `[P_i a, s⁻]` sits at `k_i − 1`, `[t⁺, P_j(b+1)]` at
`k_i + 1`, old edges of `j` at `k_i + 2 + ((m − b − 1) mod k_j)`, `[P_j b, t⁻]` at `k_i+1+k_j`,
`[s⁺, P_i(a+1)]` at `k_i+3+k_j`. -/
theorem mixed_visitCoord (v : (mixedShadow D x ε).Visit)
    (hv : v.2.val.1 = (0 : Fin ((othersM D x).card + 1))) :
    (toDiagram D x (mixedModel D x ε h) hε).visitCoord v =
      (v.2.val.2.val : ℝ) + (toDiagram D x (mixedModel D x ε h) hε).crossingParam v.1 v.2.2 := by
  sorry

/-- **Successor law, mixed case**: the successor of `D₀` is the first return of the reconnected
successor.  Proof: `cycNext_unique_on` in `D₀`; the candidate `smoothSucc` is on the same
component (`mixedCls_visit` + `smooth_comp_eq_iff`), differs from `v` unless alone, and nothing
lies strictly between because the merged coordinate is a rotation of a strictly increasing function
of the "reconnect coordinate" (rotation of `D`'s coordinate at `x` on `i`, shifted by `k_i` and
rotated at `τx` on `j`), on which `smoothSucc` is the cyclic successor
(`Record.smooth_succ_val_of_not_mem`, `smooth_succ_val_of_succ_eq*`, `nextVisit_no_between`). -/
theorem mixed_succ (v : (mixedShadow D x ε).Visit) :
    origVisit D x (mixedModel D x ε h) hε ((toDiagram D x (mixedModel D x ε h) hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x (mixedModel D x ε h) hε v,
        smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩).1 := by
  sorry

/-- The record bridge, mixed case. -/
def mixedRecordIso :
    RecordIso (toDiagram D x (mixedModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCls D x (mixedModel D x ε h) hε (mixedCls D x) (mixedCls_bijective D x h)
    (mixedCls_visit D x hε h) (mixed_succ D x hε h)

end MixedRecord

section SelfRecord

/-- The class map of the self case: `A ↦ ⟦τx⟧` (occurrences after `x`, before `τx`),
`B ↦ ⟦x⟧`. -/
def selfCls : Fin ((othersS D x).card + 2) → (D.record.smooth (xv D x)).comps :=
  Fin.cases (Sum.inl (Quotient.mk _ (D.record.pair (xv D x))))
    (Fin.cases (Sum.inl (Quotient.mk _ (xv D x)))
      (fun l => oldCls D x ((othersS D x).orderEmbOfFin rfl l)))

variable {ε} (hε : SmallEps D x ε) (h : (sS D x).1 = (tS D x).1)

include h in
theorem selfCls_bijective : Function.Bijective (selfCls D x) := by
  sorry

theorem selfCls_visit (v : (selfShadow D x ε h).Visit) :
    selfCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp
      ⟨origVisit D x (selfModel D x ε h) hε v, smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩ := by
  sorry

/-- **Successor law, self case** (same method as `mixed_succ`; on `A` the coordinate is a rotation
of `D`'s coordinate at `x`, on `B` at `τx`). -/
theorem self_succ (v : (selfShadow D x ε h).Visit) :
    origVisit D x (selfModel D x ε h) hε ((toDiagram D x (selfModel D x ε h) hε).nextVisit v) =
      ((D.record.smooth (xv D x)).succ ⟨origVisit D x (selfModel D x ε h) hε v,
        smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩).1 := by
  sorry

/-- The record bridge, self case. -/
def selfRecordIso :
    RecordIso (toDiagram D x (selfModel D x ε h) hε).record (D.record.smooth (xv D x)) :=
  recordIsoOfCls D x (selfModel D x ε h) hε (selfCls D x) (selfCls_bijective D x h)
    (selfCls_visit D x hε h) (self_succ D x hε h)

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
