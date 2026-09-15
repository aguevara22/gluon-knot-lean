# PLAN_A — `exists_smoothing` / `smoothing_record` (oriented smoothing, sm-3:1084-1103)

Architect tag **A**, 2026-09-13.  Skeleton: `work/drafts/smoothing/Skeleton_A.lean` (1404 lines,
compiles with `lake env lean`, 0 errors, 119 declarations carrying `sorry`, goal theorems depend on
`sorryAx` + standard axioms only).  Emphasis of this variant: explicit vertex tuples by `ZMod.val`
index arithmetic, an explicit `ε` as a min of finitely many positive numbers, and **one** abstract
"splice model" through which every geometric lemma is proved exactly once for both the self- and
the mixed-crossing case.

## 0. What is proved, and in which form

Fixed definitions used unchanged: `IsOrientedSmoothing`/`OrientedSmoothingData` (LinkMoves.lean
713-745), `LocalFrame`/`Clean`/`OutsideMatch`/`IsDisc` (LinkMoves 96-345), `Shadow.Arc`/`IsArc`/
`ArcCover` (LinkMoves 155-232), `Diagram.OverOn/UnderOn` (289-292), `Shadow`/`Generic`/`Diagram`
(LinkDiagram 83, 394, 490), `Record.smooth` (LinkRecord 895), `Diagram.record` (LinkDiagramRecord 500).

Goal theorems (all in the skeleton, proved from the chain):

```
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀
theorem exists_smoothing_record (D) (x) :
    ∃ D₀, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x)))
theorem exists_smoothing_record_visit (D) (x) (v : D.Γ.Visit) (hv : v.1 = x) :
    ∃ D₀, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth v))
theorem smoothingRecordClause_smoothDiagram (D) (x) :
    SmoothingRecordClause Diagram.record (fun _ v => v) D x (smoothDiagram D x (eps D x) (eps_small D x))
theorem exists_smoothing_counts (D) (x) : ∃ D₀, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso …) ∧
    D₀.componentCount = (if D.record.IsSelfCrossing (D.overVisit x) then c + 1 else c − 1) ∧
    1 ≤ D₀.componentCount ∧ Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing
```
plus the named construction `Smoothing.smoothDiagram D x ε (hε : SmallEps D x ε) : Diagram` with
`isOrientedSmoothing_smoothDiagram`, `smoothDiagram_record` (the RecordIso for the construction) and
`smoothDiagram_componentCount` (`c+1` / `c−1` directly from the construction).

**Design decision on the form of `smoothing_record`.**  The relational statement
`IsOrientedSmoothing D x D₀ → RecordIso D₀.record (D.record.smooth v)` is *not* provable from the
fixed definitions without real topology: `OutsideMatch.φ` is only a bijection of outside traversal
points with equal `eval`, `dir_pos`, and crossing correspondence; it carries no information about
which component a point lies on or about the cyclic order along components, so the successor of
`D₀.record` cannot be recovered from an arbitrary witness (one would need connectedness of the
outside arcs of the trace).  Every consumer named in the lane (rp:record-polynomial and lp:core's
(N, b) inductions, sm-3:1084-1103 / 1236-1300; mp:stack) only needs *some* smoothing with the
record `D.record.smooth v`; the constructive `exists_smoothing_record` / `exists_smoothing_record_visit`
(any occurrence `v` of `x`, via `Record.smoothPairIso`, LinkRecord 1040) is that statement.  The
counts `c(D₀) = c ± 1 ≥ 1` and `N(D₀) = N − 1` follow from `RecordIso.componentCount_eq`,
`Record.componentCount_smooth` (LinkRecordExtras 333) and `IsOrientedSmoothing.card_crossing`
(LinkMoves 1051), packaged in `exists_smoothing_counts`.  Record this in work/AUTHOR_NOTES.md when
the lane lands.

## 1. The construction

Notation (skeleton §0): `s = D.overStrand x = ⟨i, a⟩`, `t = D.underStrand x = ⟨j, b⟩`,
`p = crossingPoint x`, `τs = crossingParam x s`, `τt = crossingParam x t` (both in `(0,1)`,
LinkDiagram 1421-1430), `es = edge P_i a`, `et = edge P_j b` (nonzero, `det es et ≠ 0`:
LinkDiagram 540).  `p = P_i a + τs•es = P_j b + τt•et`.

### 1.1 Clearance radius and `ε` (skeleton §1-§2) — which finite sets are avoided

* `others := univ.filter (e ≠ s ∧ e ≠ t)` (nonempty: `⟨i, a−1⟩`).
* **Key lemma** `crossingPoint_not_mem_seg_other`: for `e ∉ {s,t}`, `p ∉ seg e`.  Proof: if `e` is
  non-adjacent to `s`, `{s, e}` is a crossing with common point `p`, so by
  `Generic.crossingPoint_injective` (LinkDiagram 463) `{s,e} = x`, i.e. `e = t`.  If `e = s+1`:
  `p ∈ interior s` (LinkDiagram 456); `p ∈ interior (s+1)` would be a triple point `s, t, s+1`
  (`no_triple`; `s+1 ≠ t` by non-adjacency); `p = tail (s+1) = head s` contradicts `tail_off (s+1) t`
  (`incident (a+1) b` fails since `b ∉ {a, a+1}`); `p = head (s+1) = tail (s+2)` contradicts
  `tail_off (s+2) s` (`incident (a+2) a` fails for `k ≥ 3`).  Symmetric for `e = s−1`, and for `t`.
* `r₁ := others.inf' (fun e => infDist p (seg e))` — a **min over finitely many positive reals**:
  positive by `IsClosed.notMem_iff_infDist_pos` with `isClosed_seg` (continuous image of `[0,1]`).
  Consequences: `r₁ ≤ dist p q` for `q ∈ seg e`, `e ∉ {s,t}`; every vertex is at distance `≥ r₁`
  (`P_i m` is the tail of `⟨i,m⟩` or head of `⟨i,m−1⟩`, one of which is `∉ {s,t}`); every other
  crossing point is at distance `≥ r₁` (one strand of `y ≠ x` is `∉ {s,t}`); and
  `r₁ ≤ τs‖es‖, (1−τs)‖es‖, τt‖et‖, (1−τt)‖et‖` (via the vertices `tail s`, `head s`, …).
* `SmallEps ε := 0 < ε ∧ ε < τs ∧ ε < 1−τs ∧ ε < τt ∧ ε < 1−τt ∧ ε‖es‖ < r₁ ∧ ε‖et‖ < r₁`;
  `eps := min(min(τs, 1−τs), min(τt, 1−τt), r₁/‖es‖, r₁/‖et‖) / 2` and `eps_small`.
  So the four cut points `s∓ = p ∓ ε es`, `t∓ = p ∓ ε et` lie in the open edges and in
  `ball p r₁`, and the two arcs lie in `ball p (ε·max(‖es‖,‖et‖)) ⊂ ball p r₁`.
* Disc: `disc := closedBall p r`, `r := (ε·max(‖es‖,‖et‖) + r₁)/2` (sup metric of `ℝ×ℝ`: a square,
  `IsDisc` by `isDisc_closedBall`, LinkMoves 100; `interior_closedBall`, `frontier_closedBall`).
  Frontier parameters `θsIn/Out = τs ∓ r/‖es‖`, `θtIn/Out = τt ∓ r/‖et‖`, all in `(0,1)` and
  `θsIn < τs − ε < τs + ε < θsOut`.

### 1.2 Strand kinds and the splice model (skeleton §4)

Every strand of the smoothed shadow has one of seven kinds (`StrandKind D x`):
`old e` (`e ∉ {s,t}`, unchanged), `cutStartS = [P_i a, s⁻]`, `cutEndS = [s⁺, P_i(a+1)]`,
`cutStartT`, `cutEndT`, `arcST = [s⁻, t⁺]`, `arcTS = [t⁻, s⁺]`.  Kind-level data: `tail`, `dir`
(`cutStartS ↦ (τs−ε)•es`, `cutEndS ↦ (1−τs−ε)•es`, arcs `↦ ε•(es+et)`), `seg`, `interior`, `orig`
(the strand of `D` a kind is a piece of), `origParam`/`liftParam` (affine parameter rescaling of the
cut pieces), and the cyclic laws `pred`/`succ` which encode the **reconnection**:
`succ cutStartS = arcST`, `succ arcST = cutEndT`, `succ cutStartT = arcTS`, `succ arcTS = cutEndS`,
`succ (old (s−1)) = cutStartS`, `succ cutEndS = old (s+1)`, etc.

```
structure SpliceModel (ε) (Γ₀ : Shadow) where
  kind : Γ₀.Strand → StrandKind D x
  kind_injective ; kind_surj : ∀ κ, κ.Occurs → ∃ u, kind u = κ ; kind_occurs : ∀ u, (kind u).Occurs
  kind_pred : ∀ u, kind ⟨u.1, u.2 − 1⟩ = (kind u).pred
  tail_eq : ∀ u, Γ₀.tail u = (kind u).tail ε ;  dir_eq : ∀ u, Γ₀.dir u = (kind u).dir ε
```
(`Occurs κ := κ ≠ old s ∧ κ ≠ old t`.)  From these six laws everything else about `Γ₀` is derived
once (§6): `seg`/`interior`/`head`, `Adjacent u u' ↔ (kind u).Adj (kind u')`,
`IncidentTail ↔ .Incident`, genericity, the crossing correspondence, the over data, cleanness, the
arcs, the outside match, hence `OrientedSmoothingData`.  This is the requested factoring: the
"re-vertexing by inserting two vertices on two strands and swapping the successor links" *is* the
kind map with its `pred` law; the two concrete shadows only have to exhibit it.

### 1.3 The mixed case `i ≠ j` (skeleton §7a): two components join into one

Merged component, `N = k_i + k_j + 4` vertices, `Q : ZMod N → Plane` by `ZMod.val` cases:
```
Q m = P_i (a + 1 + m.val)            m.val < k_i        (Q (k_i−1) = P_i a)
Q k_i = s⁻ ;  Q (k_i+1) = t⁺
Q m = P_j (b + 1 + (m.val − k_i − 2)) k_i+2 ≤ m.val < k_i+2+k_j   (Q (k_i+1+k_j) = P_j b)
Q (k_i+2+k_j) = t⁻ ;  Q (k_i+3+k_j) = s⁺ ;   Q N = Q 0 = P_i (a+1)
```
Edge kinds by index (`mergedKindIdx`): `0…k_i−2` old `⟨i, a+1+m⟩`; `k_i−1` cutStartS; `k_i` arcST;
`k_i+1` cutEndT; `k_i+2…k_i+k_j` old `⟨j, b+1+(m−k_i−2)⟩`; `k_i+1+k_j` cutStartT; `k_i+2+k_j` arcTS;
`k_i+3+k_j` cutEndS.  Old vertices are addressed as `P_i (a + 1 + (m.val : ZMod k_i))`, so no cast
between `ZMod` sizes appears; `ZMod.val_natCast`, `ZMod.natCast_zmod_val`, `ZMod.val_add` do the
arithmetic.  Shadow: `mixedShadow := ⟨othersM.card + 1, _, Fin.cases mergedComp (fun l => comp (othersM.orderEmbOfFin l))⟩`
with `othersM = (univ.erase i).erase j` (`card + 2 = c`); `Fin.cases` reduces definitionally on
`0` and `Fin.succ`, so `comp 0 = mergedComp` and `comp l.succ = …` are `rfl`.  Kind map
`mixedKind ⟨0, m⟩ = mergedKindIdx m.val`, `mixedKind ⟨l.succ, m⟩ = old ⟨emb l, m.val⟩`.

### 1.4 The self case `i = j` (skeleton §7b): one component splits into two

`bS := (t.2.val : ZMod k_i)` (transport of `b` by value), `d := (bS − a).val ∈ [2, k−2]`
(non-adjacency; `two_le_dd`, `dd_add_two_le`).
```
A (d+2 vertices):  Q_A m = P (a+1+m.val) (m.val < d, so Q_A (d−1) = P b) ; Q_A d = t⁻ ; Q_A (d+1) = s⁺
   edges: 0…d−2 old ⟨i,a+1+m⟩ ; d−1 cutStartT ; d arcTS ; d+1 cutEndS  (wraps to P(a+1))
B (k−d+2 vertices): Q_B m = P (bS+1+m.val) (m.val < k−d, so Q_B (k−d−1) = P a) ; Q_B (k−d) = s⁻ ; Q_B (k−d+1) = t⁺
   edges: 0…k−d−2 old ⟨i,b+1+m⟩ ; k−d−1 cutStartS ; k−d arcST ; k−d+1 cutEndT (wraps to P(b+1))
```
`selfShadow := ⟨othersS.card + 2, _, Fin.cases compA (Fin.cases compB (fun l => comp (emb l)))⟩`,
`othersS = univ.erase i`.  `A` carries the occurrences met after `x` and before `τx`
(`A ↦ ⟦τx⟧ = ⟦underVisit x⟧` in `Record.SmoothComps`), `B ↦ ⟦x⟧`.

### 1.5 The smoothed diagram and the record bridge (skeleton §6c, §8)

`toDiagram M hε : Diagram` on any model: `overStrand₀ y := if orig y.fst = D.overStrand (origCrossing y) then y.fst else y.snd`
where `y.fst := Classical.choose y.2`, `y.snd := other`, and `origCrossing y := {orig y.fst, orig y.snd}`
(a crossing of `D` ≠ `x` by `isCrossing_orig`).  `smoothDiagram D x ε hε := if h : i = j then toDiagram (selfModel h) hε else toDiagram (mixedModel h) hε`.

Record bridge (§8): `origVisit v := ⟨origCrossing v.1, orig v.2⟩` is a bijection
`Γ₀.Visit ≃ {w // SmoothKeep (overVisit x) w}` (`visitEquiv`); twin/bit/sign transport strand-wise;
`recordIsoOfCls` assembles the `RecordIso` from a component classification
`cls : Fin Γ₀.c → (D.record.smooth xv).comps` (bijective, compatible with `origVisit`) and the
**successor law** `origVisit (D₀.nextVisit v) = ((D.record.smooth xv).succ ⟨origVisit v, _⟩).1`.
Per case: `mixedCls = Fin.cases ⟦xv⟧ (oldCls ∘ emb)`, `selfCls = Fin.cases ⟦τ xv⟧ (Fin.cases ⟦xv⟧ (oldCls ∘ emb))`,
`oldCls i₀ := if ∃ w, compOf w = i₀ then Sum.inl ⟦choose⟧ else Sum.inr ⟨i₀,_⟩`.

## 2. Lemma chain: statements, sketches, sizes

Notation: (S) = statement already in the skeleton with `sorry`; est. = estimated proof lines.
Dependency order is top to bottom within a block; blocks A→B→C→D→E→F→G.  Total ≈ 2 950 lines.

### Block A — clearance and ε (skeleton §1-3), ~330 lines
| lemma | sketch | est. |
|---|---|---|
| `others_nonempty` | witness `⟨i, a−1⟩`: `≠ s` (−1 ≠ 0, `k ≥ 3`), `≠ t` (else adjacent) | 15 |
| `crossingPoint_not_mem_seg_other` | §1.1 key lemma; cases non-adjacent / `e = s±1` / `e = t±1`; uses LinkDiagram 414, 456, 463, `Generic.tail_off`, `no_triple`, `adjacent_mk_iff` (150) | 90 |
| `isClosed_seg` | `edgeSegment = (fun θ => P i + θ•edge) '' Icc 0 1`, `IsCompact.isClosed` of `isCompact_Icc.image` | 20 |
| `r₁_pos` | `Finset.lt_inf'_iff`; each term positive by `IsClosed.notMem_iff_infDist_pos` + key lemma | 15 |
| `r₁_le_dist` | `Finset.inf'_le` + `Metric.infDist_le_dist_of_mem` | 10 |
| `r₁_le_dist_tail` | `P_l m = tail ⟨l,m⟩ = head ⟨l,m−1⟩`; one of the two strands is `∉ {s,t}` (case split, `k ≥ 3`) | 40 |
| `r₁_le_dist_crossingPoint` | `y ≠ x` ⇒ some strand of `y` is `∉ {s,t}` (`eq_pair_other`, 325) and the crossing point lies on it | 25 |
| `r₁_le_τs_mul` … (4) | `tail s ∈ seg ⟨i,a−1⟩`, `dist p (tail s) = τs‖es‖` (`norm_smul`); head via `⟨i,a+1⟩` | 40 |
| `eps_small` | `min`/`div` arithmetic; `‖es‖ > 0` | 30 |
| `sMinus_eq_edgePoint` … (4), `dist_sMinus` | unfold `edgePoint`, `pt_eq_s`, `smul_sub`, `norm_smul` | 40 |

### Block B — kind-level facts (§4, `StrandKind`), ~300 lines
| lemma | sketch | est. |
|---|---|---|
| `pred_succ`, `succ_pred`, `succ_occurs`, `pred_occurs` | case on `κ`; for `old e` the `if`s: `e = s−1`, `e = t−1` cases use `s ≠ t`, `¬Adjacent s t` to exclude coincidences (`a−1 = b−1 ⇒ s = t`; `(a−1)+1 = a`) | 80 |
| `head_eq_tail_succ` | case on `κ`: `P_i a + (τs−ε)es = p − ε es` (from `pt_eq_s`), `s⁻ + ε(es+et) = t⁺`, `s⁺ + (1−τs−ε)es = P_i(a+1)`, … ; for `old e` the three `if` branches (`e = s−1`: `head = P_i a = tail cutStartS`) | 60 |
| `tail_add_smul_dir`, `seg_subset_seg_orig`, `seg_old`, `interior_old` | algebra: `P_i a + θ(τs−ε)es = edgePoint … (θ(τs−ε))`; `origParam` maps `[0,1]` into `[0,1]` under `SmallEps` | 60 |
| `seg_arc_subset_ball`, `dist_cut_lt` | `‖(μ−1)ε es + μ ε et‖ ≤ ε max` (triangle, `norm_smul`), `< r₁` by `SmallEps` | 40 |
| `SpliceModel.kind_succ` | from `kind_pred` at `⟨u.1, u.2+1⟩` and `pred_succ`/injectivity | 15 |
| `seg_eq`, `interior_eq`, `head_eq`, `eval_eq` | unfold `Shadow.seg = edgeSegment`, `edgePoint = P m + θ•edge`, `tail_eq`, `dir_eq` | 30 |
| `adjacent_iff`, `incidentTail_iff` | `Adjacent ⟨l,m⟩ ⟨l,m'⟩ ↔ m' − m ∈ {−1,0,1}` (`adjacent_mk_iff`) ↔ `u' ∈ {pred u, u, succ u}` ↔ kinds by `kind_pred`, `kind_succ`, injectivity | 50 |
| `adjacent_old_iff` | `Adj (old e) (old e') ↔ e' ∈ {e, e±1}` since `pred (old e) = old (e−1)` when `e ≠ s+1, t+1` (and `e' ≠ s,t` excludes the cut branches) | 30 |

### Block C — the disc and the trace of `D` (§5, `DiscD`), ~360 lines
| lemma | sketch | est. |
|---|---|---|
| `discRadius_pos/_lt_r₁`, `arc_lt_discRadius` | `SmallEps`, midpoint arithmetic | 25 |
| `mem_seg_of_mem_disc` | `q ∈ seg e ∩ disc`, `e ∉ {s,t}` ⇒ `r₁ ≤ dist p q ≤ r < r₁` | 15 |
| `crossingPoint_ne_not_mem_disc`, `tail_not_mem_disc` | from `r₁_le_dist_crossingPoint`, `r₁_le_dist_tail` | 15 |
| `θ*` bounds (8) | `r < r₁ ≤ τs‖es‖` etc.; `ε‖es‖ < r` | 40 |
| `edgePoint_s_mem_disc_iff` (+ ball, + t) | `dist (P_i a + θ es) p = |θ − τs| ‖es‖` (`pt_eq_s`, `norm_smul`), divide | 60 |
| `θ₀_mem` | `liftParam` of the frontier parameters lies in `[0,1)`: `θsIn/(τs−ε) ∈ (0,1)` since `0 < θsIn < τs − ε` | 30 |
| `traversalBetween_same_edge` | unfold `traversalBetween`, `traversalKey = val + θ`; the two wrap disjuncts are impossible since `key(a,θ₁) < key(a,θ₂)`; the middle key forces `r.1.val = a.val` (`ZMod.val_injective`) | 40 |
| `traversalBetween_span_two` | same with keys in `[m.val + θ₁, m.val + 2 + θ₂)`, three sub-cases by `⌊key⌋` | 50 |
| `clean_D` | `frontier_injOn`: a frontier point is on `s` or `t` (`mem_seg_of_mem_disc`); two traversal points with equal eval on the same edge have equal parameter (`edge ≠ 0`, `smul_right_injective`); on `s` and `t` the common point is `p` (`common_point_unique`, 414), not on the frontier. `exits`: the vertex `⟨l,(0,0)⟩` (`tail_not_mem_disc`) | 60 |
| `center_mem` | `interior_disc`, `mem_ball_self` | 5 |
| `arcS_ne_arcT` | components differ or edge labels `a ≠ b` | 10 |
| `arcCover_D` | `isArc`: ends on the sphere (`edgePoint_s_mem_disc_iff` at equality), inner points via `traversalBetween_same_edge` + `edgePoint_s_mem_ball_iff`; `mem_iff`: `eval q ∈ disc` ⇒ on `s`/`t` with parameter in `[θIn, θOut]` ⇒ `Mem`; `disjoint`: different edge labels | 90 |
| `overOn_arcS`, `underOn_arcT` | `visitPt (overVisit x) = ⟨i,(a,τs)⟩`, `θsIn < τs < θsOut` | 15 |
| `inner_iff_D` | `←` center; `→` `crossingPoint_ne_not_mem_disc` | 10 |

### Block D — model-level genericity and crossings (§6a-6b), ~520 lines
| lemma | sketch | est. |
|---|---|---|
| `seg_inter_succ` | `q = tail + α e_u = head + β e_{u+1}`; if `det ≠ 0`: `intersection_parameters_unique` (Segment 55) gives `α = 1, β = 0`; if `det = 0`: `RegularPair` (RegularPairs 8) ⇒ `e_{u+1} = λ e_u`, `λ > 0` (`scalar_of_det_zero`, EuclideanPlane 75; not negative), then `(α−1) = βλ` forces `α = 1, β = 0` | 60 |
| `kind_disjoint` | cases: two cut pieces of one strand (parameter intervals `[0,τ−ε]`, `[τ+ε,1]` disjoint, `edge ≠ 0`); cut piece of `s` vs cut piece of `t` (common point would be in `seg s ∩ seg t = {p}` by `common_point_unique`, but `p` has parameter `τ` outside both pieces); arc vs arc (`(μ−1) = ν ∧ μ = ν−1` impossible, via `intersection_parameters_unique` with `det es et ≠ 0`); arc vs non-adjacent cut piece (same independence computation: `με = 0`, `λ = −ε`); arc vs old (`seg_arc_subset_ball` + `r₁_le_dist`) | 120 |
| `cut_inter_old` | if `Adjacent (orig κ) e`, `e = orig κ ± 1`; `seg (s−1) ∩ seg s = {tail s}` (`seg_inter_succ`), and `tail s ∉ cutEndS`; the touching pairs are `Adj` | 50 |
| `regular` | strand `u` of component `l` with kinds `κ = kind ⟨l,m−1⟩`, `κ' = kind ⟨l,m⟩ = succ κ`: `RegularPair (κ.dir) (κ'.dir)`: old/old inherited (`D.generic.regular`); old/`cutStartS`: `(τs−ε)•es` positive multiple (`RegularPair u (λ•v) ↔ RegularPair u v`, `λ>0`); `cutStartS/arcST`: `es` vs `es+et` independent (`det ≠ 0`); `arcST/cutEndT`: `es+et` vs `et`; `cutEndS/old(s+1)`: inherited | 90 |
| `tail_off` | `tail u ∉ seg u'` when not incident: `tail u` is an old vertex or a cut point. Old vertex vs old strand: inherited (`D.generic.tail_off`, incidence transported by `incidentTail_iff`/`adjacent_old_iff`); old vertex vs cut piece: on `seg s` ⇒ incident to `s` in `D` ⇒ `tail s`/`head s`, excluded by parameters; old vertex vs arc: `tail_not_mem_disc` + `seg_arc_subset_ball`; cut point vs old strand `e ∉ {s,t}`: `r₁_le_dist` vs `dist_cut_lt`; cut point vs cut piece / arc: parameters and `kind_disjoint` | 100 |
| `transverse` | non-adjacent kinds that meet: both old ⇒ `D.generic.transverse` (`adjacent_old_iff`); old vs cut piece ⇒ non-adjacent in `D` (`cut_inter_old`) ⇒ `det (edge e) (λ•es) = λ det ≠ 0`; every other pair is disjoint (`kind_disjoint`) | 50 |
| `no_triple` | a triple with an arc: the common interior point is in `ball p r₁`, so the others are cut pieces/the other arc, all disjoint from the arc except at ends (not interior); no arc: at most one cut piece (cut pieces pairwise disjoint), the other two old ⇒ triple of `D` with `orig` | 50 |
| `isCrossing_orig` | from the classification in `transverse`: a meeting non-adjacent pair is old/old or old/cut; `orig` pair non-adjacent in `D` and meeting; `≠ x.val` since `x = {s,t}` and old strands are `∉ {s,t}` | 40 |
| `origCrossing_ne`, `orig_mem_origCrossing`, `origCrossing_injective`, `orig_injOn_crossing` | from `isCrossing_orig` and `orig` injective on a crossing (the two strands of a `Γ₀`-crossing have distinct originals) | 40 |
| `crossingPoint_origCrossing` | `common_point_unique` (414) for `D`: the `Γ₀` crossing point lies on both original segments (`seg_subset_seg_orig`) | 20 |
| `orig_liftStrand`, `isCrossing_lift`, `origCrossing_liftCrossing`, `liftCrossing_origCrossing` | `liftStrand` picks the cut piece containing the crossing point: `crossingParam y s ≠ τs` and `|param − τs|‖es‖ ≥ r₁ > ε‖es‖` (`r₁_le_dist_crossingPoint`), so the point is on `cutStartS` iff `param < τs`; non-adjacency by `adjacent_iff` (`e ≠ s−1` etc. from `¬Adjacent e s`); round trips by `kind_injective` and uniqueness of the containing piece | 100 |

### Block E — over data, cleanness of `D₀`, arcs, outside match (§6c-6f), ~600 lines
| lemma | sketch | est. |
|---|---|---|
| `orig_overStrand₀`, `toDiagram_underStrand_orig`, `toDiagram_sign` | `over_mem`/`eq_under_of_mem_of_ne`; `dir` of a cut piece is `λ•dir orig`, `λ>0` ⇒ `det` sign preserved (`sign_mul`) | 60 |
| `crossingParam_toDiagram` | uniqueness of the parameter on a nonzero edge (`smul_right_injective`) + `tail_add_smul_dir` | 40 |
| `clean_toDiagram` | frontier point is on a cut piece (arcs are inside the open ball, old strands outside); each cut piece meets the sphere once (`edgePoint_*_mem_disc_iff`, `θ₀_mem`); cut pieces pairwise disjoint; `exits`: every component has a strand whose tail is an old vertex (`kind_pred` of an arc is a cutStart, whose tail is old) | 90 |
| `strandOf_cutEndT_eq`, `strandOf_cutEndS_eq` | `kind_succ` twice | 15 |
| `arcST₀_ne_arcTS₀` | different start kinds ⇒ different strands (`kind_injective`) | 10 |
| `arcCover_toDiagram` | `isArc`: ends on the sphere via `crossingParam`-free evaluation `eval_eq` + `origParam` of `θ₀*` = `θ*`; inner points via `traversalBetween_span_two` (start on `cutStartS`, middle `arcST`, stop on `cutEndT` = `m+2`, no wrap: `(cutStartS).2.val + 2 < k` since `cutEndT` is a strand of the same component — from `strandOf_cutEndT_eq` and `ZMod.val_add`); `mem_iff`: `eval q ∈ disc` ⇒ kind is a cut piece or arc (`mem_seg_of_mem_disc` on the original) ⇒ on `a₀` or `b₀`; `disjoint`: distinct kinds | 150 |
| `arcST₀_start` … (4) | `eval_eq` + `tail_add_smul_dir` + `origParam ∘ liftParam = id` | 40 |
| `eval_origPt`, `origPt_outside` | for `q` outside: kind is not an arc (arcs inside the open ball), `origParam ∈ [0,1)` (clamp inactive), `tail_add_smul_dir` | 50 |
| `origPt_bijective` | injective: same original strand and parameter ⇒ same kind (cut pieces of one strand have disjoint `origParam` ranges) and same parameter (`liftParam` inverse); surjective: an outside point on `e ∉ {s,t}` ↦ `⟨strandOf (old e), θ⟩`; on `s` with `θ ≤ θsIn` (resp. `≥ θsOut`) ↦ `cutStartS` (resp. `cutEndS`) with `liftParam`; `θsIn ≤ τs−ε` (`θsIn_lt_cut`) | 100 |
| `outsideEquiv_eval`, `_dir_pos`, `_dir_pos_before` | `Equiv.ofBijective_symm_apply` + `eval_origPt`; `dir_eq` with `λ ∈ {1, τs−ε, 1−τs−ε, …} > 0`; `strandBefore` at parameter `0` is `⟨l, m−1⟩` — `kind_pred` gives the kind, whose `dir` is a positive multiple of `dir (strandBefore (origPt q))` (for `old (s+1)`: predecessor `cutEndS` vs `s`) | 90 |
| `outsideEquiv_outerOverPt`, `_outerUnderPt` | `outerEquiv` unfolds to `liftCrossing`; `visitPt` of the over visit of `liftCrossing y` is `⟨liftStrand s, liftParam (crossingParam)⟩` (`crossingParam_toDiagram`), whose `origPt` is `visitPt (overVisit y)` (`orig_liftStrand`, `origParam ∘ liftParam = id`), then `Equiv.ofBijective` injectivity | 60 |

### Block F — the concrete models (§7), ~500 lines
| lemma | sketch | est. |
|---|---|---|
| `card_othersM`, `card_othersS`, `two_le_dd`, `dd_add_two_le` | `Finset.card_erase_of_mem`, `card_fin`; `dd`: `¬adjacent a bS` (transport `t.2` along `h` by `ZMod.val`: `(h ▸ b).val = b.val`) ⇒ `bS − a ∉ {−1,0,1}` ⇒ `2 ≤ val ≤ k−2` (`ZMod.val_lt`, `ZMod.natCast_self_eq_zero`) | 60 |
| `mixedModel` (6 fields) | all by `Fin.cases` on the component and `ZMod.val` case analysis of `mergedKindIdx`: `kind_injective` (old kinds determine `l` and `m.val`; the eight special indices are distinct); `kind_surj`/`kind_occurs` (an old `e ∉ {s,t}` is `⟨emb l, m⟩` for `e.1 ∈ othersM`, else `e.1 = i` and `e = ⟨i, a+1+m'⟩` with `m' = (e.2 − a − 1).val < k_i − 1`, similarly for `j`); `kind_pred` (`(m − 1).val` is `m.val − 1` or `N − 1`, `ZMod.val_sub`/`val_add`, then the `if` chains of `mergedKindIdx` and `StrandKind.pred` line up: e.g. index `k_i` (arcST) has predecessor `k_i − 1` (cutStartS) ✓, index `0` (old `⟨i,a+1⟩`) has predecessor `N−1` = cutEndS and `pred (old (s+1)) = cutEndS` ✓); `tail_eq` (`Q m` by the tuple definition and `sMinus_eq_edgePoint` etc.); `dir_eq` (`Q (m+1) − Q m`, one case per kind: e.g. `Q k_i − Q (k_i−1) = s⁻ − P_i a = (τs−ε)es`) | 220 |
| `selfModel` (6 fields) | same with two `Fin.cases` and the tuples `A`, `B`; `kind_pred` at index `0` of `A` (old `⟨i,a+1⟩`, predecessor index `d+1` = cutEndS) and at index `0` of `B` (old `⟨i,bS+1⟩`, predecessor `k−d+1` = cutEndT); surjectivity splits old strands `⟨i, m⟩` by `cycBetween`-free arithmetic: `(m − a).val ∈ [1, d−1]` ⇒ in `A`, `∈ [d+1, k−1]` ⇒ in `B` | 220 |

### Block G — the record bridge (§8), ~640 lines
| lemma | sketch | est. |
|---|---|---|
| `origVisit_injective`, `smoothKeep_origVisit`, `exists_origVisit` | `origCrossing_injective` + `orig_injOn_crossing`; `origCrossing_ne` ⇒ `v.1 ≠ x` ⇒ `≠ xv, ≠ τ xv` (`smoothKeep_iff`, LinkRecord 855); lift via `liftCrossing` and `liftStrand` | 60 |
| `twin_origVisit`, `overBit_origVisit` | `twin` = `other` transported by `orig_injOn_crossing`; `overBit` via `orig_overStrand₀` | 40 |
| `mixedCls_bijective` | classes: `Sum.inl ⟦w⟧` for `w` on `i₀ ∉ {i,j}` equals the `succ`-class (`Record.smooth_comp_eq_iff` 932; on such components `reconnect = succ`, `reconnect_apply_of_ne`); `⟦xv⟧ = ⟦τ xv⟧` and every `w` on `i` or `j` is in it (`reconnect_sameCycle_of_mixed` 1086); free comps `Sum.inr` correspond to crossing-free `i₀ ∉ {i,j}` (`i`, `j` carry `xv`, `τ xv`). Injective by `sameCycle_iff_comp_eq` + `h`; surjective by the classification `reconnect_sameCycle_or` (Extras 280) | 120 |
| `mixedCls_visit` | `v` on component `0` ⇒ `origVisit v` on `i` or `j` ⇒ class `⟦xv⟧` (`reconnect_sameCycle_of_mixed`); on `l.succ` ⇒ `oldCls (emb l)` = `⟦origVisit v⟧` (same `succ`-cycle) | 50 |
| `mixed_visitCoord` | definitional (`visitCoord = traversalKey (visitPt) = val + crossingParam`) | 10 |
| `mixed_succ` | see §3 below (the hardest lemma) | 220 |
| `selfCls_bijective`, `selfCls_visit` | `A`'s occurrences are on the `reconnect`-cycle of `τ xv` and `B`'s on that of `xv`: an occurrence `w` on `i` with `cycBetween (coord xv) (coord w) (coord (τ xv))` reaches `τ xv` by iterating `succ` without meeting `xv` (`nextVisit_no_between`, induction on the `ent` index, LinkDiagramRecord 912-970) ⇒ `reconnect`-same-cycle as `τ xv` (`reconnect_apply_of_ne`); the two classes differ (`smooth_comps_ne_of_self`, Extras 285); old components as in the mixed case | 160 |
| `self_succ` | as `mixed_succ` | 180 |

## 3. The successor law (`mixed_succ`, `self_succ`) — method

Template: `Diagram.restrictVisit_nextVisit` (LinkDiagramRecord 1344-1452) proves the analogous law
for restriction with `cycNext_unique_on` (LinkDiagramRecord 102).  Here the coordinates change, so
the argument has two halves.

(L1) **Coordinate transfer.**  For retained `w` on the merged cycle define the *reconnect
coordinate* `ρ(w) := rexB_rot k_i (coord xv) (coord w)` if `compOf w = i`, and
`k_i + rexB_rot k_j (coord (τ xv)) (coord w)` if `compOf w = j` (`rexB_rot`, LinkRecordExtension 53:
rotation of the cut circle so that `xv`, resp. `τ xv`, sits at `0`).  Then the `D₀`-coordinate of
`origVisit⁻¹ w` on the merged component is `rexB_rot N c₀ (F (ρ w))` for an explicit strictly
increasing piecewise-affine `F` (the blocks in `ρ`-order: `i`-occurrences after `x` (on `cutEndS`),
old `i`-edges, `i`-occurrences before `x` (`cutStartS`), `j` after `τx` (`cutEndT`), old `j`-edges,
`j` before `τx` (`cutStartT`); `F` is affine on each block by `crossingParam_toDiagram`/`liftParam`
and the edge indices of `mergedKindIdx`; `c₀` rotates the first block to the end).  Consequently
`D₀.VisitBetween v w u ↔ cycBetween (ρ v') (ρ w') (ρ u')` on the merged component
(`rexB_cycBetween_rot` 82, `rexB_cycBetween_of_strictMonoOn` 102).  In the self case `ρ_A(w) :=
rexB_rot k (coord xv) (coord w)` on `A`, `ρ_B(w) := rexB_rot k (coord (τ xv)) (coord w)` on `B`,
`F` affine on three blocks each.

(L2) **`smoothSucc` is the `ρ`-cyclic successor among retained occurrences.**  Case `succ w ∉ {xv, τ xv}`:
`smoothSucc w = succ w` (`smooth_succ_val_of_not_mem`, LinkRecord 941) and nothing is `cycBetween`
in `D`-coordinates (`nextVisit_no_between` 335); rotation preserves this, and no occurrence of the
*other* component can be strictly between because `ρ(succ w) > ρ(w)` (otherwise `xv` would lie
between `w` and `succ w`).  Case `succ w = xv`: `smoothSucc w = succ (τ xv)` (949; or `succ xv` if
`τ xv` is alone, 964): `ρ w` is the largest `i`-value and `ρ (succ (τ xv))` the smallest `j`-value.
Case `succ w = τ xv`: symmetric (983, 998).  Then `cycNext_unique_on` in `D₀` with
`p := same component`, `k := D₀.visitCoord`, candidates `D₀.nextVisit v` (by definition) and
`origVisit⁻¹ (smoothSucc (origVisit v))` (on the same component by `*Cls_visit` +
`smooth_comp_eq_iff` 932; `≠ v` unless `v` is alone, by `smooth_succ` fixed-point analysis).
Untouched components: `smooth_succ_val_of_comp_ne` (1104) and the coordinate is literally the same.

## 4. Existing lemmas reused (file:line)

LinkDiagram.lean: `Shadow.Generic` 394, `Generic.common_point_unique` 414,
`Generic.crossingPoint_param` 434, `Generic.crossingPoint_mem_interior` 456,
`Generic.crossingPoint_injective` 463, `adjacent_mk_iff` 150, `incidentTail_mk_iff` 162,
`other`/`eq_pair_other`/`mem_iff_eq_or_other`/`eq_other_of_mem_of_ne` 315-343,
`Diagram.det_over_under_ne_zero` 540, `not_adjacent_over_under` 531, `crossingParam*` 1413-1430,
`visitPt`, `eval_visitPt`, `visitPt_injective` 1435-1470, `overVisit`/`underVisit`/`visit_eq_over_or_under` 597-625.
LinkMoves.lean: `isDisc_closedBall` 100, `strandOf`/`strandBefore` 121-135, `Arc.*` 155-200,
`IsArc` 213, `ArcCover` 226, `OuterCrossing`/`outerOverPt` 265-285, `OutsideMatch` 311,
`Clean` 336, `LocalFrame` 343, `OrientedSmoothingData` 713, `IsOrientedSmoothing` 743,
`SmoothingRecordClause` 1128, `Shadow.edge_ne_zero` 1257, `Arc.inner_mk_iff` 2727,
`OrientedSmoothingData.card_crossing` 1041, `IsOrientedSmoothing.card_crossing` 1051.
LinkRecord.lean: `Record` 309, `RecordIso` 539, `reconnect*` 822-845, `SmoothKeep`/`smoothKeep_iff` 849-866,
`SmoothComps` 880, `smooth` 895, `smooth_comp_eq_iff` 932, `smooth_succ_val_of_not_mem` 941,
`smooth_succ_val_of_succ_eq(')` 949/964, `smooth_succ_val_of_succ_eq_pair(')` 983/998,
`smoothPairIso` 1040, `IsSelfCrossing` 1069, `reconnect_sameCycle_pair_of_mixed` 1080,
`reconnect_sameCycle_of_mixed` 1086, `reconnect_sameCycle_refines_of_self` 1098,
`smooth_succ_val_of_comp_ne` 1104, `firstReturn*` 100-187.
LinkRecordExtras.lean: `not_reconnect_sameCycle_pair_of_self` 274, `reconnect_sameCycle_or` 280,
`smooth_comps_ne_of_self` 285, `card_comps_smooth_of_self/mixed` 290/298, `componentCount_smooth` 333.
LinkDiagramRecord.lean: `cycBetween` 78, `cycNext_unique_on` 102, `compOf` 164, `visitCoord` 181,
`visitCoord_injOn` 189, `nextVisit` 258, `nextVisit_no_between` 335, `nextVisit_ne_self` 355,
`nextVisit_eq_self` 371, `twin` 413, `overBit` 470, `record` 500, `record_componentCount` 537,
`record_isSelfCrossing_iff` 583, `VisitBetween` 882, `ent`/`visitBetween_ent_iff` 912-970,
`restrictVisit_nextVisit` 1344 (template), `restrictRecordIso` 1454 (template).
LinkRecordExtension.lean: `rexB_rot` 53, `rexB_cycBetween_rot` 82, `rexB_cycBetween_of_strictMonoOn` 102.
LinkDiagramExtras.lean: `Shadow.otherVisit` 353, `StrandMap.mapVisit` 525 (pattern only).
Polygon.lean: `edge` 49, `edgePoint` 51, `edgeSegment` 54, `edgeInterior` 57, `incident` 60, `adjacent` 63.
Segment.lean: `independent_of_det_ne_zero` 13, `no_multiple_of_det_ne_zero` 40,
`intersection_parameters_unique` 55.  RegularPairs.lean: `RegularPair` 8, `negativeScalar_iff_dot_det` 11.
RegularLocus.lean: `Regular` 12, `regular_iff_edges` 17.  EuclideanPlane.lean: `scalar_of_det_zero` 75.
Traversal.lean: `TraversalPoint` 12, `traversalKey` 16, `traversalBetween` 73.
Mathlib: `Metric.infDist`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_le_dist_of_mem`,
`Finset.inf'`, `Finset.lt_inf'_iff`, `Finset.inf'_le`, `interior_closedBall`, `frontier_closedBall`,
`Metric.mem_ball/closedBall/sphere`, `norm_smul`, `Prod.norm_def`, `ZMod.val_natCast`,
`ZMod.natCast_zmod_val`, `ZMod.val_lt`, `ZMod.val_add`, `Fin.cases` (+ `cases_zero`, `cases_succ`),
`Finset.orderEmbOfFin`, `Finset.card_erase_of_mem`, `Equiv.ofBijective`, `Equiv.subtypeEquivRight`,
`Equiv.subtypeUnivEquiv`.

## 5. Dependency order for provers (suggested lanes)

1. Block A (clearance, ε) and Block B (kinds) are independent of each other → two provers.
2. Block C (disc, `D`'s arcs, `clean_D`) needs A only.
3. Block D (genericity, crossings) needs A, B, C(`mem_seg_of_mem_disc`).
4. Block E needs C, D.  `arcCover_toDiagram` and `origPt_bijective` are the two large items.
5. Block F (models) needs only §0-§4 definitions — can start immediately (pure index arithmetic);
   it is the bulk of the `ZMod.val` bookkeeping and should be a dedicated lane.
6. Block G needs D, E (`origCrossing`, `crossingParam_toDiagram`) and F; `mixed_succ`/`self_succ`
   last.
Line totals: A 330, B 300, C 360, D 520, E 600, F 500, G 640 → ≈ 3 250 lines including the 1 400
skeleton lines already written (statements/definitions), i.e. ≈ 2 950 lines of new proof text.

## 6. Three riskiest steps and fallbacks

1. **`mixed_succ` / `self_succ` (Block G, the coordinate transfer L1).**  Risk: the explicit
   piecewise-affine `F` and its rotation are long and fiddly (six blocks, modular index arithmetic).
   Fallbacks: (a) avoid `F` entirely and prove `D₀.VisitBetween ↔ cycBetween ∘ ρ` block-pairwise
   (36 ordered block pairs, but each is a one-line `linarith` after the block ranges are
   established); (b) replace coordinates by a *walk* characterisation of `nextVisit` (`nextVisit v`
   = first occurrence on `strand v` with larger parameter, else the first on `succ strand`, …),
   proved once as a general lemma about any diagram, then matched kind by kind with the first-return
   description of `smoothSucc`; (c) weaken the deliverable to `exists_smoothing` + the count lemmas
   (`smoothDiagram_componentCount`, `card_crossing`) and ship `smoothing_record` later — the
   consumers' inductions need the RecordIso, so (c) is a schedule fallback only.
2. **`origPt_bijective` and `arcCover_toDiagram` (Block E).**  Risk: `Outside U` bijection needs a
   clean classification of traversal points by kind and parameter, and `ArcCover.mem_iff` for `D₀`
   needs the two-edge `traversalBetween_span_two` with `ZMod` index `m + 2` on a component whose size
   is only known abstractly (`(cutStartS).2.val + 2 < k` must come from `kind_succ` twice).  Fallback:
   add to `SpliceModel` two more laws that make the size explicit (`3 ≤ (Γ₀.comp l).k` is already
   in `PolyComp`; add `kind_val_succ : (⟨l, m+1⟩).2.val = m.val + 1 ∨ …` or directly
   `(strandOf cutStartS).2.val + 2 < k`), provable trivially in both concrete models.
3. **`mixedModel` / `selfModel` `kind_pred` and `tail_eq`/`dir_eq` (Block F).**  Risk: `ZMod.val`
   arithmetic across the wrap (`(m − 1).val` when `m.val = 0`; `(a + 1 + m).val`) and `Fin.cases`
   on `u.1` inside `Sigma` types produce heavy `dsimp`/`omega` goals; the self case additionally
   transports `b` to `ZMod k_i` by value.  Fallbacks: (a) state and prove a small toolbox first
   (`ZMod.val_sub_one_of_pos`, `val_add_one_of_lt`, `natCast_val_eq`), then every field is `omega`
   after `split_ifs`; (b) if `Fin.cases` with a dependent motive misbehaves, define the shadows with
   `comp := fun l => if l.val = 0 then … else …` and the kind map on `(l.val, m.val)` only, using
   `ZMod.natCast_zmod_val` to rebuild labels — all statements in the skeleton are on `.val` already.

## 7. Notes for the implementer

* Never change the fixed definitions; the skeleton only adds `Shadow.Crossing.fst/snd` (root
  namespace helpers) and the `Smoothing` namespace.
* `include`/`omit` discipline: sections `DiscD` (`hε`) and `Model` (`M hε`) include their variables;
  definitions that do not need them are marked `omit … in`.
* The over/under choice fixes `s = overStrand x`; `Record.smoothPairIso` handles the other occurrence.
* Signs: `toDiagram_sign` gives `sign₀ y = sign (origCrossing y)`, hence `writhe` transport is free
  if a consumer needs it.
