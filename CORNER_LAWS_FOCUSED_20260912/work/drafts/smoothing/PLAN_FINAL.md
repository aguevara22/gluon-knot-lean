# PLAN_FINAL — `exists_smoothing` / `smoothing_record` (oriented smoothing, sm-3:1084-1103)

Plan of record, written 2026-09-13 by the judge of the two architect plans
`PLAN_A.md` / `Skeleton_A.lean` (tag A) and `PLAN_B.md` / `Skeleton_B.lean` (tag B).
Skeleton of record: **`work/drafts/smoothing/Skeleton_FINAL.lean`** (1761 lines, `lake env lean`
exit 0, 146 `sorry`-declarations, all four goal theorems depend on `[propext, sorryAx,
Classical.choice, Quot.sound]` only).  When the lane lands the file becomes
`work/lean/SM/LinkSmoothing.lean` (imports `LinkDiagramRecord`, `LinkMoves`, `LinkRecordExtras`,
`LinkDiagramExtras`, `LinkRecordExtension`); the §0' toolbox may be moved into
`LinkDiagramExtras`.

## 0. Verdict

**Winner: A** (splice-model construction, no-wrap layouts, one abstract geometric proof),
**with four grafts from B** and **two fixes to A** (details in §2).

| criterion | A | B | why |
|---|---|---|---|
| (a) correctness against the fixed definitions | **7** | 6 | Both build a genuine `OrientedSmoothingData` in both cases (self: one circle → `A`, `B`; mixed: two circles → merged) with the right reconnection (`s⁻ → t⁺`, `t⁻ → s⁺`), and both `ZMod` layouts check out edge by edge (§1.3-1.4 below record the check).  A has one definitional bug: `origPt` clamps the original parameter into `[0, 1/2]` (`max 0 (min … (1/2))`), so `eval_origPt` is false for old-strand points with parameter `> 1/2`; fixed here with B's `[0,1)`-clamp.  A's `traversalBetween_span_two` needs `m.val + 2 < n`, which the six splice-model laws do not imply; fixed by a seventh law `cut_val` (trivial in both concrete models).  B has one false chain lemma: `smB_reconnect_no_between` (L5.4a) fails in the mixed case at the last retained occurrence before `vo` (its `s₁`-image is `vo`, placed by `smB_off` at `0`, while `vu` at `k_o` lies cyclically between); fixed here by evaluating the coordinate after `swap vo vu` (`rkey`).  B's arcs `a₀`/`b₀` wrap around label `0` (self case both, mixed case `b₀`) — correct but every arc lemma needs a wrap case. |
| (b) provability in Lean with the existing library | **7** | 6 | A proves all geometry once against six index laws (`kind`, injective/surjective, `kind_pred`, `tail_eq`, `dir_eq`); the two concrete models are pure `ZMod.val` arithmetic; components are `Fin.cases`-indexed so `comp 0 = merged` is `rfl`.  B indexes components by `Fintype.equivFin` on the smoothed record's `comps` and describes them through `Quotient.out` and classical `if`s on `SameCycle`, so every shape lemma (kinds, injectivity, positions) first needs the record-cycle classification — the geometric and record layers are entangled, and `smB_kind_injective` needs `smooth_comps_ne_of_self`.  B's record bridge, however, is better structured (general first-return lemma + one global coordinate), while A's `mixed_succ`/`self_succ` are two 200-line monoliths with no intermediate statements. |
| (c) minimality of the geometric burden | **8** | 6 | A: 7-field `SmallEps`, explicit `eps`, disc radius derived from the clearance `r₁ = min infDist` (one `Finset.inf'`), no wrap cases, geometry proved once.  B: 15-field `Small` with a 150-line `exists_small`, wrap cases in both arc covers and in `smB_dir_pos_before`, geometry proved per kind but positions proved per descriptor type (4 types). |
| total | **22** | 18 | |

Both architects agree, correctly, that the *relational* form `IsOrientedSmoothing D x D₀ →
RecordIso D₀.record (D.record.smooth v)` is not provable from the fixed `OutsideMatch` (no cyclic
order clause on `φ`); the deliverable is the constructive form (§0.1).  This is recorded as an open
item for work/AUTHOR_NOTES.md when the lane lands.

### 0.1 Goal theorems (unchanged from A; namespace `SM.Link`)

```lean
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀
theorem exists_smoothing_record (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x)))
theorem exists_smoothing_record_visit (D : Diagram) (x : D.Γ.Crossing) (v : D.Γ.Visit) (hv : v.1 = x) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧ Nonempty (RecordIso D₀.record (D.record.smooth v))
theorem smoothingRecordClause_smoothDiagram (D : Diagram) (x : D.Γ.Crossing) :
    SmoothingRecordClause Diagram.record (fun _ v => v) D x (smoothDiagram D x (eps D x) (eps_small D x))
theorem exists_smoothing_counts (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x))) ∧
      D₀.componentCount = (if D.record.IsSelfCrossing (D.overVisit x) then D.componentCount + 1
        else D.componentCount - 1) ∧
      1 ≤ D₀.componentCount ∧ Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing
```
All five are proved in the skeleton from the chain; `exists_smoothing_record_visit` uses
`Record.smoothPairIso` (LinkRecord 1040) for the under occurrence, `exists_smoothing_counts` uses
`RecordIso.componentCount_eq`, `Record.componentCount_smooth` (LinkRecordExtras 333),
`IsOrientedSmoothing.card_crossing` (LinkMoves 1051).

## 1. The construction (tag A, as fixed)

Notation (skeleton §0): `s = D.overStrand x = ⟨i, a⟩`, `t = D.underStrand x = ⟨j, b⟩`,
`p = crossingPoint x`, `τs = crossingParam x (over_mem)`, `τt`, `es = dir s`, `et = dir t`
(`det es et ≠ 0`, `τs, τt ∈ (0,1)`), `xv = D.overVisit x`, `τ xv = D.underVisit x`
(`D.record.pair xv = D.underVisit x` is `rfl`: `record_pair_xv`).

### 1.1 Clearance, `ε`, the disc (skeleton §1-3, §5)
* `others := univ.filter (· ∉ {s,t})`, nonempty (`⟨i, a−1⟩`).  **Key lemma**
  `crossingPoint_not_mem_seg_other : e ∉ {s,t} → p ∉ seg e` (now a corollary of the §0' lemma
  `Generic.crossingPoint_not_mem_seg`).
* `r₁ := others.inf' _ (fun e => infDist p (seg e)) > 0`; every other strand, every vertex and every
  other double point is at distance `≥ r₁` from `p`; `r₁ ≤ τs‖es‖, (1−τs)‖es‖, τt‖et‖, (1−τt)‖et‖`.
* `SmallEps ε` (7 fields: `0 < ε < τs, 1−τs, τt, 1−τt`; `ε‖es‖, ε‖et‖ < r₁`), `eps := (min of six)/2`.
  Derived (graft of B's `ε_vis`): `crossingParam_far_s/t`: every other occurrence on `s` (`t`) has
  `|param − τ| > ε`.
* Cut points `s⁻ = p − ε es`, `s⁺ = p + ε es`, `t⁻`, `t⁺`; arcs `s⁻ → t⁺` (`arcST`) and `t⁻ → s⁺`
  (`arcTS`), both with direction `ε(es+et)`, disjoint (`coords_unique`).
* Disc `U = closedBall p r`, `r := (ε·max(‖es‖,‖et‖) + r₁)/2` (sup metric: a square; `isDisc_closedBall`);
  frontier parameters `θsIn/Out = τs ∓ r/‖es‖`, `θtIn/Out`, with `0 < θsIn < τs−ε < τs+ε < θsOut < 1`.

### 1.2 Kinds and the splice model (skeleton §4)
Seven `StrandKind`s: `old e`, `cutStartS = [P_i a, s⁻]`, `cutEndS = [s⁺, P_i(a+1)]`, `cutStartT`,
`cutEndT`, `arcST`, `arcTS`, with `tail`, `dir`, `orig`, `origParam`/`liftParam` (affine parameter
rescaling) and the cyclic laws `pred`/`succ` encoding the reconnection
(`succ cutStartS = arcST`, `succ arcST = cutEndT`, `succ cutStartT = arcTS`, `succ arcTS = cutEndS`,
`succ (old (s−1)) = cutStartS`, `succ cutEndS = old (s+1)`, …).
```lean
structure SpliceModel (ε : ℝ) (Γ₀ : Shadow) where
  kind : Γ₀.Strand → StrandKind D x
  kind_injective : Function.Injective kind
  kind_surj : ∀ κ : StrandKind D x, κ.Occurs → ∃ u, kind u = κ
  kind_occurs : ∀ u, (kind u).Occurs
  kind_pred : ∀ u : Γ₀.Strand, kind ⟨u.1, u.2 - 1⟩ = (kind u).pred
  tail_eq : ∀ u, Γ₀.tail u = (kind u).tail ε
  dir_eq : ∀ u, Γ₀.dir u = (kind u).dir ε
  cut_val : ∀ u : Γ₀.Strand, (kind u = StrandKind.cutStartS ∨ kind u = StrandKind.cutStartT) →
    u.2.val + 2 < (Γ₀.comp u.1).k          -- NEW (fix): the no-wrap law
```
From these laws everything geometric is proved once (§6 of the skeleton): genericity (`generic`),
the crossing correspondence `crossingEquiv : Γ₀.Crossing ≃ {y // y ≠ x}` (`origCrossing`/`liftCrossing`),
the smoothed diagram `toDiagram` (over strand pulled back through `orig`), `clean_toDiagram`, the arcs
`arcST₀ = (cutStartS at θ₀sIn) → (+2 at θ₀tOut)`, `arcTS₀`, the outside match
(`origPt` with the `[0,1)`-clamp `clampIco`, `outsideEquiv := (ofBijective origPt).symm`,
`outerEquiv`), hence `orientedSmoothingData : OrientedSmoothingData (disc D x ε) D x (toDiagram D x M hε)`.

### 1.3 The mixed case `i ≠ j` (skeleton §7a) — checked edge by edge
Merged component, `N = k_i + k_j + 4`, `Q : ZMod N → Plane`:
`Q m = P_i(a+1+m)` (`m < k_i`, so `Q(k_i−1) = P_i a`), `Q k_i = s⁻`, `Q(k_i+1) = t⁺`,
`Q(k_i+2+m') = P_j(b+1+m')` (`m' < k_j`, so `Q(k_i+1+k_j) = P_j b`), `Q(k_i+2+k_j) = t⁻`,
`Q(k_i+3+k_j) = s⁺`, `Q N = Q 0 = P_i(a+1)`.
Edges (`mergedKindIdx`): `0…k_i−2` old `⟨i,a+1+m⟩` ✓; `k_i−1` `P_i a → s⁻` = cutStartS ✓; `k_i` arcST ✓;
`k_i+1` `t⁺ → P_j(b+1)` = cutEndT ✓; `k_i+2…k_i+k_j` old `⟨j,b+1+m'⟩` ✓; `k_i+1+k_j` `P_j b → t⁻` = cutStartT ✓;
`k_i+2+k_j` arcTS ✓; `k_i+3+k_j` `s⁺ → P_i(a+1)` = cutEndS ✓.  Both arc windows
`[k_i−1, k_i+1]`, `[k_i+1+k_j, k_i+3+k_j]` avoid label `0`: **no wrap** (`cut_val` holds).
`mixedShadow := ⟨othersM.card + 1, _, Fin.cases mergedComp (comp ∘ orderEmbOfFin)⟩`,
`othersM = (univ.erase i).erase j`; `mixedKind ⟨0, m⟩ = mergedKindIdx m.val`,
`mixedKind ⟨l.succ, m⟩ = old ⟨emb l, m.val⟩`.

### 1.4 The self case `i = j` (skeleton §7b) — checked edge by edge
`bS := (t.2.val : ZMod k_i)` (transport of `b` by value), `d := (bS − a).val ∈ [2, k−2]`.
`A` (`d+2` vertices): `Q_A m = P(a+1+m)` (`m < d`; `Q_A(d−1) = P(a+d) = P b`), `Q_A d = t⁻`, `Q_A(d+1) = s⁺`;
edges `0…d−2` old `⟨i,a+1+m⟩`, `d−1` cutStartT, `d` arcTS, `d+1` cutEndS (wraps to `P(a+1)`) ✓.
`B` (`k−d+2`): `Q_B m = P(bS+1+m)` (`m < k−d`; `Q_B(k−d−1) = P(b+k−d) = P a`), `Q_B(k−d) = s⁻`,
`Q_B(k−d+1) = t⁺`; edges `0…k−d−2` old `⟨i,b+1+m⟩`, `k−d−1` cutStartS, `k−d` arcST, `k−d+1` cutEndT ✓.
No wrap in either window.  `A` carries the occurrences met after `x` and before `τx` — the word `A`
of `(x A y B)`, the `s₁`-cycle of `τ xv` (`selfCls 0 = ⟦τ xv⟧`); `B` carries the rest (`⟦xv⟧`).
`selfShadow := ⟨othersS.card + 2, _, Fin.cases compA (Fin.cases compB (comp ∘ orderEmbOfFin))⟩`.

### 1.5 The smoothed diagram
`smoothDiagram D x ε hε := if h : i = j then toDiagram (selfModel h) hε else toDiagram (mixedModel h) hε`;
`isOrientedSmoothing_smoothDiagram`, `smoothDiagram_componentCount` (`c+1`/`c−1` by counting
`Fin.cases` components — already proved in the skeleton).

## 2. What was grafted from B, what was fixed in A (the record bridge, skeleton §0' and §8)

1. **`clampIco : ℝ → Set.Ico 0 1`** (B's `smB_ico`) replaces A's `max 0 (min · (1/2))` in `origPt`;
   `origParam_mem` shows the clamp is inactive, `origPt_param` is the resulting `rfl`-free unfolding.
2. **`cut_val`** added to `SpliceModel` (see 1.2); `strandOf_cutStartS_val`, `strandOf_cutStartT_val`
   feed `traversalBetween_span_two`.
3. **B's §0 toolbox** (`Shadow.edgePt`, `dist_edgePt`, `Generic.seg_inter_succ`,
   `Generic.crossingPoint_not_mem_seg`, `Generic.crossingPoint_ne_tail`, `Generic.seg_inter_seg_eq`,
   `Generic.edgePt_injective`, `two_le_val_sub_of_not_adjacent`, `coords_unique`, four `regularPair_*`
   lemmas, `Diagram.visitCoord_eq` (`rfl`)) is §0' of the final skeleton.
4. **B's record-bridge architecture, corrected.**  Instead of A's two per-case monoliths
   `mixed_succ`/`self_succ`, the successor law is proved **once at the model level**:
   * `key : D.Γ.Visit → ℝ` (B's `smB_off`): `cyclicOffset k_i (coord xv) (coord v)` on the circle of `s`;
     `k_i + cyclicOffset k_j (coord τxv) (coord v)` on the circle of `t`; `coord v` elsewhere.
   * **Fix of B's L5.4a:** `rkey v := key (swap xv τxv v)`.  `s₁ = succ ∘ swap(xv, τxv)` sends the last
     retained occurrence before `xv` to `xv`; on the merged/split cycle `xv`'s cyclic position is that
     of `τ xv` (`k_i` in the mixed case), not `0`, so B's statement with `smB_off` is false there; with
     `rkey` it holds: `reconnect_no_between : SameCycle u v → ¬ cycBetween (rkey v) (rkey u) (rkey (s₁ v))`,
     and `rkey = key` on retained occurrences (`rkey_of_smoothKeep`).
   * `firstReturn_no_between` (B's L5.4b, general): the first return of a cyclic-successor permutation
     to `p` is the cyclic successor within `p`.  Combined: `smoothSucc_no_between` (proved in the skeleton
     from the two).
   * `succ_of_coord`: from an injective classification `cls` compatible with `origVisit` and a
     **per-component rotated** strictly monotone coordinate
     `rexB_rot k (c₀ l) (D₀.visitCoord ·) < … ↔ key (origVisit ·) < key (origVisit ·)`,
     the successor law `origVisit (D₀.nextVisit v) = (smooth.succ ⟨origVisit v,_⟩).1` follows by
     `cycNext_unique_on` (template `restrictVisit_nextVisit`).  The rotation `c₀` is needed because A's
     no-wrap layouts start at `P_i(a+1)` while the smoothed order starts at the cut-end piece
     `[s⁺, P_i(a+1)]`, which sits at the **last** label (`mixedBase 0 = N−1`, `selfBase 0 = d+1`,
     `selfBase 1 = k−d+1`, `0` on untouched components).  `rexB_cycBetween_rot` (LinkRecordExtension 82)
     makes the rotation free (`visitBetween_iff_of_rot_lt_iff`).
   * `recordIsoOfCoord` assembles the `RecordIso`; per case only `*_cls_bijective`, `*_cls_visit`,
     `*Base_mem` and `*_key_lt_iff` remain.
   * Two D-side classification lemmas support the self case: `self_sameCycle_pair_iff` (the `s₁`-cycle
     of `τ xv` is `{τ xv} ∪ {w : cycBetween (coord xv) (coord w) (coord τxv)}`) and
     `sameCycle_of_comp_ne` (untouched circles keep their cycles).

## 3. Lemma chain by prover unit (exact statements)

Units are listed in dependency order; a unit may assume every `sorry` statement of the units it
depends on **as stated in `Skeleton_FINAL.lean`**.  Statements below are copied verbatim from the
skeleton (line numbers refer to it); `est.` = estimated proof lines.  Every unit must keep the file
compiling (`cd work/lean && lake env lean ../drafts/smoothing/Skeleton_FINAL.lean`), never change a
statement or a definition, and record any statement it believes false in this file's §5.

### U1-clearance-kinds — Generic-shadow toolbox (§0'), clearance radius `r₁`, `ε`, cut points, kind-level laws (§1-4)  (≈ 936 lines)

Depends on: nothing beyond the definitions of the skeleton.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `dist_edgePt` (82) | <code>theorem dist_edgePt (s : Γ.Strand) (t t' : ℝ) :<br>    dist (Γ.edgePt s t) (Γ.edgePt s t') = \|t - t'\| * ‖Γ.dir s‖</code> | `edgePt_eq`, `dist_eq_norm`, `← sub_smul`, `norm_smul`, `Real.norm_eq_abs`. | 10 |
| 2 | `isClosed_seg` (87) | <code>theorem isClosed_seg (s : Γ.Strand) : IsClosed (Γ.seg s)</code> | `seg = (fun θ => P + θ•e) '' Icc 0 1`; `(isCompact_Icc.image (by fun_prop)).isClosed`. | 15 |
| 3 | `isCompact_seg` (90) | <code>theorem isCompact_seg (s : Γ.Strand) : IsCompact (Γ.seg s)</code> | same image, `IsCompact.image`. | 10 |
| 4 | `Generic.seg_inter_succ` (95) | <code>theorem Generic.seg_inter_succ {Γ : Shadow} (hΓ : Γ.Generic) (u : Γ.Strand) :<br>    Γ.seg u ∩ Γ.seg ⟨u.1, u.2 + 1⟩ = {Γ.head u}</code> | `q = tail u + α e_u = head u + β e_{u+1}`; if `det e_u e_{u+1} ≠ 0`: `intersection_parameters_unique` against `α=1, β=0`; if `det = 0`: `scalar_of_det_zero` gives `e_{u+1} = λ e_u`, `λ > 0` by `Regular` (`negativeScalar_iff_dot_det`), then `(α−1) = βλ` with `α ≤ 1`, `β ≥ 0` forces `α = 1, β = 0`. | 50 |
| 5 | `Generic.crossingPoint_not_mem_seg` (102) | <code>theorem Generic.crossingPoint_not_mem_seg {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)<br>    {t : Γ.Strand} (ht : t ∉ x.val) : Γ.crossingPoint x ∉ Γ.seg t</code> | `P₀ = edgePt t θ`. `θ ∈ (0,1)`: triple point `s, t, u` of `x` (`crossingPoint_mem_interior`) vs `no_triple`. `θ = 0`: `tail t ∈ seg s` with `¬IncidentTail` (else `t` adjacent to `s`, so `tail t ∈ {P a, P(a+1)}` puts `τ ∈ {0,1}`, contra `crossingPoint_param`) vs `tail_off`. `θ = 1`: same with `tail ⟨t.1, t.2+1⟩`. | 60 |
| 6 | `Generic.crossingPoint_ne_tail` (107) | <code>theorem Generic.crossingPoint_ne_tail {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing)<br>    (s : Γ.Strand) : Γ.crossingPoint x ≠ Γ.tail s</code> | `s ∈ x.val`: `crossingPoint_param` gives `τ ∈ (0,1)` while `tail = edgePt s 0`, `edgePt_injective`; else `crossingPoint_not_mem_seg` with `tail_mem_seg`. | 15 |
| 7 | `Generic.seg_inter_seg_eq` (112) | <code>theorem Generic.seg_inter_seg_eq {Γ : Shadow} (hΓ : Γ.Generic) (x : Γ.Crossing) {s t : Γ.Strand}<br>    (hs : s ∈ x.val) (ht : t ∈ x.val) (hst : s ≠ t) :<br>    Γ.seg s ∩ Γ.seg t = {Γ.crossingPoint x}</code> | `⊆`: `common_point_unique`; `⊇`: `crossingPoint_mem`. | 12 |
| 8 | `Generic.edgePt_injective` (118) | <code>theorem Generic.edgePt_injective {Γ : Shadow} (hΓ : Γ.Generic) (s : Γ.Strand) :<br>    Function.Injective (Γ.edgePt s)</code> | `edgePoint_injective` + `edge_ne_zero`. | 8 |
| 9 | `two_le_val_sub_of_not_adjacent` (126) | <code>theorem two_le_val_sub_of_not_adjacent {k : ℕ} [NeZero k] {a b : ZMod k} (h : ¬ adjacent a b) :<br>    2 ≤ (b - a).val ∧ (b - a).val + 2 ≤ k</code> | `(b−a).val ∈ {0, 1, k−1}` iff `b − a ∈ {0, 1, −1}` (`ZMod.val_eq_zero`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `ZMod.natCast_self_eq_zero`); `omega`. | 30 |
| 10 | `coords_unique` (132) | <code>theorem coords_unique {u v : Plane} (hd : det u v ≠ 0) {α β α' β' : ℝ}<br>    (h : α • u + β • v = α' • u + β' • v) : α = α' ∧ β = β'</code> | `intersection_parameters_unique` with `a = b = 0` (or expand `det` componentwise and `nlinarith`). | 12 |
| 11 | `regularPair_smul_pos` (137) | <code>theorem regularPair_smul_pos {u v : Plane} {l m : ℝ} (hl : 0 < l) (hm : 0 < m)<br>    (h : RegularPair u v) : RegularPair (l • u) (m • v)</code> | unfold `RegularPair`; `smul_ne_zero`; a negative multiple `m•v = r•(l•u)` gives `v = (r l / m)•u` with `r l/m < 0`. | 12 |
| 12 | `regularPair_of_det_ne_zero` (142) | <code>theorem regularPair_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) : RegularPair u v</code> | `v = r•u` gives `det u v = 0` (`det_smul_self`); nonzero vectors from `det ≠ 0`. | 12 |
| 13 | `regularPair_add_right_of_det_ne_zero` (146) | <code>theorem regularPair_add_right_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :<br>    RegularPair (l • u) (u + v)</code> | `u + v = r•(l•u)` gives `v = (rl−1)•u`, so `det u v = 0`. | 12 |
| 14 | `regularPair_add_left_of_det_ne_zero` (150) | <code>theorem regularPair_add_left_of_det_ne_zero {u v : Plane} (hd : det u v ≠ 0) {l : ℝ} (hl : 0 < l) :<br>    RegularPair (u + v) (l • v)</code> | symmetric (`det_add_right`, `det_smul_self`). | 12 |
| 15 | `others_nonempty` (247) | <code>theorem others_nonempty : (others D x).Nonempty</code> | witness `⟨i, a−1⟩`: `≠ s` since `a − 1 ≠ a` (`k ≥ 3`, `sub_eq_self`), `≠ t` since `⟨i,a−1⟩ = t` makes `s, t` adjacent (`adjacent_mk_iff`). | 15 |
| 16 | `crossingPoint_not_mem_seg_other` (251) | <code>theorem crossingPoint_not_mem_seg_other (e : D.Γ.Strand) (hs : e ≠ sS D x) (ht : e ≠ tS D x) :<br>    pt D x ∉ D.Γ.seg e</code> | `Generic.crossingPoint_not_mem_seg` with `e ∉ x.val` from `D.val_eq_pair x` and `hs, ht`. | 10 |
| 17 | `r₁_pos` (259) | <code>theorem r₁_pos : 0 < r₁ D x</code> | `Finset.lt_inf'_iff`; each term positive by `IsClosed.notMem_iff_infDist_pos (isClosed_seg) (nonempty)` + `crossingPoint_not_mem_seg_other`. | 15 |
| 18 | `r₁_le_dist` (262) | <code>theorem r₁_le_dist {e : D.Γ.Strand} (hs : e ≠ sS D x) (ht : e ≠ tS D x) {q : Plane}<br>    (hq : q ∈ D.Γ.seg e) : r₁ D x ≤ dist (pt D x) q</code> | `Finset.inf'_le` + `Metric.infDist_le_dist_of_mem`. | 10 |
| 19 | `r₁_le_dist_tail` (268) | <code>theorem r₁_le_dist_tail (e : D.Γ.Strand) : r₁ D x ≤ dist (pt D x) (D.Γ.tail e)</code> | `P_l m = tail ⟨l,m⟩ = head ⟨l,m−1⟩ ∈ seg ⟨l,m−1⟩`; one of `⟨l,m⟩`, `⟨l,m−1⟩` is `∉ {s,t}` (if `⟨l,m⟩ = s` then `⟨l,m−1⟩ = s−1 ∉ {s,t}` by `k ≥ 3` and non-adjacency; same for `t`); `r₁_le_dist`. | 40 |
| 20 | `r₁_le_dist_crossingPoint` (272) | <code>theorem r₁_le_dist_crossingPoint {y : D.Γ.Crossing} (hy : y ≠ x) :<br>    r₁ D x ≤ dist (pt D x) (D.Γ.crossingPoint y)</code> | `y ≠ x` ⇒ some strand `e ∈ y.val` is `∉ {s,t}` (else `y.val = {s,t} = x.val`, `Subtype.ext`); `crossingPoint_mem`; `r₁_le_dist`. | 25 |
| 21 | `r₁_le_τs_mul` (276) | <code>theorem r₁_le_τs_mul : r₁ D x ≤ τs D x * ‖es D x‖</code> | `tail s = head ⟨i,a−1⟩ ∈ seg ⟨i,a−1⟩`, `⟨i,a−1⟩ ∉ {s,t}`; `dist p (tail s) = τs‖es‖` by `pt_eq_s`, `norm_smul`. | 10 |
| 22 | `r₁_le_one_sub_τs_mul` (278) | <code>theorem r₁_le_one_sub_τs_mul : r₁ D x ≤ (1 - τs D x) * ‖es D x‖</code> | `head s = tail ⟨i,a+1⟩ ∈ seg ⟨i,a+1⟩`; `dist = (1−τs)‖es‖`. | 10 |
| 23 | `r₁_le_τt_mul` (280) | <code>theorem r₁_le_τt_mul : r₁ D x ≤ τt D x * ‖et D x‖</code> | as for `s`. | 10 |
| 24 | `r₁_le_one_sub_τt_mul` (282) | <code>theorem r₁_le_one_sub_τt_mul : r₁ D x ≤ (1 - τt D x) * ‖et D x‖</code> | as for `s`. | 10 |
| 25 | `eps_small` (303) | <code>theorem eps_small : SmallEps D x (eps D x)</code> | `min`/`div` arithmetic; `‖es‖, ‖et‖ > 0` (`norm_pos_iff`, `es_ne_zero`); `r₁_pos`. | 30 |
| 26 | `crossingParam_far_s` (309) | <code>theorem crossingParam_far_s {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = sS D x)<br>    (hne : w.1 ≠ x) : ε < \|D.crossingParam w.1 w.2.2 - τs D x\|</code> | `eval_visitPt`: the crossing point of `w.1` is `edgePt s (param w)`; `r₁_le_dist_crossingPoint` and `dist_edgePt` give `r₁ ≤ |param − τs|‖es‖`; `SmallEps.mul_es_lt`. | 25 |
| 27 | `crossingParam_far_t` (313) | <code>theorem crossingParam_far_t {ε : ℝ} (hε : SmallEps D x ε) (w : D.Γ.Visit) (hw : w.2.val = tS D x)<br>    (hne : w.1 ≠ x) : ε < \|D.crossingParam w.1 w.2.2 - τt D x\|</code> | same with `t`. | 25 |
| 28 | `sMinus_eq_edgePoint` (330) | <code>theorem sMinus_eq_edgePoint : sMinus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x - ε)</code> | unfold `edgePoint`, `pt_eq_s`, `sub_smul`, `add_sub_assoc`. | 8 |
| 29 | `sPlus_eq_edgePoint` (332) | <code>theorem sPlus_eq_edgePoint : sPlus D x ε = edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 (τs D x + ε)</code> | same, `add_smul`. | 8 |
| 30 | `tMinus_eq_edgePoint` (334) | <code>theorem tMinus_eq_edgePoint : tMinus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x - ε)</code> | same with `t`. | 8 |
| 31 | `tPlus_eq_edgePoint` (336) | <code>theorem tPlus_eq_edgePoint : tPlus D x ε = edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 (τt D x + ε)</code> | same with `t`. | 8 |
| 32 | `dist_sMinus` (340) | <code>theorem dist_sMinus : dist (sMinus D x ε) (pt D x) = \|ε\| * ‖es D x‖</code> | `dist_eq_norm`, `sub_sub_cancel_left`, `norm_neg`, `norm_smul`. | 8 |
| 33 | `pred_succ` (468) | <code>theorem pred_succ (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.pred = κ</code> | case on `κ`; for `old e` the `if`s: `e = s−1` gives `pred cutStartS = old (s−1)` ✓; `e = t−1` similarly; else `pred (old (e+1))`: `e+1 ≠ s+1` (as `e ≠ s`), `e+1 ≠ t+1`, and `e+1−1 = e`. | 20 |
| 34 | `succ_pred` (471) | <code>theorem succ_pred (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.succ = κ</code> | symmetric. | 20 |
| 35 | `succ_occurs` (474) | <code>theorem succ_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.succ.Occurs</code> | `old (e+1) = old s` iff `e = s − 1`, which is the `cutStartS` branch; `old (s+1) ≠ old s, old t` (`k ≥ 3`, `¬Adjacent s t`). | 20 |
| 36 | `pred_occurs` (477) | <code>theorem pred_occurs (κ : StrandKind D x) (hκ : κ.Occurs) : κ.pred.Occurs</code> | symmetric. | 20 |
| 37 | `head_eq_tail_succ` (481) | <code>theorem head_eq_tail_succ (ε : ℝ) (κ : StrandKind D x) (hκ : κ.Occurs) :<br>    κ.head ε = κ.succ.tail ε</code> | case on `κ`: `P_i a + (τs−ε)es = p − ε es` (`pt_eq_s`); `s⁻ + ε(es+et) = t⁺` (`pt_eq_t`); `s⁺ + (1−τs−ε)es = P_i(a+1)` (`pt_eq_s`, `edge`); `old e`: three `if` branches (`e = s−1`: `head = P_i a = tail cutStartS`; `e = t−1`; else `head e = tail (e+1)`). | 60 |
| 38 | `tail_add_smul_dir` (487) | <code>theorem tail_add_smul_dir (ε : ℝ) (κ : StrandKind D x) (hκ : κ ≠ arcST) (hκ' : κ ≠ arcTS) (θ : ℝ) :<br>    κ.tail ε + θ • κ.dir ε = edgePoint (D.Γ.comp κ.orig.1).P κ.orig.2 (κ.origParam ε θ)</code> | algebra per kind: `P_i a + θ(τs−ε)es = edgePoint … (θ(τs−ε))`; `s⁺ + θ(1−τs−ε)es = P_i a + (τs+ε+θ(1−τs−ε))es`; `smul_add`, `add_smul`, `mul_smul`. | 30 |
| 39 | `seg_subset_seg_orig` (491) | <code>theorem seg_subset_seg_orig (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x) (hκ : κ ≠ arcST)<br>    (hκ' : κ ≠ arcTS) : κ.seg ε ⊆ D.Γ.seg κ.orig</code> | `tail_add_smul_dir`; `origParam` maps `[0,1]` into `[0,1]` under `SmallEps` (`mul_nonneg`, `nlinarith`). | 30 |
| 40 | `seg_old` (495) | <code>theorem seg_old (ε : ℝ) (e : D.Γ.Strand) : (old e : StrandKind D x).seg ε = D.Γ.seg e</code> | `Set.ext`; unfold `edgeSegment`/`edgePoint`. | 8 |
| 41 | `interior_old` (498) | <code>theorem interior_old (ε : ℝ) (e : D.Γ.Strand) :<br>    (old e : StrandKind D x).interior ε = D.Γ.interior e</code> | same. | 8 |
| 42 | `seg_arc_subset_ball` (503) | <code>theorem seg_arc_subset_ball (ε : ℝ) (hε : SmallEps D x ε) (κ : StrandKind D x)<br>    (hκ : κ = arcST ∨ κ = arcTS) :<br>    κ.seg ε ⊆ Metric.ball (pt D x) (max (ε * ‖es D x‖) (ε * ‖et D x‖))</code> | point `s⁻ + θ ε(es+et) = p + ε((θ−1)es + θ et)`; `‖(θ−1)ε es + θ ε et‖ ≤ (1−θ)ε‖es‖ + θε‖et‖ ≤ max` (`norm_add_le`, `norm_smul`); strictness: if the convex combination could equal `max`, weaken the statement to `closedBall` — `arc_lt_discRadius` already leaves strict room, so callers only need `⊆ closedBall p (max …) ⊆ ball p r`.  (If the prover keeps `ball`, argue `θ ∈ [0,1]` and one of the two weights is `< 1` unless `‖es‖ = ‖et‖`, then use `ε‖es‖ < r₁`.) | 25 |
| 43 | `dist_cut_lt` (509) | <code>theorem dist_cut_lt (ε : ℝ) (hε : SmallEps D x ε) :<br>    dist (sMinus D x ε) (pt D x) < r₁ D x ∧ dist (sPlus D x ε) (pt D x) < r₁ D x ∧<br>      dist (tMinus D x ε) (pt D x) < r₁ D x ∧ dist (tPlus D x ε) (pt D x) < r₁ D x</code> | `dist_sMinus` (+ the three analogues), `abs_of_pos`, `SmallEps.mul_es_lt/mul_et_lt`. | 15 |
| 44 | `kind_succ` (556) | <code>theorem kind_succ (u : Γ₀.Strand) : M.kind ⟨u.1, u.2 + 1⟩ = (M.kind u).succ</code> | `kind_pred` at `⟨u.1, u.2+1⟩` (`add_sub_cancel_right`) gives `kind u = (kind ⟨u.1,u.2+1⟩).pred`; apply `succ_pred` with `kind_occurs`. | 15 |
| 45 | `seg_eq` (559) | <code>theorem seg_eq (u : Γ₀.Strand) : Γ₀.seg u = (M.kind u).seg ε</code> | unfold `Shadow.seg = edgeSegment`, `edgePoint = P m + θ•edge`; `tail_eq`, `dir_eq`. | 10 |
| 46 | `interior_eq` (562) | <code>theorem interior_eq (u : Γ₀.Strand) : Γ₀.interior u = (M.kind u).interior ε</code> | same. | 10 |
| 47 | `head_eq` (565) | <code>theorem head_eq (u : Γ₀.Strand) : Γ₀.head u = (M.kind u).head ε</code> | `head u = tail ⟨u.1, u.2+1⟩ = tail u + dir u`; `tail_eq`, `dir_eq`. | 10 |
| 48 | `adjacent_iff` (569) | <code>theorem adjacent_iff (u u' : Γ₀.Strand) : Γ₀.Adjacent u u' ↔ (M.kind u).Adj (M.kind u')</code> | `Adjacent ⟨l,m⟩ ⟨l,m'⟩ ↔ m' − m ∈ {−1,0,1}` (`adjacent_iff`/`adjacent_mk_iff`) ↔ `u' ∈ {⟨l,m−1⟩, u, ⟨l,m+1⟩}` ↔ kinds by `kind_pred`, `kind_succ`, `kind_injective`; different components: both sides false (`Adj` of kinds would force equal strands by injectivity). | 30 |
| 49 | `incidentTail_iff` (572) | <code>theorem incidentTail_iff (u u' : Γ₀.Strand) :<br>    Γ₀.IncidentTail u u' ↔ (M.kind u).Incident (M.kind u')</code> | `incident a b ↔ b = a − 1 ∨ b = a` ↔ `u' ∈ {⟨l,m−1⟩, u}` ↔ `Incident` by `kind_pred`, injectivity. | 20 |
| 50 | `adjacent_old_iff` (577) | <code>theorem adjacent_old_iff (e e' : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)<br>    (he' : e' ≠ sS D x ∧ e' ≠ tS D x) :<br>    (StrandKind.old e : StrandKind D x).Adj (StrandKind.old e') ↔ D.Γ.Adjacent e e'</code> | `succ (old e) = old (e+1)` when `e ≠ s−1, t−1` and `pred (old e) = old (e−1)` when `e ≠ s+1, t+1`; in the cut branches `Adj (old e) (old e')` is false since `e' ∉ {s,t}`; `adjacent_mk_iff`, `Sigma.ext_iff`. | 30 |
| 51 | `eval_eq` (583) | <code>theorem eval_eq (q : Γ₀.Pt) :<br>    Γ₀.eval q = (M.kind ⟨q.1, q.2.1⟩).tail ε + q.2.2.val • (M.kind ⟨q.1, q.2.1⟩).dir ε</code> | `eval ⟨l,(m,θ)⟩ = edgePoint P m θ = P m + θ•edge P m`; `tail_eq`, `dir_eq`. | 10 |

### U2-disc-and-D-arcs — The disc, frontier parameters, cyclic-order lemmas on `TraversalPoint`, cleanness and the two arcs of `D` (§5)  (≈ 480 lines)

Depends on: U1-clearance-kinds.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `discRadius_pos` (601) | <code>theorem discRadius_pos (hε : SmallEps D x ε) : 0 < discRadius D x ε</code> | `SmallEps.pos`, `r₁_pos`, `le_max_left`, `norm_nonneg`. | 8 |
| 2 | `discRadius_lt_r₁` (604) | <code>theorem discRadius_lt_r₁ (hε : SmallEps D x ε) : discRadius D x ε < r₁ D x</code> | midpoint: `max (ε‖es‖) (ε‖et‖) < r₁` from `mul_es_lt`, `mul_et_lt`. | 8 |
| 3 | `arc_lt_discRadius` (607) | <code>theorem arc_lt_discRadius (hε : SmallEps D x ε) :<br>    max (ε * ‖es D x‖) (ε * ‖et D x‖) < discRadius D x ε</code> | same midpoint arithmetic. | 8 |
| 4 | `mem_seg_of_mem_disc` (623) | <code>theorem mem_seg_of_mem_disc (hε : SmallEps D x ε) {e : D.Γ.Strand} {q : Plane} (hq : q ∈ D.Γ.seg e)<br>    (hU : q ∈ disc D x ε) : e = sS D x ∨ e = tS D x</code> | by contradiction: `e ∉ {s,t}` ⇒ `r₁ ≤ dist p q` (`r₁_le_dist`) but `dist q p ≤ r < r₁`. | 15 |
| 5 | `crossingPoint_ne_not_mem_disc` (628) | <code>theorem crossingPoint_ne_not_mem_disc (hε : SmallEps D x ε) {y : D.Γ.Crossing} (hy : y ≠ x) :<br>    D.Γ.crossingPoint y ∉ disc D x ε</code> | `r₁_le_dist_crossingPoint`, `discRadius_lt_r₁`, `Metric.mem_closedBall`. | 10 |
| 6 | `tail_not_mem_disc` (633) | <code>theorem tail_not_mem_disc (hε : SmallEps D x ε) (e : D.Γ.Strand) : D.Γ.tail e ∉ disc D x ε</code> | `r₁_le_dist_tail`. | 10 |
| 7 | `θsIn_pos` (643) | <code>theorem θsIn_pos (hε : SmallEps D x ε) : 0 < θsIn D x ε</code> | `r < r₁ ≤ τs‖es‖` (`r₁_le_τs_mul`), `div_lt_iff`. | 5 |
| 8 | `θsOut_lt_one` (645) | <code>theorem θsOut_lt_one (hε : SmallEps D x ε) : θsOut D x ε < 1</code> | `r₁_le_one_sub_τs_mul`. | 5 |
| 9 | `θtIn_pos` (647) | <code>theorem θtIn_pos (hε : SmallEps D x ε) : 0 < θtIn D x ε</code> | as `s`. | 5 |
| 10 | `θtOut_lt_one` (649) | <code>theorem θtOut_lt_one (hε : SmallEps D x ε) : θtOut D x ε < 1</code> | as `s`. | 5 |
| 11 | `θsIn_lt_θsOut` (651) | <code>theorem θsIn_lt_θsOut (hε : SmallEps D x ε) : θsIn D x ε < θsOut D x ε</code> | `r/‖es‖ > 0`. | 5 |
| 12 | `θtIn_lt_θtOut` (653) | <code>theorem θtIn_lt_θtOut (hε : SmallEps D x ε) : θtIn D x ε < θtOut D x ε</code> | same. | 5 |
| 13 | `θsIn_lt_cut` (658) | <code>theorem θsIn_lt_cut (hε : SmallEps D x ε) : θsIn D x ε < τs D x - ε ∧ τs D x + ε < θsOut D x ε</code> | `ε‖es‖ ≤ max < r` (`arc_lt_discRadius`) ⇒ `ε < r/‖es‖`. | 10 |
| 14 | `θtIn_lt_cut` (660) | <code>theorem θtIn_lt_cut (hε : SmallEps D x ε) : θtIn D x ε < τt D x - ε ∧ τt D x + ε < θtOut D x ε</code> | same. | 10 |
| 15 | `edgePoint_s_mem_disc_iff` (665) | <code>theorem edgePoint_s_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :<br>    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ disc D x ε ↔<br>      θsIn D x ε ≤ θ ∧ θ ≤ θsOut D x ε</code> | `dist (edgePt s θ) p = |θ − τs|‖es‖` (`pt_eq_s` as `edgePt s τs`, `dist_edgePt`); `abs_sub_le_iff`, `div`. | 15 |
| 16 | `edgePoint_s_mem_ball_iff` (670) | <code>theorem edgePoint_s_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :<br>    edgePoint (D.Γ.comp (sS D x).1).P (sS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔<br>      θsIn D x ε < θ ∧ θ < θsOut D x ε</code> | same with `<`. | 15 |
| 17 | `edgePoint_t_mem_disc_iff` (675) | <code>theorem edgePoint_t_mem_disc_iff (hε : SmallEps D x ε) (θ : ℝ) :<br>    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ disc D x ε ↔<br>      θtIn D x ε ≤ θ ∧ θ ≤ θtOut D x ε</code> | same with `t`. | 15 |
| 18 | `edgePoint_t_mem_ball_iff` (680) | <code>theorem edgePoint_t_mem_ball_iff (hε : SmallEps D x ε) (θ : ℝ) :<br>    edgePoint (D.Γ.comp (tS D x).1).P (tS D x).2 θ ∈ Metric.ball (pt D x) (discRadius D x ε) ↔<br>      θtIn D x ε < θ ∧ θ < θtOut D x ε</code> | same with `t`. | 15 |
| 19 | `θ₀_mem` (691) | <code>theorem θ₀_mem (hε : SmallEps D x ε) : θ₀sIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀sOut D x ε ∈ Set.Ico (0:ℝ) 1 ∧<br>    θ₀tIn D x ε ∈ Set.Ico (0:ℝ) 1 ∧ θ₀tOut D x ε ∈ Set.Ico (0:ℝ) 1</code> | `θsIn/(τs−ε) ∈ [0,1)`: `0 < θsIn < τs − ε` (`θsIn_pos`, `θsIn_lt_cut`), `div_lt_one`; `(θsOut − τs − ε)/(1−τs−ε)`: `0 < θsOut − τs − ε` and `θsOut < 1`; same for `t`. | 30 |
| 20 | `traversalBetween_same_edge` (698) | <code>theorem traversalBetween_same_edge {n : ℕ} [NeZero n] (a : ZMod n) (θ₁ θ₂ : Set.Ico (0:ℝ) 1)<br>    (h : θ₁.val < θ₂.val) (r : TraversalPoint n) :<br>    traversalBetween (a, θ₁) r (a, θ₂) ↔ r.1 = a ∧ θ₁.val < r.2.val ∧ r.2.val < θ₂.val</code> | unfold `traversalBetween`, `traversalKey = val + θ`; keys `a.val + θ₁ < a.val + θ₂`; the two wrap disjuncts are impossible (`linarith`); the middle key `r.1.val + r.2 ∈ (a.val+θ₁, a.val+θ₂)` forces `r.1.val = a.val` (integer part, `Nat.cast` bounds with `r.2 ∈ [0,1)`), then `ZMod.val_injective`. | 40 |
| 21 | `traversalBetween_span_two` (705) | <code>theorem traversalBetween_span_two {n : ℕ} [NeZero n] (m : ZMod n) (hm : m.val + 2 < n)<br>    (θ₁ θ₂ : Set.Ico (0:ℝ) 1) (r : TraversalPoint n) :<br>    traversalBetween (m, θ₁) r (m + 2, θ₂) ↔<br>      (r.1 = m ∧ θ₁.val < r.2.val) ∨ r.1 = m + 1 ∨ (r.1 = m + 2 ∧ r.2.val < θ₂.val)</code> | `(m+1).val = m.val+1`, `(m+2).val = m.val+2` (`ZMod.val_add_of_lt`, `hm`); keys in `[m.val + θ₁, m.val + 2 + θ₂)`, no wrap; three sub-cases by `⌊key r⌋ ∈ {m.val, m.val+1, m.val+2}`; `ZMod.val_injective`. | 50 |
| 22 | `clean_D` (716) | <code>theorem clean_D : Clean (disc D x ε) D</code> | `frontier_disc`; a frontier traversal point lies on `s` or `t` (`mem_seg_of_mem_disc`); two with equal `eval`: same strand ⇒ same parameter (`Generic.edgePt_injective`) ⇒ equal (`Sigma.ext`); `s` vs `t` ⇒ common point `= p` (`Generic.seg_inter_seg_eq`) not on the sphere (`dist p p = 0 ≠ r`). `exits`: `⟨l,(0,⟨0,_⟩)⟩` evaluates to a vertex, `tail_not_mem_disc`. | 60 |
| 23 | `center_mem` (719) | <code>theorem center_mem : pt D x ∈ interior (disc D x ε)</code> | `interior_disc`, `Metric.mem_ball_self`. | 5 |
| 24 | `arcS_ne_arcT` (738) | <code>theorem arcS_ne_arcT : arcS D x hε ≠ arcT D x hε</code> | components differ or edge labels `a ≠ b` (`sS_ne_tS`, `Sigma.ext_iff`); `Arc.mk.injEq`. | 10 |
| 25 | `arcCover_D` (741) | <code>theorem arcCover_D : D.Γ.ArcCover (disc D x ε) {arcS D x hε, arcT D x hε}</code> | `isArc`: `start ≠ stop` (`θsIn_lt_θsOut`), ends on the sphere (`edgePoint_s_mem_disc_iff` at equality: `|θsIn − τs|‖es‖ = r`), inner points via `Arc.inner_mk_iff` + `traversalBetween_same_edge` + `edgePoint_s_mem_ball_iff`. `mem_iff`: `eval q ∈ disc` ⇒ strand `∈ {s,t}` (`mem_seg_of_mem_disc`) with parameter in `[θIn, θOut]` ⇒ `Mem` (end or inner); converse from the three `Mem` cases. `disjoint`: `Mem arcS q ⇒ q.1 = i ∧ q.2.1 = a`, `Mem arcT q ⇒ … = b`, `s ≠ t`. | 90 |
| 26 | `overOn_arcS` (744) | <code>theorem overOn_arcS : D.OverOn (arcS D x hε) x</code> | `visitPt (overVisit x) = ⟨i,(a,τs)⟩`; `Arc.inner_mk_iff`, `traversalBetween_same_edge`, `θsIn < τs < θsOut`. | 8 |
| 27 | `underOn_arcT` (747) | <code>theorem underOn_arcT : D.UnderOn (arcT D x hε) x</code> | same with `t`. | 8 |
| 28 | `inner_iff_D` (750) | <code>theorem inner_iff_D (y : D.Γ.Crossing) : D.Γ.crossingPoint y ∈ interior (disc D x ε) ↔ y = x</code> | `←`: `center_mem`; `→`: `crossingPoint_ne_not_mem_disc` (interior ⊆ disc). | 10 |

### U3-model-genericity-crossings — Genericity of any splice model and the crossing correspondence (§6a-6b)  (≈ 720 lines)

Depends on: U1-clearance-kinds, U2-disc-and-D-arcs.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `kind_disjoint` (773) | <code>theorem kind_disjoint (κ κ' : StrandKind D x) (hκ : ¬ ∃ e, κ = StrandKind.old e)<br>    (hadj : ¬ κ.Adj κ') (hold : ∀ e, κ' = StrandKind.old e → False) :<br>    Disjoint (κ.seg ε) (κ'.seg ε)</code> | cases on `(κ, κ')`: two cut pieces of one strand (parameter ranges `[0,τ−ε]`, `[τ+ε,1]` disjoint via `tail_add_smul_dir` + `edgePt_injective`); cut piece of `s` vs cut piece of `t` (common point `∈ seg s ∩ seg t = {p}` by `seg_inter_seg_eq`, but `p = edgePt s τs` has parameter `τs` outside both pieces); arc vs arc (`coords_unique` on `p + ε((μ−1)es + μ et) = p + ε(ν es + (ν−1)et)`: `μ−1 = ν ∧ μ = ν−1`); arc vs non-adjacent cut piece (`coords_unique`: the `et`-coefficient `εμ = 0` forces the endpoint, excluded by non-adjacency); arc vs old (`seg_arc_subset_ball` + `r₁_le_dist`). | 120 |
| 2 | `cut_inter_old` (782) | <code>theorem cut_inter_old (κ : StrandKind D x) (hκ : κ ≠ StrandKind.arcST ∧ κ ≠ StrandKind.arcTS)<br>    (hκo : ¬ ∃ e, κ = StrandKind.old e) (e : D.Γ.Strand) (he : e ≠ sS D x ∧ e ≠ tS D x)<br>    (hmeet : (κ.seg ε ∩ D.Γ.seg e).Nonempty) (hadj : ¬ κ.Adj (StrandKind.old e)) :<br>    ¬ D.Γ.Adjacent κ.orig e</code> | if `Adjacent (orig κ) e` then `e = orig κ ± 1` and `seg (orig κ) ∩ seg e = {common vertex}` (`Generic.seg_inter_succ`); the vertex lies on exactly one of the two cut pieces of `orig κ` (parameter `0` on `cutStart`, `1` on `cutEnd`), and that pair is `Adj` (`pred cutStartS = old (s−1)`, `succ cutEndS = old (s+1)`), contradicting `hadj`. | 50 |
| 3 | `regular` (791) | <code>theorem regular (i : Fin Γ₀.c) : Regular (Γ₀.comp i).P</code> | `regular_iff_edges`; consecutive edges `⟨l,m−1⟩, ⟨l,m⟩` have kinds `κ.pred, κ` (`kind_pred`) with directions `dir_eq`; cases: old/old inherited from `D.generic.regular` (labels `e−1, e` in `D`); old/`cutStartS`: `(dir (s−1), (τs−ε)•es)` = `regularPair_smul_pos` of `D`'s pair at `s`; `cutStartS/arcST`: `((τs−ε)es, ε(es+et))` by `regularPair_add_right_of_det_ne_zero` (after factoring `ε`, `regularPair_smul_pos`); `arcST/cutEndT`: `regularPair_add_left…`; `cutEndS/old(s+1)`: `regularPair_smul_pos`. | 90 |
| 4 | `tail_off` (794) | <code>theorem tail_off (u u' : Γ₀.Strand) (h : ¬ Γ₀.IncidentTail u u') : Γ₀.tail u ∉ Γ₀.seg u'</code> | `tail u` is an old vertex or a cut point (`tail_eq`). Old vertex vs old strand: `D.generic.tail_off`, incidence transported by `incidentTail_iff`/`adjacent_old_iff`; old vertex vs cut piece: a vertex on `seg s` is `tail s` or `head s` (`D.generic.tail_off` at `s`), i.e. parameters `0`/`1`, on `cutStartS` only at `θ=0` = incident, on `cutEndS` only at `θ=1` = head = tail of `old (s+1)`, incident; old vertex vs arc: `tail_not_mem_disc` vs `seg_arc_subset_ball`; cut point vs old strand `e`: `dist_cut_lt` vs `r₁_le_dist`; cut point vs other cut piece/arc: `kind_disjoint` and parameters. | 100 |
| 5 | `transverse` (797) | <code>theorem transverse (u u' : Γ₀.Strand) (h : ¬ Γ₀.Adjacent u u')<br>    (hmeet : (Γ₀.seg u ∩ Γ₀.seg u').Nonempty) : det (Γ₀.dir u) (Γ₀.dir u') ≠ 0</code> | classify by `adjacent_iff`: both old ⇒ `D.generic.transverse` (`adjacent_old_iff`); old vs cut piece ⇒ `cut_inter_old` gives non-adjacent in `D`, meeting (`seg_subset_seg_orig`), so `det (dir e) (λ•es) = λ·det ≠ 0` (`det_smul_right`); every other non-adjacent pair is disjoint (`kind_disjoint`), contradicting `hmeet`. | 50 |
| 6 | `no_triple` (801) | <code>theorem no_triple : ¬ ∃ u u' u'' : Γ₀.Strand, u ≠ u' ∧ u' ≠ u'' ∧ u ≠ u'' ∧<br>    (Γ₀.interior u ∩ Γ₀.interior u' ∩ Γ₀.interior u'').Nonempty</code> | a common interior point `q` of three strands: if one is an arc, `q ∈ ball p r₁`, so the other two are cut pieces or the other arc (old strands are `≥ r₁` away), all disjoint from the arc except at endpoints, which are not interior; if none is an arc: two cut pieces of the same strand are disjoint, of different strands meet only at `p` (not interior to a cut piece), so at most one cut piece and ≥ 2 old strands ⇒ triple point of `D` at `q` under `orig` (`seg_subset_seg_orig`), `D.generic.no_triple`. | 50 |
| 7 | `isCrossing_orig` (816) | <code>theorem isCrossing_orig {u u' : Γ₀.Strand} (h : Γ₀.IsCrossing {u, u'}) :<br>    D.Γ.IsCrossing {M.orig u, M.orig u'} ∧ ({M.orig u, M.orig u'} : Finset D.Γ.Strand) ≠ x.val</code> | from the classification in `transverse`: a meeting non-adjacent pair is old/old or old/cut; `orig` pair non-adjacent in `D` (`adjacent_old_iff`, `cut_inter_old`) and meeting (`seg_subset_seg_orig`); `≠ x.val` since `x.val = {s,t}` and an old strand is `∉ {s,t}`. | 40 |
| 8 | `origCrossing_ne` (824) | <code>theorem origCrossing_ne (y : Γ₀.Crossing) : origCrossing D x M hε y ≠ x</code> | `(isCrossing_orig …).2` and `Subtype.ext`. | 10 |
| 9 | `orig_mem_origCrossing` (827) | <code>theorem orig_mem_origCrossing {y : Γ₀.Crossing} {u : Γ₀.Strand} (hu : u ∈ y.val) :<br>    M.orig u ∈ (origCrossing D x M hε y).val</code> | `y.val_eq`, `Finset.mem_insert`/`mem_singleton`. | 10 |
| 10 | `origCrossing_injective` (831) | <code>theorem origCrossing_injective : Function.Injective (origCrossing D x M hε)</code> | `orig` is injective on a crossing (`orig_injOn_crossing`) and `{orig fst, orig snd}` determines the two kinds up to the cut-piece ambiguity, resolved because the two cut pieces of `s` are disjoint (`kind_disjoint`) so only one meets the other strand at the crossing point; `Subtype.ext`, `Finset` pair equality. | 20 |
| 11 | `crossingPoint_origCrossing` (835) | <code>theorem crossingPoint_origCrossing (y : Γ₀.Crossing) :<br>    Γ₀.crossingPoint y = D.Γ.crossingPoint (origCrossing D x M hε y)</code> | `common_point_unique` for `D` at `origCrossing y`: `Γ₀.crossingPoint y ∈ seg u ⊆ seg (orig u)` (`seg_subset_seg_orig`) for both strands. | 20 |
| 12 | `orig_liftStrand` (852) | <code>theorem orig_liftStrand (y : D.Γ.Crossing) (e : D.Γ.Strand) (he : e ∈ y.val) :<br>    M.orig (liftStrand D x M y e he) = e</code> | unfold `liftStrand`; `split_ifs`; `kind_strandOf`; `StrandKind.orig`. | 15 |
| 13 | `isCrossing_lift` (857) | <code>theorem isCrossing_lift {y : D.Γ.Crossing} (hy : y ≠ x) :<br>    Γ₀.IsCrossing {liftStrand D x M y y.fst y.fst_mem, liftStrand D x M y y.snd y.snd_mem}</code> | the lifted strands are non-adjacent (`adjacent_iff`: kinds `old e`/cut pieces are `Adj` only when `e = s ± 1` etc., excluded by `¬Adjacent e s` in `D`) and meet at `crossingPoint y`: for `e ∉ {s,t}` on `seg (old e)`; for `e = s`: `crossingParam y ≠ τs` and `|param − τs| > ε` (`crossingParam_far_s` with `w := ⟨y, ⟨s, he⟩⟩`), so the point lies on `cutStartS` iff `param < τs` (`tail_add_smul_dir`, `liftParam`). | 60 |
| 14 | `origCrossing_liftCrossing` (865) | <code>theorem origCrossing_liftCrossing (y : D.Γ.Crossing) (hy : y ≠ x) :<br>    origCrossing D x M hε (liftCrossing D x M hε y hy) = y</code> | `Subtype.ext`; `orig_liftStrand` twice; `y.val_eq`. | 30 |
| 15 | `liftCrossing_origCrossing` (869) | <code>theorem liftCrossing_origCrossing (y : Γ₀.Crossing) :<br>    liftCrossing D x M hε (origCrossing D x M hε y) (origCrossing_ne D x M hε y) = y</code> | `Subtype.ext`; the lift of `orig u` is `u`: `kind_injective` after showing the chosen cut piece is the one containing the crossing point (uniqueness of the containing piece). | 40 |
| 16 | `orig_injOn_crossing` (881) | <code>theorem orig_injOn_crossing (y : Γ₀.Crossing) {u u' : Γ₀.Strand} (hu : u ∈ y.val) (hu' : u' ∈ y.val)<br>    (h : M.orig u = M.orig u') : u = u'</code> | two strands of a crossing with the same `orig` are both cut pieces of one strand or equal; two cut pieces of one strand are disjoint (`kind_disjoint`) hence not a crossing pair. | 15 |

### U4-model-outside-arcs — Over data and signs, cleanness of `D₀`, the two smoothing arcs, the outside match (§6c-6e)  (≈ 825 lines)

Depends on: U1-clearance-kinds, U2-disc-and-D-arcs, U3-model-genericity-crossings.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `orig_overStrand₀` (898) | <code>theorem orig_overStrand₀ (y : Γ₀.Crossing) :<br>    M.orig (overStrand₀ D x M hε y) = D.overStrand (origCrossing D x M hε y)</code> | unfold `overStrand₀`; `split_ifs`; else branch: `orig fst ≠ over ⇒ orig fst = under ⇒ orig snd = over` (`orig_injOn_crossing`, `eq_over_of_mem_of_ne`). | 20 |
| 2 | `toDiagram_underStrand_orig` (911) | <code>theorem toDiagram_underStrand_orig (y : Γ₀.Crossing) :<br>    M.orig ((toDiagram D x M hε).underStrand y) = D.underStrand (origCrossing D x M hε y)</code> | `underStrand = other (overStrand₀)`; `orig_injOn_crossing` + `eq_under_of_mem_of_ne`. | 20 |
| 3 | `toDiagram_sign` (916) | <code>theorem toDiagram_sign (y : Γ₀.Crossing) :<br>    (toDiagram D x M hε).sign y = D.sign (origCrossing D x M hε y)</code> | `dir_eq`: `dir u = λ_u • dir (orig u)` with `λ_u > 0` for non-arc kinds (crossings never involve arcs, `isCrossing_orig`); `det_smul_left/right`, `sign_mul`, `sign_pos`. | 25 |
| 4 | `crossingParam_toDiagram` (921) | <code>theorem crossingParam_toDiagram (y : Γ₀.Crossing) {u : Γ₀.Strand} (hu : u ∈ y.val) :<br>    (toDiagram D x M hε).crossingParam y hu =<br>      (M.kind u).liftParam ε (D.crossingParam (origCrossing D x M hε y)<br>        (orig_mem_origCrossing D x M hε hu))</code> | both parameters describe the same point `Γ₀.crossingPoint y = D.crossingPoint (origCrossing y)` (`crossingPoint_origCrossing`, `crossingParam_spec`); `tail_add_smul_dir` and `edgePt_injective` on the original strand give `origParam (param₀) = param_D`, then `liftParam ∘ origParam = id` (field arithmetic, `SmallEps` for nonzero denominators). | 40 |
| 5 | `clean_toDiagram` (937) | <code>theorem clean_toDiagram : Clean (disc D x ε) (toDiagram D x M hε)</code> | a frontier point is on a cut piece (old strands are outside `disc`: `mem_seg_of_mem_disc`; arcs inside the open ball: `seg_arc_subset_ball`, `arc_lt_discRadius`); each cut piece meets the sphere in one parameter (`edgePoint_s_mem_disc_iff` at equality + `tail_add_smul_dir`); cut pieces pairwise disjoint (`kind_disjoint`, or of the same strand by parameter ranges); `exits`: every component has an old strand (iterate `kind_pred` ≤ 3 times from any strand), whose tail is an old vertex `∉ disc` (`tail_not_mem_disc`). | 90 |
| 6 | `strandOf_cutEndT_eq` (962) | <code>theorem strandOf_cutEndT_eq :<br>    M.strandOf StrandKind.cutEndT StrandKind.occurs_cutEndT =<br>      ⟨(M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).1,<br>        (M.strandOf StrandKind.cutStartS StrandKind.occurs_cutStartS).2 + 2⟩</code> | `kind_succ` twice at `strandOf cutStartS`: kinds `arcST`, `cutEndT`; `kind_injective`. | 15 |
| 7 | `strandOf_cutEndS_eq` (969) | <code>theorem strandOf_cutEndS_eq :<br>    M.strandOf StrandKind.cutEndS StrandKind.occurs_cutEndS =<br>      ⟨(M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).1,<br>        (M.strandOf StrandKind.cutStartT StrandKind.occurs_cutStartT).2 + 2⟩</code> | same from `cutStartT`. | 15 |
| 8 | `arcST₀_ne_arcTS₀` (988) | <code>theorem arcST₀_ne_arcTS₀ : arcST₀ D x M hε ≠ arcTS₀ D x M hε</code> | the start strands have different kinds, hence differ (`kind_injective`); compare `Arc.i`/`Arc.start` via `Sigma.ext_iff`. | 10 |
| 9 | `arcCover_toDiagram` (991) | <code>theorem arcCover_toDiagram : Γ₀.ArcCover (disc D x ε) {arcST₀ D x M hε, arcTS₀ D x M hε}</code> | `isArc`: `start ≠ stop` (labels differ by `2`, `strandOf_cutStartS_val`); ends on the sphere (`eval_eq`, `tail_add_smul_dir`, `origParam ∘ liftParam = id` at `θsIn`/`θtOut`, `edgePoint_*_mem_disc_iff`); inner points via `Arc.inner_mk_iff` + `traversalBetween_span_two` (hypothesis `strandOf_cutStartS_val`): on `cutStartS` after `θ₀sIn`, on `arcST` (inside the open ball by `seg_arc_subset_ball`), or on `cutEndT` before `θ₀tOut`. `mem_iff`: `eval q ∈ disc` ⇒ kind is a cut piece or an arc (`mem_seg_of_mem_disc` on the original via `seg_subset_seg_orig`) ⇒ `Mem` of the corresponding arc; `disjoint`: the two arcs live on disjoint kind sets `{cutStartS, arcST, cutEndT}` vs `{cutStartT, arcTS, cutEndS}`. | 150 |
| 10 | `arcST₀_start` (994) | <code>theorem arcST₀_start : Γ₀.eval (arcST₀ D x M hε).startPt = D.Γ.eval (arcS D x hε).startPt</code> | `eval_eq`, `tail_add_smul_dir`, `origParam (liftParam θsIn) = θsIn`. | 10 |
| 11 | `arcST₀_stop` (996) | <code>theorem arcST₀_stop : Γ₀.eval (arcST₀ D x M hε).stopPt = D.Γ.eval (arcT D x hε).stopPt</code> | same at `θtOut` on `cutEndT` (`strandOf_cutEndT_eq`). | 10 |
| 12 | `arcTS₀_start` (998) | <code>theorem arcTS₀_start : Γ₀.eval (arcTS₀ D x M hε).startPt = D.Γ.eval (arcT D x hε).startPt</code> | same. | 10 |
| 13 | `arcTS₀_stop` (1000) | <code>theorem arcTS₀_stop : Γ₀.eval (arcTS₀ D x M hε).stopPt = D.Γ.eval (arcS D x hε).stopPt</code> | same. | 10 |
| 14 | `origParam_mem` (1021) | <code>theorem origParam_mem (κ : StrandKind D x) (θ : Set.Ico (0:ℝ) 1) :<br>    κ.origParam ε θ.val ∈ Set.Ico (0:ℝ) 1</code> | case on `κ`: `θ(τs−ε) ∈ [0, τs−ε) ⊆ [0,1)`; `τs+ε+θ(1−τs−ε) ∈ [τs+ε, 1)`; arcs: `τs ∈ (0,1)`; `nlinarith` with `SmallEps`. | 15 |
| 15 | `eval_origPt` (1030) | <code>theorem eval_origPt (q : Γ₀.Pt) (hq : Γ₀.eval q ∉ interior (disc D x ε)) :<br>    D.Γ.eval (origPt D x M q) = Γ₀.eval q</code> | `eval_eq`; kind is not an arc (arcs lie in the open ball: `seg_arc_subset_ball`, `arc_lt_discRadius`, `interior_disc`); `origPt_param`; `tail_add_smul_dir`. | 50 |
| 16 | `origPt_bijective` (1039) | <code>theorem origPt_bijective :<br>    Function.Bijective (fun q : Γ₀.Outside (disc D x ε) =><br>      (⟨origPt D x M q.1, origPt_outside D x M hε q.1 q.2⟩ : D.Γ.Outside (disc D x ε)))</code> | injective: equal `origPt` ⇒ same `orig` strand and same `origParam` value; same `orig` with two different kinds means two cut pieces of one strand, whose `origParam` ranges `[0,τ−ε)`, `[τ+ε,1)` are disjoint ⇒ same kind ⇒ same strand (`kind_injective`) and same parameter (`origParam` injective per kind); surjective: an outside point `⟨e, θ⟩` with `e ∉ {s,t}` lifts to `⟨strandOf (old e), θ⟩`; on `s` with `θ ≤ θsIn` (resp. `≥ θsOut`) to `cutStartS` (resp. `cutEndS`) at `liftParam θ` (in `[0,1)` by `θsIn_lt_cut`); `θ ∈ (θsIn, θsOut)` is excluded by `edgePoint_s_mem_ball_iff` (the point would be in the open disc). | 100 |
| 17 | `outsideEquiv_eval` (1048) | <code>theorem outsideEquiv_eval (q : D.Γ.Outside (disc D x ε)) :<br>    Γ₀.eval (outsideEquiv D x M hε q).1 = D.Γ.eval q.1</code> | `Equiv.ofBijective_apply_symm_apply` gives `origPt (φ q) = q`; `eval_origPt`. | 15 |
| 18 | `outsideEquiv_dir_pos` (1052) | <code>theorem outsideEquiv_dir_pos (q : D.Γ.Outside (disc D x ε)) (hq : D.Γ.eval q.1 ∉ disc D x ε) :<br>    ∃ l : ℝ, 0 < l ∧<br>      Γ₀.dir (Γ₀.strandOf (outsideEquiv D x M hε q).1) = l • D.Γ.dir (D.Γ.strandOf q.1)</code> | `q' := φ q` has `origPt q' = q`, so `orig (strandOf q') = strandOf q`; `dir_eq` with `λ ∈ {1, τs−ε, 1−τs−ε, τt−ε, 1−τt−ε}` (`SmallEps` positivity); the kind is not an arc (`q'` is outside the open disc). | 40 |
| 19 | `outsideEquiv_dir_pos_before` (1057) | <code>theorem outsideEquiv_dir_pos_before (q : D.Γ.Outside (disc D x ε))<br>    (hq : D.Γ.eval q.1 ∉ disc D x ε) :<br>    ∃ l : ℝ, 0 < l ∧ Γ₀.dir (Γ₀.strandBefore (outsideEquiv D x M hε q).1) =<br>      l • D.Γ.dir (D.Γ.strandBefore q.1)</code> | `strandBefore` (parameter `0` ⇒ previous strand): the parameter of `q'` is `0` iff `origParam = 0` iff (old, cutStart kinds) the parameter of `q` is `0`; then `kind ⟨l,m−1⟩ = pred` (`kind_pred`): `pred (old e) ∈ {old (e−1), cutEndS (e = s+1), cutEndT}` with `dir` a positive multiple of `dir (e−1)`; `pred cutStartS = old (s−1)`; cut-end pieces never have parameter `0` (`origParam > 0`), so `strandBefore = strandOf` on both sides. | 60 |
| 20 | `outsideEquiv_outerOverPt` (1070) | <code>theorem outsideEquiv_outerOverPt (y : D.OuterCrossing (disc D x ε)) :<br>    outsideEquiv D x M hε (D.outerOverPt y) =<br>      (toDiagram D x M hε).outerOverPt (outerEquiv D x M hε y)</code> | `outerEquiv` unfolds to `liftCrossing`; the over strand of `liftCrossing y` is `liftStrand y (overStrand y)` (`orig_overStrand₀`, `orig_liftStrand`, `orig_injOn_crossing`); its `visitPt` has parameter `liftParam (crossingParam y)` (`crossingParam_toDiagram`), whose `origPt` is `visitPt (overVisit y)` (`origParam ∘ liftParam = id`); conclude with `Equiv.symm_apply_eq` for `Equiv.ofBijective`. | 60 |
| 21 | `outsideEquiv_outerUnderPt` (1075) | <code>theorem outsideEquiv_outerUnderPt (y : D.OuterCrossing (disc D x ε)) :<br>    outsideEquiv D x M hε (D.outerUnderPt y) =<br>      (toDiagram D x M hε).outerUnderPt (outerEquiv D x M hε y)</code> | same with `toDiagram_underStrand_orig`. | 60 |

### U5-concrete-models — The two explicit shadows are splice models — pure `ZMod.val` index arithmetic (§7)  (≈ 595 lines)

Depends on: nothing beyond the definitions of the skeleton.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `card_othersM` (1166) | <code>theorem card_othersM (h : (sS D x).1 ≠ (tS D x).1) : (othersM D x).card + 2 = D.Γ.c</code> | `Finset.card_erase_of_mem` twice (`j ∈ univ.erase i` by `h`), `Finset.card_univ`, `Fintype.card_fin`. | 15 |
| 2 | `mixedModel` (1200) | <code>def mixedModel (h : (sS D x).1 ≠ (tS D x).1) : SpliceModel D x ε (mixedShadow D x ε)</code> | all seven fields by `Fin.cases` on the component (`obtain ⟨l, m⟩ := u; induction l using Fin.cases`) and `ZMod.val` case analysis on `mergedKindIdx`: `kind_injective` (old kinds determine `l` and `m.val` — `ZMod.val_natCast` with `m.val < N`; the eight special indices are distinct); `kind_surj`/`kind_occurs` (an old `e ∉ {s,t}`: `e.1 ∈ othersM` ⇒ `⟨index via Finset.range_orderEmbOfFin, e.2⟩`, else `e.1 = i` and `e = ⟨i, a+1+m'⟩` with `m' = (e.2 − a − 1).val < k_i − 1`, similarly `j`); `kind_pred` (`(m−1).val = m.val − 1` or `N−1` when `m.val = 0`; then the `if` chains of `mergedKindIdx` and `StrandKind.pred` align, e.g. index `k_i` (arcST) has predecessor `k_i−1` (cutStartS); index `0` (old `⟨i,a+1⟩`) has predecessor `N−1` = cutEndS = `pred (old (s+1))`; old `⟨i,a+1+m⟩`: `⟨i, a+1+m⟩ = ⟨i,a+1⟩ ↔ m = 0` via `Sigma.mk.inj_iff`, `ZMod.natCast_eq_zero_iff`/`val`); `tail_eq` (`mergedTuple` by cases; `StrandKind.tail` is literal); `dir_eq` (`Q (m+1) − Q m` per block: `Q k_i − Q (k_i−1) = s⁻ − P_i a = (τs−ε)•es` by `pt_eq_s`; `Q(k_i+1) − Q k_i = t⁺ − s⁻ = ε(es+et)`; old blocks `P_i(a+2+m) − P_i(a+1+m) = edge` with `push_cast`); `cut_val` (`cutStartS` at `m.val = k_i − 1`, `+2 < N`; `cutStartT` at `k_i+1+k_j`).  Recommended: first prove a 6-lemma `ZMod.val` toolbox (`val_natCast_of_lt`, `val_add_one_of_lt`, `val_sub_one_of_pos`, `val_sub_one_of_zero`, `natCast_val_eq`, `mk_eq_mk_iff_val`). | 250 |
| 3 | `two_le_dd` (1234) | <code>theorem two_le_dd (h : (sS D x).1 = (tS D x).1) : 2 ≤ dd D x</code> | `bS = (t.2.val : ZMod k_i)` equals `h ▸ t.2` by value (`ZMod.natCast_zmod_val` after transporting along `h`); `¬adjacent a bS` from `not_adjacent_sS_tS` via `adjacent_iff`; `two_le_val_sub_of_not_adjacent`. | 30 |
| 4 | `dd_add_two_le` (1237) | <code>theorem dd_add_two_le (h : (sS D x).1 = (tS D x).1) : dd D x + 2 ≤ kI D x</code> | second half of `two_le_val_sub_of_not_adjacent`. | 30 |
| 5 | `card_othersS` (1261) | <code>theorem card_othersS : (othersS D x).card + 1 = D.Γ.c</code> | `Finset.card_erase_of_mem`. | 10 |
| 6 | `selfModel` (1303) | <code>def selfModel (h : (sS D x).1 = (tS D x).1) : SpliceModel D x ε (selfShadow D x ε h)</code> | as `mixedModel` with two nested `Fin.cases` and the tuples `A`, `B`: `kind_pred` at index `0` of `A` (old `⟨i,a+1⟩`, predecessor index `d+1` = cutEndS ✓) and at index `0` of `B` (old `⟨i,bS+1⟩`, predecessor `k−d+1` = cutEndT ✓ since `bS = b` by value and `pred (old (t+1)) = cutEndT`); surjectivity splits old `⟨i,m⟩ ∉ {s,t}` by `(m − a).val ∈ [1, d−1]` ⇒ on `A` at index `(m−a).val − 1`, `∈ [d+1, k−1]` ⇒ on `B` at index `(m−a).val − d − 1`; `cut_val`: `cutStartT` at `d−1` on `A` (size `d+2`), `cutStartS` at `k−d−1` on `B` (size `k−d+2`). | 260 |

### U6-record-bridge — Cyclic-order core (first return, smoothed coordinate `key`/`rkey`, self-case cycle classification), the model-level successor law `succ_of_coord`, and the per-case classification and rotated coordinate (§0' `firstReturn_no_between`, §8).  Internally three sub-lanes: 6a general/D-side (`firstReturn_no_between`, `rkey_*`, `reconnect_no_between`, `self_sameCycle_pair_iff`, `sameCycle_of_comp_ne`, `visitBetween_iff_of_rot_lt_iff`), 6b model-level (`origVisit_*`, `twin/overBit/visitCoord_origVisit`, `compOf_eq_iff_of_cls`, `succ_of_coord`, `oldCls_eq`), 6c per case (`mixed*`, `self*`); 6b/6c only assume 6a's statements  (≈ 1705 lines)

Depends on: U3-model-genericity-crossings, U4-model-outside-arcs, U5-concrete-models.  May assume: every `sorry` statement of the units it depends on, as stated in the skeleton.

| # | lemma (line) | exact statement | proof sketch | est. |
|---|---|---|---|---|
| 1 | `firstReturn_no_between` (175) | <code>theorem firstReturn_no_between {α : Type*} [Fintype α] (f : Equiv.Perm α) (p : α → Prop)<br>    [DecidablePred p] (κ : α → ℝ)<br>    (hκ : ∀ v u, f.SameCycle u v → κ u = κ v → u = v)<br>    (hf : ∀ v u, f.SameCycle u v → ¬ cycBetween (κ v) (κ u) (κ (f v)))<br>    (v : {m // p m}) (u : α) (hu : f.SameCycle u v.1) (hp : p u) :<br>    ¬ cycBetween (κ v.1) (κ u) (κ (firstReturn f p v).1)</code> | set `n := returnTime`; for `0 < j < n`, `¬p (f^j v)` (`returnTime_min`) and `f^j v ≠ v`; claim by induction on `j ≤ n`: `cycBetween (κ v) (κ u) (κ (f^j v)) → ∃ i, 0 < i ∧ i < j ∧ u = f^i v` for `u` on the cycle — step: `w := f^j v`; `hf w v` gives `¬cycBetween (κ w) (κ v) (κ (f w))`, so with distinct keys (`hκ`) `cycBetween (κ v) (κ w) (κ (f w))` (cyclic trichotomy), and the arc from `v` to `f w` is the arc to `w`, `w` itself, and the arc from `w` to `f w` (which contains no cycle element by `hf`); a 12-case `linarith` bash. Apply at `j = n`: `u = f^i v` with `0<i<n` contradicts `hp`. If `f^n v = v`, `not_cycBetween_self_right`. | 150 |
| 2 | `rkey_of_smoothKeep` (1393) | <code>theorem rkey_of_smoothKeep (v : D.Γ.Visit) (hv : D.record.SmoothKeep (xv D x) v) :<br>    rkey D x v = key D x v</code> | `smoothKeep_iff` gives `v ≠ xv`, `v ≠ τxv` (`record_pair_xv`); `Equiv.swap_apply_of_ne_of_ne`. | 15 |
| 3 | `rkey_injOn` (1399) | <code>theorem rkey_injOn (v u : D.Γ.Visit) (hu : (D.record.reconnect (xv D x)).SameCycle u v)<br>    (he : rkey D x u = rkey D x v) : u = v</code> | with `u' := swap u`, `v' := swap v`: equal `key` ⇒ same branch (the branches have disjoint ranges `[0,k_i)` / `[k_i, k_i+k_j)` on the circles of `s`, `t`; on other components a cycle stays on one component by `sameCycle_of_comp_ne`, and `visitCoord_injOn` applies) ⇒ `cyclicOffset` injective on `[0,k)` (`cyclicOffset_of_le/lt`) ⇒ `visitCoord u' = visitCoord v'` with equal `compOf` ⇒ `u' = v'` ⇒ `u = v` (`swap` injective). | 50 |
| 4 | `reconnect_no_between` (1408) | <code>theorem reconnect_no_between (v u : D.Γ.Visit)<br>    (hu : (D.record.reconnect (xv D x)).SameCycle u v) :<br>    ¬ cycBetween (rkey D x v) (rkey D x u) (rkey D x (D.record.reconnect (xv D x) v))</code> | `reconnect_xv_apply`. Case `v ∉ {xv, τxv}`: `s₁ v = succ v`, `rkey v = key v`; if `succ v ∉ {xv,τxv}` then `rkey (succ v) = key (succ v)` and `nextVisit_no_between` transported by `rexPL_rot_eq_cyclicOffset` + `rexB_cycBetween_rot` (on the circle of `s`, base `coord xv`; on the circle of `t` the shift `k_i` is a translation); `u` on the other circle (mixed) cannot be between: `key v, key (succ v)` lie in one block and `key u` in the other, and the only surviving disjunct of `cycBetween` is the wrap `c < a`, which `nextVisit_no_between` at `v` with `u := xv` excludes. If `succ v = xv`: `rkey xv = key τxv` (`= k_i` mixed / `= cyclicOffset (coord xv) (coord τxv)` self) and nothing retained is between `key v` and it (`nextVisit_no_between v xv`). Case `v = xv`: `s₁ xv = succ τxv`, `rkey xv = key τxv`; a retained `u` between would be between `τxv` and `succ τxv` (`nextVisit_no_between` at `τxv`). Case `v = τxv`: symmetric. | 180 |
| 5 | `self_sameCycle_pair_iff` (1432) | <code>theorem self_sameCycle_pair_iff (h : (sS D x).1 = (tS D x).1) (w : D.Γ.Visit)<br>    (hw : D.compOf w = (sS D x).1) :<br>    (D.record.reconnect (xv D x)).SameCycle w (D.underVisit x) ↔<br>      w = D.underVisit x ∨<br>        cycBetween (D.visitCoord (xv D x)) (D.visitCoord w) (D.visitCoord (D.underVisit x))</code> | `→`: the set `W := {w | w = τxv ∨ cycBetween (coord xv) (coord w) (coord τxv)}` is `s₁`-closed (for `w ∈ W`, `w ≠ τxv`: `s₁ w = succ w`; `nextVisit_no_between w τxv` and cyclic trichotomy give `succ w = τxv ∨ cycBetween (coord xv) (coord (succ w)) (coord τxv)`; for `w = τxv`: `s₁ τxv = succ xv`, `nextVisit_no_between xv τxv`), so by `SameCycle.exists_pow_eq'` and induction on the power it contains the `s₁`-cycle of `τxv`. `←`: by `reconnect_sameCycle_or` it suffices to exclude `SameCycle w xv`: the complementary set `W' := {w | w = xv ∨ cycBetween (coord τxv) (coord w) (coord xv)}` is likewise `s₁`-closed and contains `xv`, and `W ∩ W' = ∅` (`cycBetween` asymmetry). | 120 |
| 6 | `sameCycle_of_comp_ne` (1440) | <code>theorem sameCycle_of_comp_ne (v w : D.Γ.Visit) (hv : D.compOf v ≠ (sS D x).1)<br>    (hv' : D.compOf v ≠ (tS D x).1) :<br>    (D.record.reconnect (xv D x)).SameCycle v w ↔ D.compOf v = D.compOf w</code> | `→`: `SameCycle.exists_pow_eq'` gives `w = s₁^n v`; by induction `s₁^n v = succ^n v` (all iterates stay on the component, none is `xv`/`τxv`), then `sameCycle_iff_comp_eq`/`compOf_nextVisit`. `←`: `visitSucc_sameCycle` + `Record.sameCycle_of_eqOn_orbit succ s₁` (`s₁ = succ` on the orbit). | 40 |
| 7 | `visitBetween_iff_of_rot_lt_iff` (1447) | <code>theorem visitBetween_iff_of_rot_lt_iff (D₀ : Diagram) (κ : D₀.Γ.Visit → ℝ) (c₀ : Fin D₀.Γ.c → ℝ)<br>    (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((D₀.Γ.comp l).k : ℝ))<br>    (hlt : ∀ v w, D₀.compOf v = D₀.compOf w →<br>      (rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord v) <<br>        rexB_rot ((D₀.Γ.comp (D₀.compOf v)).k : ℝ) (c₀ (D₀.compOf v)) (D₀.visitCoord w) ↔ κ v < κ w))<br>    (v u w : D₀.Γ.Visit) (hu : D₀.compOf u = D₀.compOf v) (hw : D₀.compOf w = D₀.compOf v) :<br>    D₀.VisitBetween v u w ↔ cycBetween (κ v) (κ u) (κ w)</code> | `VisitBetween` unfolds to `cycBetween` of `visitCoord`s; `rexB_cycBetween_rot` (bounds `visitCoord_nonneg`, `visitCoord_lt`, `hc₀`) rewrites it to `cycBetween` of rotated coordinates; then `cycBetween` is three strict inequalities, each transported by `hlt` (`compOf v = compOf u = compOf w`, so the same `k`, `c₀`). | 40 |
| 8 | `origVisit_injective` (1467) | <code>theorem origVisit_injective : Function.Injective (origVisit D x M hε)</code> | `Sigma.ext`: `origCrossing_injective` on the first components, then `orig_injOn_crossing` on the strands. | 20 |
| 9 | `smoothKeep_origVisit` (1471) | <code>theorem smoothKeep_origVisit (v : Γ₀.Visit) : D.record.SmoothKeep (xv D x) (origVisit D x M hε v)</code> | `smoothKeep_iff`: `(origVisit v).1 = origCrossing v.1 ≠ x` (`origCrossing_ne`), while `xv.1 = τxv.1 = x`. | 15 |
| 10 | `exists_origVisit` (1474) | <code>theorem exists_origVisit (w : D.Γ.Visit) (hw : D.record.SmoothKeep (xv D x) w) :<br>    ∃ v, origVisit D x M hε v = w</code> | `w.1 ≠ x` from `SmoothKeep` (both occurrences of `x` are `xv`, `τxv`: `visit_eq_over_or_under`); lift `y := liftCrossing w.1`, strand `liftStrand w.1 w.2.val w.2.2`; `origCrossing_liftCrossing`, `orig_liftStrand`; `Sigma.ext`. | 40 |
| 11 | `twin_origVisit` (1486) | <code>theorem twin_origVisit (v : Γ₀.Visit) :<br>    D.twin (origVisit D x M hε v) = origVisit D x M hε ((toDiagram D x M hε).twin v)</code> | `twin` takes the other strand; `orig` maps the other strand of `y` to the other strand of `origCrossing y` (`orig_injOn_crossing`, `eq_other_of_mem_of_ne`). | 25 |
| 12 | `overBit_origVisit` (1490) | <code>theorem overBit_origVisit (v : Γ₀.Visit) :<br>    (toDiagram D x M hε).overBit v = D.overBit (origVisit D x M hε v)</code> | `overBit = decide (strand = overStrand)`; `orig_overStrand₀` and `orig_injOn_crossing` transport the equality both ways; `decide_eq_decide`. | 25 |
| 13 | `visitCoord_origVisit` (1501) | <code>theorem visitCoord_origVisit (v : Γ₀.Visit) :<br>    D.visitCoord (origVisit D x M hε v) =<br>      ((M.orig v.2.val).2.val : ℝ) +<br>        (M.kind v.2.val).origParam ε ((toDiagram D x M hε).crossingParam v.1 v.2.2)</code> | `visitCoord_eq` on `D`; `origVisit` has strand `orig v.2.val` and parameter `crossingParam (origCrossing v.1)`; `crossingParam_toDiagram` rewritten as `origParam (param₀) = param_D` (`origParam ∘ liftParam = id`). | 15 |
| 14 | `compOf_eq_iff_of_cls` (1526) | <code>theorem compOf_eq_iff_of_cls (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)<br>    (hcls : Function.Injective cls)<br>    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =<br>      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)<br>    (v w : Γ₀.Visit) :<br>    (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w ↔<br>      (D.record.reconnect (xv D x)).SameCycle (origVisit D x M hε v) (origVisit D x M hε w)</code> | `compOf v = v.2.val.1`; `hcls.eq_iff` turns it into `cls … = cls …`, `hcls_visit` into `smooth.comp _ = smooth.comp _`, `Record.smooth_comp_eq_iff`. | 25 |
| 15 | `succ_of_coord` (1544) | <code>theorem succ_of_coord (cls : Fin Γ₀.c → (D.record.smooth (xv D x)).comps)<br>    (hcls : Function.Injective cls)<br>    (hcls_visit : ∀ v : Γ₀.Visit, cls v.2.val.1 =<br>      (D.record.smooth (xv D x)).comp ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩)<br>    (c₀ : Fin Γ₀.c → ℝ) (hc₀ : ∀ l, 0 ≤ c₀ l ∧ c₀ l < ((Γ₀.comp l).k : ℝ))<br>    (hlt : ∀ v w : Γ₀.Visit, (toDiagram D x M hε).compOf v = (toDiagram D x M hε).compOf w →<br>      (rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord v) <<br>        rexB_rot ((Γ₀.comp v.2.val.1).k : ℝ) (c₀ v.2.val.1) ((toDiagram D x M hε).visitCoord w) ↔<br>        key D x (origVisit D x M hε v) < key D x (origVisit D x M hε w)))<br>    (v : Γ₀.Visit) :<br>    origVisit D x M hε ((toDiagram D x M hε).nextVisit v) =<br>      ((D.record.smooth (xv D x)).succ ⟨origVisit D x M hε v, smoothKeep_origVisit D x M hε v⟩).1</code> | mirror `restrictVisit_nextVisit`. Let `w := origVisit v`, `hw`. If `∀ u, compOf u = compOf v → u = v` then `nextVisit v = v` (`nextVisit_eq_self`) and the first return of `s₁` from `w` to `SmoothKeep` is `w` (its cycle has no other retained element by `compOf_eq_iff_of_cls` + `exists_origVisit`): both sides `w`. Else pick `v'` with `origVisit v' = (smooth.succ ⟨w,hw⟩).1` (`exists_origVisit`, retained by `.2`); `compOf v' = compOf v` (`compOf_eq_iff_of_cls`, `sameCycle_firstReturn_apply`); `v' ≠ v` (else `firstReturn` fixes `w`, so no other retained element is on the cycle: `firstReturn_no_between` with any other retained `u` on the cycle gives `¬cycBetween (κ w) (κ u) (κ w)`… use instead that `smooth.succ` is a permutation whose fixed point `w` would make `u`'s successor chain avoid `w` — simplest: `smoothSucc_no_between` at `u` and at `w` plus cyclic trichotomy); then `cycNext_unique_on (p := fun u => compOf u = compOf v) (k := visitCoord)` with `visitCoord_injOn`, candidates `nextVisit v` (`nextVisit_no_between`, `nextVisit_ne_self`) and `v'` (`smoothSucc_no_between` transported by `visitBetween_iff_of_rot_lt_iff` with `hlt`). | 130 |
| 16 | `oldCls_eq` (1583) | <code>theorem oldCls_eq (i₀ : Fin D.Γ.c) (hi : i₀ ≠ (sS D x).1) (hj : i₀ ≠ (tS D x).1) (w : D.Γ.Visit)<br>    (hw : D.compOf w = i₀) : oldCls D x i₀ = Sum.inl (Quotient.mk _ w)</code> | unfold `oldCls`; the `dif_pos ⟨w, hw⟩` branch; `Quotient.sound`: `Classical.choose h` and `w` are on the same untouched component, hence `s₁`-same-cycle (`sameCycle_of_comp_ne`). | 40 |
| 17 | `mixedBase_mem` (1604) | <code>theorem mixedBase_mem (l : Fin ((othersM D x).card + 1)) :<br>    0 ≤ mixedBase D x l ∧ mixedBase D x l < (((mixedShadow D x ε).comp l).k : ℝ)</code> | `Fin.cases` on `l`: `0 ≤ N − 1 < N` (`Nat.cast_lt`); `0 ≤ 0 < k` (`PolyComp.hk`). | 10 |
| 18 | `mixedCls_bijective` (1609) | <code>theorem mixedCls_bijective : Function.Bijective (mixedCls D x)</code> | injective: `Fin.cases` on both arguments; `inl ⟦xv⟧ ≠ oldCls i₀` (`i₀ ∉ {i,j}`: a same-cycle occurrence would lie on `i₀` by `sameCycle_of_comp_ne`; `inl ≠ inr`); `oldCls i₀ = oldCls i₁ ⇒ i₀ = i₁` (`inl`: `sameCycle_of_comp_ne`; `inr`: `Subtype.ext_iff`); `orderEmbOfFin` injective. surjective: `inl ⟦w⟧`: `compOf w ∈ {i,j}` ⇒ `⟦w⟧ = ⟦xv⟧` (`reconnect_sameCycle_of_mixed`), else `compOf w ∈ othersM` (`Finset.mem_erase`), `l` from `Finset.range_orderEmbOfFin`, `oldCls_eq`; `inr ⟨c,hc⟩`: `c ∉ {i,j}` (they carry `xv`, `τxv`), `oldCls c = inr` (the `dif_neg` branch). | 100 |
| 19 | `mixedCls_visit` (1612) | <code>theorem mixedCls_visit (v : (mixedShadow D x ε).Visit) :<br>    mixedCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp<br>      ⟨origVisit D x (mixedModel D x ε h) hε v, smoothKeep_origVisit D x (mixedModel D x ε h) hε v⟩</code> | `v.2.val.1 = 0`: `origVisit v` lies on `i` or `j` (`orig` of a merged-component strand is `⟨i,·⟩` or `⟨j,·⟩` by the shape of `mergedKindIdx`), so `smooth.comp = inl ⟦origVisit v⟧ = inl ⟦xv⟧` (`reconnect_sameCycle_of_mixed`, `Quotient.sound`); `= l.succ`: `origVisit v` on `emb l ∉ {i,j}`, `oldCls_eq`. | 50 |
| 20 | `mixed_key_lt_iff` (1622) | <code>theorem mixed_key_lt_iff (v w : (mixedShadow D x ε).Visit)<br>    (hc : (toDiagram D x (mixedModel D x ε h) hε).compOf v =<br>      (toDiagram D x (mixedModel D x ε h) hε).compOf w) :<br>    (rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)<br>        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord v) <<br>      rexB_rot (((mixedShadow D x ε).comp v.2.val.1).k : ℝ) (mixedBase D x v.2.val.1)<br>        ((toDiagram D x (mixedModel D x ε h) hε).visitCoord w) ↔<br>      key D x (origVisit D x (mixedModel D x ε h) hε v) <<br>        key D x (origVisit D x (mixedModel D x ε h) hε w))</code> | Shared helpers (prove first, ~20 lines each, also used by U6's self case): `key_of_old_i (w) (hw : w.2.val = ⟨i, a + m⟩) (hm : 1 ≤ m ∧ m ≤ k_i − 1) : key w = m + param w − τs`; `key_of_s_lt (w on s, param < τs) : key w = param − τs + k_i`; `key_of_s_gt (param > τs) : key w = param − τs`; and the `j`-versions with `k_i +`.  Then for `v` on component `0` at label `m` with `θ := param₀ v`: by `mergedKindIdx` cases and `visitCoord_origVisit`, `key (origVisit v) = G(m.val, θ)` with the six affine blocks of the docstring, and `rexB_rot N (N−1) (m.val + θ) = m.val + 1 + θ` for `m.val < N−1`, `= θ` for `m.val = N−1`. Monotonicity: within a block affine with positive slope; across blocks the ranges are increasing in the rotated label (block-end values in the docstring), so a two-level comparison (block index, then `θ`) closes each direction with `linarith`. Components `l.succ`: both sides are the identity (`key = visitCoord` since `emb l ∉ {i,j}`; `origVisit` has the same label and parameter; `rexB_rot k 0 = id` on `[0,k)`). | 200 |
| 21 | `selfBase_mem` (1658) | <code>theorem selfBase_mem (l : Fin ((othersS D x).card + 2)) :<br>    0 ≤ selfBase D x l ∧ selfBase D x l < (((selfShadow D x ε h).comp l).k : ℝ)</code> | `Fin.cases` twice; `dd + 1 < dd + 2`, `k − dd + 1 < k − dd + 2`, `0 < k`. | 15 |
| 22 | `selfCls_bijective` (1663) | <code>theorem selfCls_bijective : Function.Bijective (selfCls D x)</code> | as `mixedCls_bijective` with the two classes `⟦τxv⟧`, `⟦xv⟧` distinct (`smooth_comps_ne_of_self` with `IsSelfCrossing` from `record_isSelfCrossing_iff`) and surjectivity onto occurrences of `i` by `reconnect_sameCycle_or`. | 110 |
| 23 | `selfCls_visit` (1668) | <code>theorem selfCls_visit (v : (selfShadow D x ε h).Visit) :<br>    selfCls D x v.2.val.1 = (D.record.smooth (xv D x)).comp<br>      ⟨origVisit D x (selfModel D x ε h) hε v, smoothKeep_origVisit D x (selfModel D x ε h) hε v⟩</code> | `v` on `A` (component `0`): `origVisit v` is on `⟨i,a+1+m⟩` (`m ≤ d−2`), on `t` before `τt` (cutStartT), or on `s` after `τs` (cutEndS); with the `key_of_*` helpers its `key = cyclicOffset (coord xv) (coord ·)` lies in `(0, d + τt − τs)` = strictly before `τxv` (`key τxv = d + τt − τs`), i.e. `cycBetween (coord xv) (coord (origVisit v)) (coord τxv)` (`rexPL_rot_eq_cyclicOffset`, `rexB_cycBetween_zero`), so `self_sameCycle_pair_iff` gives the class `⟦τxv⟧`. On `B` (component `1`): keys in `(d + τt − τs, k)`, not between, so not same-cycle with `τxv`, hence same-cycle with `xv` (`reconnect_sameCycle_or`). Components `l.succ.succ`: `oldCls_eq`. | 90 |
| 24 | `self_key_lt_iff` (1677) | <code>theorem self_key_lt_iff (v w : (selfShadow D x ε h).Visit)<br>    (hc : (toDiagram D x (selfModel D x ε h) hε).compOf v =<br>      (toDiagram D x (selfModel D x ε h) hε).compOf w) :<br>    (rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)<br>        ((toDiagram D x (selfModel D x ε h) hε).visitCoord v) <<br>      rexB_rot (((selfShadow D x ε h).comp v.2.val.1).k : ℝ) (selfBase D x v.2.val.1)<br>        ((toDiagram D x (selfModel D x ε h) hε).visitCoord w) ↔<br>      key D x (origVisit D x (selfModel D x ε h) hε v) <<br>        key D x (origVisit D x (selfModel D x ε h) hε w))</code> | as `mixed_key_lt_iff` with the blocks of the docstring; on `A` the rotation is by `d+1`, on `B` by `k−d+1`; the `key_of_*` helpers are the same. | 200 |

**Total estimated new proof text: ≈ 5261 lines** on top of the 1761-line skeleton, i.e. ≈ 7022 lines for the lane.  Tag A's 2 950 was optimistic (it omitted the cyclic-order core and under-counted the outside match); tag B's 5 400 counted a 15-field `Small`, the wrap cases the final layout avoids, and a per-descriptor-type shape analysis.

## 4. Existing library lemmas to reuse (file:line, verified 2026-09-13)

LinkDiagram.lean: `Shadow`/`PolyComp` 60-100, `adjacent_mk_iff` 150, `incidentTail_mk_iff` 162,
`IncidentTail.adjacent` 220, `IsCrossing`/`Crossing`/`Visit` 244-260, `crossing_card_two` 284,
`other`/`eq_pair_other`/`mem_iff_eq_or_other`/`eq_other_of_mem_of_ne`/`other_other`/`not_adjacent_other`
315-351, `crossingPoint`/`crossingPoint_mem` 370-378, `Generic` 394, `Generic.common_point_unique` 414,
`Generic.crossingPoint_param` 434, `Generic.crossingPoint_mem_interior` 456,
`Generic.crossingPoint_injective` 463, `Diagram` 490, `underStrand`/`val_eq_pair`/`mem_iff`/
`eq_under_of_mem_of_ne`/`eq_over_of_mem_of_ne`/`not_adjacent_over_under`/`det_over_under_ne_zero`
505-542, `sign` 552, `overVisit`/`underVisit`/`visit_eq_over_or_under` 597-625, `crossingParam`/
`crossingParam_spec/pos/lt_one` 1413-1429, `visitPt`/`visitPt_param`/`eval_visitPt`/`visitPt_injective`
1435-1470, `cyclicOffset` and `cyclicOffset_self/of_le/of_lt/nonneg/lt` 1487-1509.
LinkMoves.lean: `IsDisc`/`isDisc_closedBall` 100-104, `strandOf`/`strandBefore(_of_zero/_of_ne_zero)`
121-136, `Outside` 139, `Arc`/`startPt`/`stopPt`/`Inner`/`Mem`/`Before` 145-200, `IsArc` 213,
`ArcCover` 226, `OuterCrossing`/`outerOverPt`/`outerUnderPt` 265-285, `OverOn`/`UnderOn` 289-292,
`OutsideMatch` 311, `Clean` 336, `LocalFrame` 343, `OrientedSmoothingData` 713, `IsOrientedSmoothing` 743,
`OrientedSmoothingData.card_crossing` 1041, `IsOrientedSmoothing.card_crossing` 1051,
`SmoothingRecordClause` 1128, `Shadow.edge_ne_zero` 1257, `traversalBetween_inner_iff` 2691,
`traversalBetween_total_inner` 2702, `traversalBetween_asymm'` 2717, `Arc.inner_mk_iff` 2727.
LinkRecord.lean: `exists_return`/`returnTime(_pos/_spec/_min/_eq_iff)` 55-70, `firstReturn`/
`firstReturn_apply(_of_mem/_of_not_mem/_of_not_mem₂)` 100-133, `sameCycle_firstReturn_apply` 141,
`firstReturn_sameCycle_of_sameCycle` 179, `mul_swap_apply_of_ne_of_ne/left/right` 202-209,
`mul_swap_sameCycle_left/right` 235-246, `Record` 309, `componentCount` 350, `sameCycle_iff_comp_eq` 376,
`FreeComp` 518, `RecordIso` 539, `RecordIso.componentCount_eq` 613, `reconnect(_apply_*)` 822-834,
`SmoothKeep`/`smoothKeep_iff`/`not_smoothKeep_self/pair` 849-866, `SmoothComps` 880, `smoothSucc` 892,
`smooth` 895, `smooth_comp` 918, `smooth_succ_val` 926, `smooth_comp_eq_iff` 932,
`smooth_succ_val_of_not_mem/…_eq/…_eq'/…_eq_pair/…_eq_pair'` 941-1014, `smoothPairIso` 1040,
`IsSelfCrossing` 1069, `isSelfCrossing_iff_sameCycle` 1074, `reconnect_sameCycle_pair_of_mixed` 1080,
`reconnect_sameCycle_of_mixed` 1086, `reconnect_sameCycle_refines_of_self` 1098,
`smooth_succ_val_of_comp_ne` 1104, `sameCycle_of_eqOn_orbit` 1316.
LinkRecordExtras.lean: `mul_swap_sameCycle_or` 64, `not_mul_swap_sameCycle_of_sameCycle` 76,
`not_reconnect_sameCycle_pair_of_self` 274, `reconnect_sameCycle_or` 280, `smooth_comps_ne_of_self` 285,
`componentCount_smooth(_of_self/_of_mixed)` 316-333, `one_le_componentCount_smooth` 341.
LinkDiagramRecord.lean: `cycBetween` 78, `not_cycBetween_self_right/left/mid` 85-95, `cycNext_unique_on` 102,
`compOf` 164, `visitCoord`/`visitCoord_nonneg`/`visitCoord_lt`/`visitCoord_injOn` 181-189,
`compList`/`nextVisit`/`prevVisit`/`visitSucc` 232-290, `visitSucc_sameCycle` 326,
`nextVisit_no_between` 335, `nextVisit_ne_self` 355, `nextVisit_eq_self(_iff)` 371-392, `twin` 413,
`overBit` 470, `record` and the `record_*` `rfl`-lemmas 500-526, `record_componentCount` 537,
`record_isSelfCrossing_iff` 583, `VisitBetween`/`not_visitBetween_*` 882-899, `ent` enumeration 912-960,
`restrictVisit_nextVisit` 1344 (the template for `succ_of_coord`), `restrictRecordIso` 1454.
LinkRecordExtension.lean: `rexB_rot`/`rexB_unrot`/`rexB_rot_mem`/`rexB_unrot_rot` 53-78,
`rexB_cycBetween_rot` 82, `rexB_cycBetween_of_strictMonoOn` 102, `rexB_cycBetween_zero` 112,
`rexB_pl_strictMonoOn` 274 (optional, for a piecewise-affine `G`), `rexPL_rot_eq_cyclicOffset` 759.
Accepted Chapter-1 library: Polygon.lean `LabelledTuple` 14, `det` 16, `edge` 49, `edgePoint` 51,
`edgeSegment` 54, `edgeInterior` 57, `incident` 60, `adjacent` 63; Segment.lean `det_smul_right` 27,
`det_smul_self` 32, `det_add_right` 36, `intersection_parameter_identity` 47,
`intersection_parameters_unique` 55; EuclideanPlane.lean `det_smul_self` 51, `scalar_of_det_zero` 75;
Crossings.lean `edgePoint_injective` 88; G1Consequences.lean `edgePoint_zero/one`; RegularPairs.lean
`RegularPair` 8, `negativeScalar_iff_dot_det` 11; RegularLocus.lean `Regular` 12, `regular_iff_edges` 18;
Traversal.lean `TraversalPoint` 12, `traversalKey` 17, `traversalKey_injective` 31, `traversalBetween` 73;
SortedCyclicGap.lean `sorted_next_no_cyclic_between` 10.
Mathlib: `Metric.infDist`, `IsClosed.notMem_iff_infDist_pos`, `Metric.infDist_le_dist_of_mem`,
`Finset.inf'`/`lt_inf'_iff`/`inf'_le`, `isCompact_Icc`, `IsCompact.image`, `IsCompact.isClosed`,
`interior_closedBall`, `frontier_closedBall`, `Metric.ball_subset_interior_closedBall`,
`Metric.mem_ball/closedBall/sphere`, `norm_smul`, `dist_eq_norm`, `ZMod.val_natCast`,
`ZMod.natCast_zmod_val`, `ZMod.val_lt`, `ZMod.val_add`, `ZMod.val_add_of_lt`, `ZMod.val_injective`,
`ZMod.natCast_self_eq_zero`, `Fin.cases`/`Fin.cases_zero`/`Fin.cases_succ`, `Finset.orderEmbOfFin`,
`Finset.range_orderEmbOfFin`, `Finset.card_erase_of_mem`, `Equiv.ofBijective(_apply_symm_apply/_symm_apply_apply)`,
`Equiv.subtypeEquivRight`, `Equiv.subtypeUnivEquiv`, `Equiv.swap_apply_of_ne_of_ne`,
`Equiv.Perm.SameCycle.exists_pow_eq'` (Mathlib/GroupTheory/Perm/Cycle/Basic 183), `Quotient.sound`,
`Quotient.exact`, `Fintype.card_congr`, `Fintype.card_subtype_compl`.

## 5. Riskiest steps and fallbacks

1. **`mixed_key_lt_iff` / `self_key_lt_iff` (U6, 400 lines together).**  Risk: the block-by-block
   computation of `key ∘ origVisit` from `mergedKindIdx`/`kindIdxA/B` and the cross-block comparison.
   Mitigation built in: the six `key_of_*` helper lemmas (docstring of `mixed_key_lt_iff`) make each block
   a one-line rewrite, and the rotation puts the blocks in increasing order.  Fallbacks: (a) prove
   `StrictMonoOn G (Ico 0 N)` for the explicit piecewise-affine `G` with `rexB_pl_strictMonoOn`
   (LinkRecordExtension 274) and derive the `lt_iff` from `G (rot coord₀) = key`; (b) if the rotation is
   painful, re-index the concrete tuples to start at the cut-end piece (B's layout) — then `c₀ = 0` but
   `arcTS₀` wraps and `traversalBetween_span_two` needs a wrap variant (`m.val = n − 2`; ~40 lines);
   (c) schedule fallback: ship `exists_smoothing` + `smoothDiagram_componentCount` + `card_crossing`
   first (they do not depend on §8).
2. **`reconnect_no_between` and `self_sameCycle_pair_iff` (U6, 300 lines).**  Risk: the case analysis at
   `xv`, `τ xv` and the mixed-case shift.  The statement has been checked by hand in all three cases
   (§2.4); if a case resists, the fallback is B's (b): prove `succ_of_coord` directly from the five
   explicit successor formulas `Record.smooth_succ_val_of_not_mem/_of_succ_eq/_of_succ_eq'/
   _of_succ_eq_pair/_of_succ_eq_pair'` (LinkRecord 941-1014) with `cycNext_unique_on`, which needs no
   coordinate on the erased occurrences at all.
3. **`mixedModel` / `selfModel` (U5, 510 lines).**  Risk: `ZMod.val` wrap arithmetic (`(m−1).val` at
   `m.val = 0`, `(a+1+m).val`) and `Fin.cases` with a dependent motive on `Sigma` strands.  Fallbacks:
   (a) a 6-lemma `ZMod.val` toolbox first (`val_natCast_of_lt`, `val_add_one_of_lt`,
   `val_sub_one_of_pos`, `val_sub_one_of_zero`, `natCast_val_eq`, `mk_eq_mk_iff_val`), then every field is
   `split_ifs` + `omega`/`simp`; (b) if `Fin.cases` misbehaves, redefine the shadows with
   `comp := fun l => if l.val = 0 then … else …` and the kind map on `(l.val, m.val)` — every statement
   in the skeleton is already on `.val`.
4. **`origPt_bijective` and `arcCover_toDiagram` (U4, 250 lines).**  Risk: classification of traversal
   points by kind and parameter.  The no-wrap law removes the wrap case; the remaining risk is the
   `origParam` range bookkeeping, for which `origParam_mem` and `θ₀_mem` are the two facts to prove first.
5. **`kind_disjoint` / `tail_off` (U3, 220 lines).**  Risk: many kind pairs.  Do all inside-disc
   geometry in the basis `(es, et)` with `coords_unique`, all outside-disc geometry by
   `seg_subset_seg_orig` + `D.generic`, and treat "arc vs anything old" uniformly by
   `seg_arc_subset_ball` + `r₁_le_dist`.

Form (not proof) risk: the relational `smoothing_record` for an arbitrary `D₀` is **not** provable from
the current `OutsideMatch` (no cyclic-order clause on `φ`).  If a consumer needs it, either add a
cyclic-order clause to `OutsideMatch` (then `nextVisit_comm_of_visitBetween_iff`, LinkDiagramRecord
1086, gives it) or prove that an `eval`- and direction-preserving bijection of outside traversal points
preserves `traversalBetween` (a connectedness argument, ≥ 600 lines).  Not planned.

## 6. Notes for the provers

* Never change the fixed definitions in LinkMoves/LinkRecord/LinkDiagramRecord; the skeleton adds only
  `Shadow.Crossing.fst/snd`, the §0' toolbox, `clampIco`, and the `Smoothing` namespace.
* `include`/`omit` discipline: sections `DiscD` (`hε`), `Model` (`M hε`), `RecordBridge` (`M hε`)
  include their variables; definitions that do not need them are `omit … in`.
* Never `unfold`/`show` through `Diagram.record`, `nextVisit`, `compList`: use the `record_*` `rfl`-lemmas,
  `visitCoord_eq`, `record_pair_xv`, `reconnect_xv_apply`, and `have … := rfl` casts (B's warning,
  observed while assembling the isomorphism).  `⟨origVisit v, _⟩ : {w // SmoothKeep xv w}` is only
  defeq to an element of `(smooth xv).M`; `rw` with `Record.smooth_*` lemmas may fail at instance
  transparency — state the needed equation with `rfl` first.
* The over/under choice fixes `s = overStrand x`; `Record.smoothPairIso` handles the other occurrence.
* `toDiagram_sign` gives `sign₀ y = sign (origCrossing y)`, so `writhe` transport is free for consumers.
* Times: report progress with both UTC and New York time.

## §5 addendum (executor, 2026-09-13 ~22:52Z) — false chain lemma found by U1

`seg_arc_subset_ball` (skeleton line 1097) is FALSE as stated: `Plane = ℝ × ℝ` carries the sup norm, so the
arc can lie entirely on the sphere of radius `ε · max(‖es‖, ‖et‖)` (counterexample es = (1,0), et = (−1, 1/2),
recorded in U1_clearance.lean's docstring). U1 proved the correct form `seg_arc_subset_closedBall` (same
hypotheses, `Metric.closedBall`). ASSEMBLY RULE: every use of `seg_arc_subset_ball` (U2's arc lemmas, U6b's
`kind_ne_arc_of_mem`, any U3/U4 use) must be replaced by `seg_arc_subset_closedBall` followed by
`Metric.closedBall_subset_ball (arc_lt_discRadius …)` (strict inequality `ε · max < discRadius`); the false
lemma is dropped from the assembled module.
