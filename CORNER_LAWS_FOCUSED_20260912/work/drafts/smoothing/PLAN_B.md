# PLAN_B — oriented smoothing: `exists_smoothing` and `smoothing_record` (tag B)

Written 2026-09-13. Companion skeleton: `work/drafts/smoothing/Skeleton_B.lean` (1264 lines,
typechecks with `lake env lean`, 120 `sorry`-lemmas, every definition real). Design emphasis of
this tag: proofs as easy as possible at the cost of longer definitions.

## 0. What is delivered and in which exact form

Fixed (not touched): `OrientedSmoothingData`/`IsOrientedSmoothing` (LinkMoves.lean 713-744),
`OutsideMatch`/`Clean`/`LocalFrame` (316-352), `Arc`/`IsArc`/`ArcCover` (145-235),
`Record.smooth` (LinkRecord.lean 895-916), `Diagram.record` (LinkDiagramRecord.lean 500).

Goal theorems (all in the skeleton, §8, proved from the chain with `sorry` only inside chain
lemmas):

```
theorem exists_smoothing (D : Diagram) (x : D.Γ.Crossing) : ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀
theorem smoothing_record (D : Diagram) (x : D.Γ.Crossing) :
    ∃ D₀ : Diagram, IsOrientedSmoothing D x D₀ ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x)))
theorem smoothing_record_clause (D x) : ∃ D₀, IsOrientedSmoothing D x D₀ ∧
      SmoothingRecordClause Diagram.record (fun _ v => v) D x D₀          -- LinkMoves.lean 1128
theorem exists_smoothing_with_counts (D x) : ∃ D₀, IsOrientedSmoothing D x D₀ ∧
      Fintype.card D₀.Γ.Crossing + 1 = Fintype.card D.Γ.Crossing ∧
      D₀.componentCount = (if (D.overStrand x).1 = (D.underStrand x).1 then c + 1 else c - 1) ∧
      Nonempty (RecordIso D₀.record (D.record.smooth (D.overVisit x)))
```
plus, for the constructed diagram `D.smoothDiagram x ε r h`: `smoothRecordIso` (a `def`, the
actual isomorphism), `smoothDiagram_componentCount`, `smoothDiagram_card_crossing`,
`isOrientedSmoothing_smoothDiagram`.

**Form of `smoothing_record`.** The occurrence `v` of `x` is the over occurrence `D.overVisit x`
(the design's `toM D (D.overVisit x)`; `Record.smoothPairIso` (LinkRecord 1040) converts to the
under occurrence). The theorem is stated for *the constructed* smoothing (∃ D₀ with both
properties), which is what the `(N, b)` inductions of rp:record-polynomial and lp:core use
("The resulting actual smoothed diagrams thus have isomorphic decorated records", sm-3:1256-1258;
"New orders and basepoints can be chosen because the first complexity coordinate has decreased",
sm-3:1102-1103). The *relational* version `IsOrientedSmoothing D x D₀ → RecordIso …` for an
arbitrary `D₀` is **not provable from the current `OutsideMatch`**: its `φ` preserves traced points
and directions but carries no cyclic-order clause, so successor preservation for the outside
occurrences cannot be extracted without a continuity argument along traversal intervals. Recorded
as an open item (§6, risk 4); consumers do not need it.

## 1. The construction

Notation (all in namespace `SM.Link.Diagram`, prefix `smB_`): `o := D.overStrand x`,
`u := D.underStrand x`, `τo := D.crossingParam x (over_mem)`, `τu`, `P₀ := crossingPoint x`,
`do := dir o`, `du := dir u`, `vo := D.overVisit x`, `vu := D.underVisit x`,
`Γ.edgePt s t := edgePoint (Γ.comp s.1).P s.2 t` (any real `t`).

### 1.1 Cut points and the disc
`om := edgePt o (τo-ε)`, `op := edgePt o (τo+ε)`, `um := edgePt u (τu-ε)`, `up := edgePt u (τu+ε)`.
In the basis `(do, du)` centred at `P₀`: `om = P₀ - ε do`, `op = P₀ + ε do`, `um = P₀ - ε du`,
`up = P₀ + ε du`; the two smoothing segments are `n1 = om → up` (direction `ε(do+du)`) and
`n2 = um → op` (direction `ε(do+du)`, parallel to `n1`). Disc `U := closedBall P₀ r` (sup metric of
`Plane = ℝ×ℝ`, an axis-parallel square; `isDisc_closedBall`, LinkMoves 104).

### 1.2 The smallness hypotheses `Small D x ε r` (structure, skeleton §1) and the finite sets avoided
* `0 < ε < min(τo, 1-τo, τu, 1-τu)` — the cut points are interior to their edges.
* `ε < |crossingParam w - τo|` for every other occurrence `w` on `o` (and likewise on `u`) —
  avoids the finite set of other double points on `o`, `u`, so each lies strictly inside one
  half-edge and never at a cut point (`ε_vis_o`, `ε_vis_u`).
* `0 < r`, `ε‖do‖ < r`, `ε‖du‖ < r` — cut points strictly inside the open disc.
* `r < τo‖do‖`, `r < (1-τo)‖do‖`, same for `u` — the disc does not reach the four edge ends, so
  the disc cuts `o` and `u` in exactly two points each (`dist_edgePt`: `dist (edgePt o t) P₀ =
  |t-τo|·‖do‖`).
* `r_seg : ∀ t ∉ {o,u}, ∀ q ∈ seg t, r < dist q P₀` — the closed disc misses every other edge
  (finitely many compact segments not containing `P₀`, L0.2). Consequences: every vertex is
  outside the disc (vertices of `o`, `u` by the previous item; others lie on some other edge),
  every double point `y ≠ x` is outside (one strand of `y` is not in `{o,u}`), and
  `D ∩ U = (seg o ∪ seg u) ∩ U` — the clean disc.
Existence (`exists_small`): `r := ½·min(τo‖do‖, (1-τo)‖do‖, τu‖du‖, (1-τu)‖du‖, min_t δ_t)` with
`δ_t` from `IsCompact.exists_isMinOn` on `seg t`; then `ε := ½·min(τo, 1-τo, τu, 1-τu,
r/‖do‖, r/‖du‖, min_w |param w - τ|)` (finite minima over `Finset.univ` of strands/visits).

### 1.3 Vertex descriptors and the new components
`SmVert Γ := old (s : Γ.Strand) | om | op | um | up` (an old vertex is named by the strand whose
tail it is; `smB_evalVert : SmVert → Plane`). A new component is a `DescrComp := (k, 3 ≤ k,
d : ZMod k → SmVert)` and its polygon is `⟨k, hk, evalVert ∘ d⟩`. Every edge of the new shadow is a
consecutive descriptor pair, of one of **seven kinds** `SmKind := old d | hOm | hOp | hUm | hUp |
n1 | n2` (`smB_classify`): `(old d, old d')` (an old edge `d`), `(old (tail o), om) = hOm`
(the half-edge `P(ao) → om`), `(op, old (ao+1)) = hOp`, `(old (tail u), um) = hUm`,
`(up, old (au+1)) = hUp`, `(om, up) = n1`, `(um, op) = n2`.

**Self-crossing case** (`h : o.1 = u.1`, component `i` with `k` vertices, `ao := o.2`,
`au := smB_au h : ZMod k` = `u.2` transported by `cast`, the only dependent-type transport in the
file). `nA := (au - ao).val`, `nB := (ao - au).val`; by non-adjacency (L0.5) `2 ≤ nA, nB ≤ k-2`
and `nA + nB = k`. One component of `k` vertices splits into two:
* `A` (the SM's `(y A)`), `k_A = nA + 2`:
  `d j = if j.val = 0 then op else if j.val = nA+1 then um else old ⟨i, ao + (j.val : ZMod k)⟩`
  — vertices `op, P(ao+1), …, P(au), um`; edges by label: `0 = hOp`, `1…nA-1 = old (ao+m)`,
  `nA = hUm`, `nA+1 = n2`.
* `B` (the SM's `(x B)`), `k_B = nB + 2`: `up, P(au+1), …, P(ao), om`; edges `0 = hUp`,
  `1…nB-1 = old (au+m)`, `nB = hOm`, `nB+1 = n1`.
Orientation check: along `A` we arrive at `um` on `u`'s incoming end and leave along `n2` to `op`,
`o`'s outgoing end — "each incoming strand to the other strand's outgoing end" (sm-3:1084).

**Mixed case** (`o.1 ≠ u.1`, `ko`, `ku` vertices): two components join into one `M` with
`ko + ku + 4` vertices: `op, P_o(ao+1), …, P_o(ao), om, up, P_u(au+1), …, P_u(au), um`; edges
`0 = hOp`, `1…ko-1 = old ⟨o.1, ao+m⟩`, `ko = hOm`, `ko+1 = n1`, `ko+2 = hUp`,
`ko+3…ko+ku+1 = old ⟨u.1, au+(m-ko-2)⟩`, `ko+ku+2 = hUm`, `ko+ku+3 = n2`.

**Untouched components**: `smB_descrOld i : d j = old ⟨i, j⟩` (same labels, same polygon).

**ZMod index handling.** All descriptor sequences are `if … then … else` on `j.val : ℕ`; old
vertices are named `⟨i, base + (m : ZMod k)⟩` with a *natural* offset cast into `ZMod k`
(`ZMod.val_natCast`, `ZMod.natCast_zmod_val`, `ZMod.val_add_of_lt`), never with a
transport. The successor label `j+1` is handled by `ZMod.val_add_of_lt` (no wrap) and
`(j+1).val = 0` when `j.val = k-1` (wrap: the last edge `n1`/`n2`/last old edge). Positions of
special strands are natural labels `smB_lOm, smB_lN1, smB_lUp` (in component `jO`) and
`0, smB_lUm, smB_lN2` (in `jU`), built into strands with `smB_mk j (m : ℕ) := ⟨j, (m : ZMod _)⟩`.
The inverse position map `smB_ofD d` for an old strand `d ∉ {o,u}` is explicit:
`⟨jU, ((d.2 - ao).val)⟩` if `1 ≤ (d.2-ao).val < nA` (self, on `A`), `⟨jO, (d.2-au).val⟩` (self,
on `B`), `⟨jO, (d.2-ao).val⟩` / `⟨jO, ko+2+(d.2-au).val⟩` (mixed), `⟨idx (compIdxOld d.1), d.2.val⟩`
(untouched).

### 1.4 Component indexing by the smoothed record
`smB_Comps := (D.record.smooth vo).comps = Quotient (SameCycle.setoid s₁) ⊕ D.record.FreeComp`,
`s₁ := D.record.reconnect vo = visitSucc * swap vo vu` (LinkRecord 822). `c' := Fintype.card
smB_Comps ≥ 1` (`Record.one_le_componentCount_smooth`, LinkRecordExtras 341);
`smB_idx : smB_Comps ≃ Fin c'` is `Fintype.equivFin`. The descriptor of a component:
`Sum.inr f ↦ descrOld f.1` (crossing-free circle of `D`); `Sum.inl q ↦` by `q.out`:
`s₁.SameCycle q.out vo → (self: B | mixed: M)`, `s₁.SameCycle q.out vu → (self: A | mixed: M)`,
otherwise `descrOld (compOf q.out)`. Hence `jO := idx (inl ⟦vo⟧)`, `jU := idx (inl ⟦vu⟧)` (equal in
the mixed case), and **`e := smB_idx.symm` is the component bijection of the record isomorphism,
definitionally**. The reading of sm-3:1090-1096 is literal: the cycle of `s₁` through `vu` is
`(y A)` and carries the old vertices `P(ao+1)…P(au)`, the cycle through `vo` is `(x B)`; in the
mixed case the single cycle `(x B y A)` carries both vertex runs.

### 1.5 The smoothed shadow and diagram
`smoothShadow D x ε := ⟨c', _, fun j => (compDescr (idx.symm j)).toPoly (evalVert ε)⟩` (no
hypothesis needed). `smB_kind s := classify (d s.2) (d (s.2+1))`, `smB_toD s` (underlying strand
of `D`; junk `o` on `n1`,`n2`), `smB_toParam s t` (affine rescaling: `hOm: t(τo-ε)`,
`hOp: τo+ε+t(1-τo-ε)`, …), `smB_dirScale`. Over data: `smB_toDCrossing y := ⟨{toD s, toD t}, _⟩`
for the two strands of `y` (`dite`, junk `x`), `smB_over y := if toD s = D.overStrand (toDCrossing y)
then s else t`. `smoothDiagram D x ε r (h : Small) := ⟨smoothShadow, smoothShadow_generic h,
smB_over, smB_over_mem⟩`. Because the over data is *defined* through `toD`, the bit and sign clauses
of the record isomorphism reduce to the crossing correspondence (§4).

### 1.6 The record isomorphism (§5-§6 of the skeleton)
`Φ := smB_visitEquiv : D₀.Visit ≃ {v // SmoothKeep vo v}`, `Φ ⟨y, s⟩ = ⟨toDCrossing y, toD s⟩`.
Clauses: `comp_eq` from L5.1; `pair_eq` from `twin ↦ twin` (the other strand maps to the other
strand); `bit_eq`, `sgn_eq` from `smB_toD_over` and positivity of `dirScale`; `succ_eq` from the
cyclic-order bridge: the smoothed coordinate `smB_off v` (offset of `visitCoord v` from
`visitCoord vo` on `o`'s circle; `ko +` offset from `vu` on `u`'s circle; `visitCoord v` elsewhere)
is (i) a strictly increasing function of `D₀.visitCoord` on each new component (L5.2a) and (ii) a
cyclic-successor coordinate for `s₁` on each of its cycles (L5.4a); the first return of a
cyclic-successor permutation is the cyclic successor within the retained set (L5.4b, general);
`cycNext_unique_on` (LinkDiagramRecord 102) then identifies `D₀.nextVisit` with `(smooth).succ`.

### 1.7 The oriented-smoothing data (§7)
`φ` = `smB_ofDPt` (same parameter on old edges; rescaled parameter on the half-edges, chosen by
`param < τ`) with inverse `smB_toDPt`; `ψ` = the crossing bijection restricted (all `y ≠ x` are
outer for `D`, all crossings of `D₀` are outer). Arcs: `a := (o, τo-ρo, τo+ρo)`, `ρo := r/‖do‖`,
`b` likewise; `a₀ := (jO, (lOm, (τo-ρo)/(τo-ε)), (lUp, (ρu-ε)/(1-τu-ε)))` runs `hOm → om → n1 → up
→ hUp`, `b₀ := (jU, (lUm, …), (0, …))` runs `hUm → um → n2 → op → hOp`. Cleanliness: the trace
meets `∂U` in exactly the four points `edgePt o (τo±ρo)`, `edgePt u (τu±ρu)`, each on exactly one
edge (clean disc + `seg o ∩ seg u = {P₀}`), hence traversed once; every component has a vertex,
all vertices are outside `U`.

## 2. Lemma chain: statements, sketches, sizes (dependency order = file order)

Sizes are estimated proof lines. "Skeleton" = statement already in `Skeleton_B.lean`.

### §0 Generic-shadow preliminaries (reusable; ~230 lines)
| lemma | statement (short) | sketch | lines |
|---|---|---|---|
| `Shadow.dist_edgePt` | `dist (edgePt s t) (edgePt s t') = |t-t'|·‖dir s‖` | `edgePt_eq`, `dist_eq_norm`, `sub_smul`, `norm_smul` | 10 |
| `Generic.adjacent_seg_inter` (L0.1) | `seg ⟨i,a⟩ ∩ seg ⟨i,a+1⟩ = {tail ⟨i,a+1⟩}` | `q = P a + s e_a = P(a+1) + t e_{a+1}` ⇒ `(s-1) e_a = t e_{a+1}`; if `det ≠ 0` then `s=1, t=0` (`coords_unique`); else `e_{a+1} = ρ e_a`, `ρ > 0` by `Regular` (`negativeScalar_iff_dot_det`, RegularPairs 12) and `s-1 = tρ ≤ 0 ≤ …` forces `t = 0` | 45 |
| `Generic.crossingPoint_not_mem_seg` (L0.2) | `t ∉ x.val → P₀ ∉ seg t` | `P₀ = edgePt t θ`; `θ ∈ (0,1)`: triple point with `o,u` (`crossingPoint_mem_interior`, LinkDiagram 456) vs `no_triple`; `θ = 0`: `tail t ∈ seg o` ⇒ `IncidentTail t o` (`tail_off`) ⇒ `tail t ∈ {P(ao), P(ao+1)}` ⇒ `τo ∈ {0,1}` by `edgePoint_injective` (Crossings 88), contradicting `crossingParam_pos/lt_one`; `θ = 1`: same with `tail ⟨t.1, t.2+1⟩` | 50 |
| `Generic.crossingPoint_ne_tail` (L0.3) | `P₀ ≠ tail s` | if `s ∈ x.val`: parameter injectivity; else L0.2 with `tail_mem_seg` | 15 |
| `Generic.seg_inter_seg_eq` (L0.7) | `s,t ∈ x.val, s ≠ t → seg s ∩ seg t = {P₀}` | `common_point_unique` (LinkDiagram 414) | 12 |
| `Generic.edgePt_injective` | | `edgePoint_injective` + `regular_iff_edges` | 8 |
| `two_le_val_sub_of_not_adjacent` (L0.5) | `¬adjacent a b → 2 ≤ (b-a).val ∧ (b-a).val + 2 ≤ k` | `(b-a).val ∈ {0,1,k-1}` iff `b - a ∈ {0,1,-1}` (`ZMod.val_eq_zero`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`) | 30 |
| `coords_unique` (L0.6) | `α do + β du = α' do + β' du → α=α' ∧ β=β'` | rewrite as `a + s•u = b + t•v` with `a = b = 0` and apply `intersection_parameters_unique` (Segment 55) | 12 |
| `regularPair_smul_pos`, `regularPair_of_det_ne_zero`, `regularPair_add_right/left_of_det_ne_zero` | | unfold `RegularPair`; a negative multiple would give `det = 0` (`det_smul_self`, `det_add_right`, Segment 32-36) | 4×12 |

### §1 Local data and `Small` (~420 lines)
| lemma | sketch | lines |
|---|---|---|
| `smB_om_eq`…`smB_up_eq` | `edgePt_eq`, `smB_P₀_eq_o`, `add_smul`, `sub_eq_add_neg` | 4×8 |
| `smB_exists_pos_dist_seg` | `seg t` compact (`edgeSegment` = continuous image of `Icc 0 1`: `isCompact_Icc.image`), nonempty; `IsCompact.exists_isMinOn` for `dist · P₀`; min `> 0` since `P₀ ∉ seg t`; take `δ := min/2` | 40 |
| `exists_small` (L1.1) | finite minima with `Finset.exists_min_image`/`Finset.inf'` over `Finset.univ` of `D.Γ.Strand` (Fintype) and `D.Γ.Visit`; positivity of each term (`crossingParam_pos`, `visitPt_injective` for `param w ≠ τo` when `w ≠ vo`, `norm_pos_iff`); assemble the 15 fields | 150 |
| `Small.om_mem_interior` … (4) | parameters in `(0,1)` | 4×8 |
| `Small.dist_om`, `Small.*_mem_ball` (4) | `dist_edgePt` + `εdo_lt_r` | 5×8 |
| `Small.om_ne_P₀`, `Small.om_not_mem_seg_u` | `edgePt_injective`; `om ∈ seg o ∩ seg u = {P₀}` (L0.7) | 2×12 |
| `Small.seg_disjoint_ball`, `tail_not_mem_ball`, `crossingPoint_not_mem_ball` (L1.3) | `r_seg`; a vertex lies on an incident edge (`tail_mem_seg`), on `o`,`u` use `dist_edgePt` and `r_lt_o`; a double point `y ≠ x` lies on a strand `∉ {o,u}` | 15+25+25 |
| `Small.edgePt_o_mem_ball_iff`, `_u_` | `dist_edgePt` | 2×8 |
| `Small.newSeg_disjoint` (L1.4) | points `P₀ + ε(-(1-t) do + t du)` and `P₀ + ε(s do - (1-s) du)`; `coords_unique` ⇒ `t-1 = s ∧ t = s-1` ⇒ `2 = 0` | 35 |
| `Small.newSeg₁_inter_o/u`, `newSeg₂_inter_o/u` | same coordinates against `P₀ + λ do` (resp. `λ du`): the `du`-coefficient `εt = 0` forces `t = 0`, i.e. the endpoint | 4×25 |
| `Small.newSeg₁/₂_subset_ball` (L1.5) | `convex_ball`, `Convex.segment_subset`, endpoints in the ball | 2×10 |

### §2 Shape, kinds, positions (~900 lines) — the combinatorial core
| lemma | sketch | lines |
|---|---|---|
| `smB_u_eq`, `smB_two_le_nA/nB`, `smB_nA_add_nB` | `Sigma.ext` + `cast_heq`; L0.5 applied to `¬adjacent ao au` (`not_adjacent_over_under`, LinkDiagram 531, via `adjacent_mk_iff`); `(a-b).val + (b-a).val = k` for `a ≠ b` (`ZMod.val_add`, `neg`) | 20+40+25 |
| `smB_adjacent_iff` | unfold `Adjacent`, `adjacent_mk_iff`; `b - a ∈ {-1,0,1}` ⟺ `s = t ∨ next s = t ∨ next t = s` (`Sigma.ext`) | 30 |
| `smB_kind_next` (L2.1) | case on `idx.symm s.1` (the four descriptor types); for each, case on `j.val` position (`0`, middle, last two, wrap `j.val = k-1`), compute `(j+1).val` with `ZMod.val_add_of_lt`/`val_add`; the old-old case needs `⟨i, ao + (m+1)⟩ = ⟨i, ao+m⟩.next` and the two "hit `o` or `u`" tests (`ao + nA = au`, `au + nB = ao`) | 220 |
| `smB_kind_old_ne` | in every descriptor the old vertex run never has `o` (resp. `u`) as an *edge*: for `A` the run `ao+1…au` produces edges `ao+1…au-1`; `ao+m = ao` iff `m ≡ 0`, `= au` iff `m ≡ nA` — excluded by the position bounds | 50 |
| `smB_kind_injective` (L2.3) | two strands with equal kind: same descriptor type (each special kind appears in exactly one type; old kind `d` determines the component index through `d.1`, `compIdxOld` and, for `d.1 ∈ {o.1,u.1}`, the `A`/`B` range test), then equal labels by injectivity of `m ↦ ao + m` on `[1, nA)` (`ZMod.val` arithmetic) | 130 |
| `smB_kind_hOm` … `smB_kind_n2` (6) | unfold `smB_mk`, `smB_lOm` etc.; `ZMod.val_natCast` with the bound `< k`; evaluate the `if`s | 6×20 |
| `smB_kind_ofD` (L2.4) | case split as in `smB_ofD`; `compDescr (compIdxOld i) = descrOld i` needs: `q.out` for `q = ⟦h.choose⟧` is `s₁`-same-cycle to a visit of component `i ∉ {o.1,u.1}` (`Quotient.mk_out`), hence not same-cycle to `vo`, `vu` (`Record.sameCycle_of_eqOn_orbit`, LinkRecord 1316: `s₁` agrees with `succ` on that cycle; or LinkRecordExtras `reconnect_sameCycle_or` 280); `compOf q.out = i` by `comp_pow`-type transport | 110 |
| `smB_strand_cases` | from `smB_kind_next` iterated / directly from the descriptor position: `kind s = old d ⇒ s = ofD d` (injectivity + `smB_kind_ofD`), else one of six | 60 |
| `smB_toD_ofD` | rewrite `smB_kind_ofD` | 10 |
| `smB_seg_eq`, `smB_dir_eq` (L2.2) | `seg ⟨j,m⟩ = edgeSegment` between `evalVert (d m)` and `evalVert (d (m+1))`; by `smB_kind_next`-style position case, the pair is one of seven with known evaluations; `edgeSegment` of `P(ao) → om` is `edgePt o '' Icc 0 (τo-ε)` (`edgePoint` reparametrisation `edgePt o (t(τo-ε))`) ; `n1`: `edgeSegment = segment ℝ om up` (`segment_eq_image`) | 90+50 |
| `smB_edgePt_eq`, `smB_dir_eq_scale`, `smB_dirScale_pos` | unfold `toParam`, `dirScale`; `smB_om_eq` etc.; positivity from `Small` | 30+25+15 |

### §3 Genericity (~620 lines)
| lemma | sketch | lines |
|---|---|---|
| `smB_regular` (L3.1) | `Regular P ↔ ∀ i, RegularPair (edge (i-1)) (edge i)` (`regular_iff_edges`); consecutive pair = `(kind s, nextKind (kind s))` by `smB_kind_next`; seven cases: old–old ⇒ `D.generic.regular`; old–`hOm`, `hUp`–old, … ⇒ `regularPair_smul_pos` of an old pair; `hOm`–`n1`: `((τo-ε) do, ε(do+du))` ⇒ `regularPair_add_right_of_det_ne_zero`; `n1`–`hUp`: `(ε(do+du), (1-τu-ε) du)` ⇒ `…_add_left…`; likewise `hUm`–`n2`, `n2`–`hOp` | 130 |
| `smB_tail_off` (L3.2) | `tail s = evalVert (d s.2)`: (a) old vertex `V`: if `kind t = old d'` use `D.generic.tail_off` (incidence transported by `smB_kind_next`/`smB_adjacent_iff`: `IncidentTail s t` in `Γ₀` ⟺ `t ∈ {s, prev s}`); `t` a half-edge ⊆ `seg o`: `V ∈ seg o` ⇒ `V ∈ {P(ao), P(ao+1)}` (`tail_off`) and these are ends of the *other* half-edge only (parameters); `t ∈ {n1,n2}`: `V ∉ ball` (`tail_not_mem_ball`) but `seg n1 ⊆ ball`; (b) cut point (say `om`): `t` old ⇒ `om ∈ ball`, `seg t ∩ U = ∅`; `t` a half-edge of `u` ⇒ `om ∈ seg u`, contra `om_not_mem_seg_u`; `t = hOp` ⇒ parameter `τo-ε ∉ [τo+ε,1]`; `t = hOm` ⇒ incident; `t = n1` ⇒ incident; `t = n2` ⇒ `newSeg₂_inter_o` gives `om = op`, contra | 190 |
| `smB_transverse` (L3.3) | classify `(kind s, kind t)`: old–old: `D.generic.transverse` (non-adjacent in `Γ₀` ⇒ non-adjacent in `D`: consecutive old edges stay consecutive, §1.3); old–half-edge `h ⊆ seg o`: if `d` non-adjacent to `o` in `D` then `det (dir d) (dir o) ≠ 0` and `dir h = l·dir o`; if `d = o±1` then `seg d ∩ seg o = {vertex}` (L0.1) and the vertex is not on `h` unless `h` is the adjacent half-edge (then `Adjacent` in `Γ₀`, excluded); old–`n`: no meeting (ball); half–half: `seg o ∩ seg u = {P₀}` not on any half-edge; two half-edges of `o` are parameter-disjoint; half–`n`: only the shared endpoint, which makes them adjacent; `n1`–`n2`: disjoint | 170 |
| `smB_no_triple` (L3.4) | common interior point `q`: if some strand is old, `q ∉ ball`, so all three are old or half-edges; map by `toD` to `D`: distinct unless two are half-edges of one strand, whose interiors are disjoint; then `D.generic.no_triple`; if all three are half-edges/`n`: pigeonhole on `{o,u}` or `interior n1 ∩ (half-edges) = ∅` | 130 |

### §4 Crossings and occurrences (~880 lines)
| lemma | sketch | lines |
|---|---|---|
| `smB_crossing_kind_ne_n1/n2` (L4.1) | a crossing `{n1, t}` needs a meeting with a non-adjacent `t`: `t` old ⇒ ball; `t` half ⇒ only endpoints (adjacent); `t = n2` ⇒ disjoint | 2×40 |
| `smB_toD_isCrossing` | `toD s`, `toD t` non-adjacent in `D` (else by L0.1 the meeting is at a vertex, which lies on no half-edge; or `s`,`t` adjacent in `Γ₀`) and meet (`seg s ⊆ seg (toD s)`) | 80 |
| `smB_toD_mem`, `smB_toDCrossing_ne`, `smB_toDCrossing_val`, `smB_toDCrossing_injective` | unfold the `dite` with `smB_toD_isCrossing`; `≠ x`: `{toD s, toD t} = {o,u}` would put the common point at `P₀`, which is on no half-edge; injectivity from `smB_kind_injective` + `toD` injective on non-`n` kinds up to the `hOm/hOp` (resp. `hUm/hUp`) ambiguity, resolved by the position of the double point (`ε_vis_o`) | 25+30+25+60 |
| `smB_crossingPoint_eq` | `common_point_unique` for `D₀` (generic) applied to `crossingPoint (toDCrossing y)`, which lies on both `seg s` (parameter `toParam`) | 40 |
| `smB_ofD_isCrossing` (L4.2) | the two lifted strands are non-adjacent (kinds differ; adjacency of kinds is listed by `smB_kind_next`) and meet at `crossingPoint y` (the half-edge is chosen by `param < τo`, and `ε_vis_o` puts the parameter inside the half-edge range) | 110 |
| `smB_toD_ofDCrossing`, `smB_ofD_toDCrossing` | `Subtype.ext`, `Finset` pair equality, `smB_toD_ofD`, `smB_kind_hOm`… and the half-edge selection consistent with `smB_crossingParam_eq` | 60+70 |
| `smB_toD_over`, `smB_toD_under` (L4.3) | unfold `smB_over`; `toD s = overStrand ∨ toD t = overStrand` since `{toD s, toD t} = (toDCrossing y).val`; `toD s ≠ toD t` | 40+20 |
| `smB_crossingParam_eq` (L4.5) | both sides give the same plane point (`smB_edgePt_eq`, `smB_crossingPoint_eq`); `edgePt_injective` | 50 |
| `smB_sign_eq` (L4.6) | `smB_dir_eq_scale` on over and under, `det_smul_left/right`, `sign_mul`, `sign_pos` of `dirScale` | 40 |
| `smB_toDVisit_keep/injective/surjective` (L4.4) | `≠ vo, vu` from `toDCrossing y ≠ x`; injectivity from crossing injectivity and `toD` injective on the two strands of one crossing; surjectivity from `smB_ofDCrossing` and `smB_ofDStrandAt` | 20+40+60 |
| `smB_toDVisit_twin`, `smB_overBit_eq` | `other` transports (`eq_other_of_mem_of_ne`, LinkDiagram 340) via `toD` injective on `y.val`; `overBit = decide (s = over)` both sides, `smB_toD_over` + injectivity | 50+40 |

### §5 Components and cyclic order (~1050 lines) — the record heart
| lemma | sketch | lines |
|---|---|---|
| `smB_compOf_eq` (L5.1) | `compOf w = w.strand.1 = j`; show `idx.symm j = inl ⟦toDVisit w⟧`, i.e. `compDescr (idx.symm j)` is the descriptor whose old-vertex run contains the occurrence: by `smB_strand_cases`; for `s = ofD d` with `d.1 ∉ {o.1,u.1}`: `idx.symm j = compIdxOld d.1 = inl ⟦v'⟧` with `v'` on component `d.1`, and `s₁.SameCycle v' (toDVisit w)` since both are on the untouched cycle (`succ_cycle` + `sameCycle_of_eqOn_orbit`); for `s` on `A` (self): `toDVisit w` is a visit on `⟨i, ao+m⟩` with `1 ≤ m < nA` or on `hOp`/`hUm`, i.e. `cycBetween κ(vo) κ(v) κ(vu)`, and such `v` are exactly the `s₁`-cycle of `vu` (induction along `succ` from `vo`: `s₁ = succ` on the `A`-word, `s₁ vu = succ vo`); `B`, `M` likewise (mixed: `reconnect_sameCycle_of_mixed`, LinkRecord 1086 — every visit of the two components is on the merged cycle) | 220 |
| `smB_exists_monotone_coord` (L5.2a) | choose `G` per descriptor type: untouched `G = id`; `A`: `c ↦ ε + c(1-τo-ε)` on `[0,1)`, `c - τo` on `[1,nA)`, `nA - τo + (c-nA)(τu-ε)` on `[nA, nA+1)`, affine continuation after; `B`: `nA + τu - τo + ε + c(1-τu-ε)` on `[0,1)`, `nA + c - τo` on `[1,nB)`, `k - τo + (c-nB)(τo-ε)` on `[nB,nB+1)`; `M`: `ε + c(1-τo-ε)`, `c - τo`, `ko - τo + (c-ko)(τo-ε)`, `ko - ε + 2ε(c-ko-1)` (the visit-free `n1` piece), `ko + ε + (c-ko-2)(1-τu-ε)`, `c - 2 - τu`, `ko+ku-τu+(c-ko-ku-2)(τu-ε)`; each piece affine with positive slope and continuous at the knots ⇒ `StrictMonoOn` (`rexB_pl_strictMonoOn`-style, LinkRecordExtension 274, or direct); the equation `off (toDVisit w) = G (visitCoord w)` is `smB_crossingParam_eq` + `cyclicOffset` evaluation (`cyclicOffset_of_le/lt`, LinkDiagram 1492-1495) per kind | 300 |
| `smB_visitCoord_lt_iff`, `smB_visitBetween_iff` (L5.2, L5.3) | `StrictMonoOn.lt_iff_lt`; `cycBetween` is three `<` | 30+30 |
| `smB_reconnect_no_between` (L5.4a) | `v ∉ {vo,vu}`: `s₁ v = succ v`, use `nextVisit_no_between` (LinkDiagramRecord 335) transported by `cyclicOffset` (rotation invariance: `rexB_cycBetween_rot` 82 with `rexB_rot_eq_cyclicOffset` 759), plus the mixed-case shift `ko +` (no `u`-visit lies off-between two `o`-visits unless wrapping through `vo`, which `nextVisit_no_between` excludes); `v = vo`: `s₁ vo = succ vu`; the elements between `off vo = 0` and `off (succ vu)` on the cycle of `vo` — the `B`-cycle contains only `vo` and `B`-word visits (all with `off > off vu`), and `off (succ vu)` is the least of these (`nextVisit_no_between` at `vu`); `v = vu`: symmetric | 190 |
| `smB_off_injOn` | `visitCoord_injOn` (LinkDiagramRecord 189) + `cyclicOffset` injective on `[0,k)`; mixed case: the shift separates the two circles | 40 |
| `firstReturn_no_between` (L5.4b, general) | induction on `returnTime`: `f^j v` (`0 < j < n`) are not `p`; claim `cycBetween (κ v) (κ u) (κ (f^n v)) → ∃ j ∈ [1,n-1], u = f^j v` for `n` below the cycle length: step `n → n+1` uses `w := f^n v ≠ v`, `¬cycBetween (κ w) (κ v) (κ (f w))` (hypothesis) ⇒ `cycBetween (κ v) (κ w) (κ (f w))` (trichotomy for distinct keys), and the splitting `arc(v, f w) = arc(v,w) ∪ {w} ∪ arc(w, f w)` (`linarith` case bash on `cycBetween`); `returnTime ≤` cycle length since the cycle returns to `v` | 160 |
| `smB_nextVisit` (L5.4) | as `restrictVisit_nextVisit` (LinkDiagramRecord 1344-1452): singleton component ⇒ both fixed (`nextVisit_eq_self`, first return to the only retained element); else `cycNext_unique_on` with `p u := SmoothKeep u ∧ s₁.SameCycle u (toDVisit w)`, `κ := smB_off`: candidate 1 `toDVisit (nextVisit w)` (retained, same cycle by L5.1 both ways, no retained `u` between by `not_visitBetween_nextVisit` + L5.3 + surjectivity of `toDVisit` onto retained same-cycle occurrences), candidate 2 `(smooth).succ (Φ w)` (`smooth_succ_val`, `firstReturn_no_between` with L5.4a) | 130 |

### §6 Assembly (~40 lines) — already proved in the skeleton modulo the chain
`smB_comp_eq`, `smB_succ_eq`, `smB_pair_eq`, `smB_bit_eq`, `smB_sgn_eq`, `smoothRecordIso`,
`smoothing_record_clause`, `smoothDiagram_componentCount` (proved), `smoothDiagram_card_crossing`
(`Fintype.card_congr smB_crossingEquiv`, `Fintype.card_subtype_compl`, 15 lines).

### §7 `OrientedSmoothingData` (~1300 lines)
| lemma | sketch | lines |
|---|---|---|
| `smB_ofDPt_outside`, `smB_toDPt_outside` | `eval` of the image is the same plane point (`smB_eval_ofDPt`), which is outside | 30+40 |
| `smB_toDPt_ofDPt`, `smB_ofDPt_toDPt` (L7.2a) | case on the strand of `p` (`o`, `u`, other) and on `param < τo`; outside ⇒ `|param - τo|·‖do‖ ≥ r > ε‖do‖`, so the rescaled parameter is in `[0,1)` and `smB_ico` is the identity; `smB_toD_ofD`, `smB_kind_hOm`… | 120+130 |
| `smB_eval_ofDPt` | `smB_edgePt_eq` | 40 |
| `smB_dir_pos` (L7.2b) | `strandOf (ofDPt p)` has kind `old`/`hOm`/… with `dirScale > 0` | 90 |
| `smB_dir_pos_before` | `strandBefore` (LinkMoves 128): parameter `0` ⇒ previous strand; the previous strand of `ofD ⟨i,a⟩` is `ofD ⟨i,a-1⟩` unless `⟨i,a-1⟩ ∈ {o,u}` (then `hOp`/`hUp`, `dirScale = 1-τ-ε`); `smB_kind_next` read backwards (`smB_next (prev s) = s`) | 130 |
| `smB_outer_iff`, `smB_outer₀` (L7.2c) | `crossingPoint_not_mem_ball` + `center`; crossings of `D₀` are outer: their point is `crossingPoint (toDCrossing y) ∉ U` | 40+30 |
| `smB_over_eq`, `smB_under_eq` (L7.2d) | `Subtype.ext`; both sides are the traversal point of the over occurrence of `ofDCrossing y` on the strand `ofDStrandAt y (overStrand y)`; `smB_crossingParam_eq` for the parameter | 60+40 |
| `smB_clean` (L7.1) | `frontier U = sphere P₀ r` (`frontier_closedBall`); a traversal point on the sphere lies on `o` or `u` (clean disc) at parameter `τ ± ρ` (`dist_edgePt`); two such points with the same plane point: same strand (`seg o ∩ seg u = {P₀}`, `dist P₀ P₀ = 0 ≠ r`) and same parameter (`edgePt_injective`) ⇒ equal; `exits`: the vertex `⟨i, (0,0)⟩` is outside (`tail_not_mem_ball`) | 110 |
| `smB_clean₀` | same four frontier points; `D₀`'s trace on the sphere: half-edges only (old edges miss `U`, `n1`,`n2` ⊆ open ball); on `hOm` the parameter is `(τo-ρo)/(τo-ε)`; `exits`: vertex `op` is inside — use instead the old vertex `P(ao+1)` (label `1` on `A`/`M`) or any `old` descriptor (every descriptor sequence has one) | 160 |
| `smB_a_ne_b`, `smB_a₀_ne_b₀` | `o ≠ u` (`Sigma`/`Arc.ext`); `jO ≠ jU` in the self case (`smooth_comps_ne_of_self`, LinkRecordExtras 285), labels differ in the mixed case | 20+40 |
| `smB_arcCover` (L7.3) | `isArc`: `start ≠ stop` (`ρo > 0`), ends on the sphere (`dist_edgePt`), inner points: `traversalBetween` on one edge with `key start < key stop` reduces to the parameter interval (`traversalBetween` unfolds; `Arc.inner_mk_iff`, LinkMoves 2727), so `|t-τo| < ρo`; `mem_iff`: `eval p ∈ U ⇒ p`'s strand is `o` or `u` (clean disc) at `|t-τo|·‖do‖ ≤ r` ⇒ `Mem a p`; converse by `dist_edgePt`; `disjoint`: `Mem a p ⇒ p.1 = o.1 ∧ p.2.1 = o.2`, similarly for `b`, and `o ≠ u` | 150 |
| `smB_over_on_a`, `smB_under_on_b` | `visitPt vo = ⟨o.1,(o.2,τo)⟩` is `Inner a` | 2×15 |
| `smB_inner_iff` | `center` and `crossingPoint_not_mem_ball` | 20 |
| `smB_arcCover₀` | `a₀` on component `jO`: its inner points run over `hOm`-tail piece, `om`, `n1`, `up`, `hUp`-head piece — `traversalBetween start r stop` with `key start = lOm + (τo-ρo)/(τo-ε)`, `key stop = lUp + (ρu-ε)/(1-τu-ε)` (self: `lUp = 0 < lOm`, a wrap; mixed: `lOm = ko < lUp = ko+2`, no wrap) ⇒ `r` is on `hOm` past the frontier parameter, on `n1`, or on `hUp` before it; all evaluate into the open ball (`Small.*_mem_ball`, `newSeg₁_subset_ball`); `mem_iff` and `disjoint` as for `D` using `smB_seg_eq` | 200 |
| `smB_a₀_start`… (4) | evaluate: `edgePt o ((τo-ρo)/(τo-ε)·(τo-ε)) = edgePt o (τo-ρo)` (`smB_edgePt_eq`, `div_mul_cancel₀`) | 4×25 |

Grand total ≈ 230 + 420 + 900 + 620 + 880 + 1050 + 40 + 1300 ≈ **5400 lines** of proofs on top of
the 1264-line skeleton (≈ 5000-5500 total effort; the design file's 1200-1800 for this item was
optimistic once the `OutsideMatch`/`ArcCover` bookkeeping is included).

## 3. Existing lemmas reused (file:line, as read on 2026-09-13)
* LinkDiagram.lean — `Shadow.crossing_card_two` 284, `eq_pair_other` 325, `mem_iff_eq_or_other`
  334, `eq_other_of_mem_of_ne` 340, `other_other` 344, `not_adjacent_other` 351,
  `Generic.common_point_unique` 414, `Generic.crossingPoint_param` 434,
  `Generic.crossingPoint_mem_interior` 456, `Generic.crossingPoint_injective` 463,
  `adjacent_mk_iff` 150, `incidentTail_mk_iff` 162, `IncidentTail.adjacent` 220,
  `Diagram.not_adjacent_over_under` 531, `det_over_under_ne_zero` 540, `sign`/`isPositive_iff_sign_eq_one`
  552-559, `crossingParam_spec/pos/lt_one` 1416-1429, `visitPt` 1435, `eval_visitPt` 1449,
  `visitPt_injective` 1453, `cyclicOffset` and lemmas 1487-1509, `single`-free.
* LinkMoves.lean — `IsDisc`/`isDisc_closedBall` 100-104, `strandOf/strandBefore` 121-136,
  `Arc.*` 145-235, `OutsideMatch` 316, `Clean` 342, `LocalFrame` 348, `OrientedSmoothingData` 713,
  `SmoothingRecordClause` 1128, `Clean.crossingPoint_not_mem_frontier` 868,
  `card_inner_eq_zero/one` 887-897, `OrientedSmoothingData.card_crossing` 1041,
  `Shadow.edge_ne_zero` 1257, `traversalBetween_inner_iff` 2691, `traversalBetween_total_inner` 2702,
  `traversalBetween_asymm'` 2717, `Arc.inner_mk_iff` 2727.
* LinkRecord.lean — `returnTime_*`/`firstReturn_*` 59-185, `mul_swap_apply_*` 202-209,
  `mul_swap_sameCycle_*` 235-246, `Record.reconnect(_apply_*)` 822-834, `SmoothKeep`/`smoothKeep_iff`
  849-866, `SmoothComps` 880, `smooth` 895, `smooth_comp` 918, `smooth_succ_val` 926,
  `smooth_comp_eq_iff` 932, `smooth_succ_val_of_not_mem/…_eq/…_eq'/…_eq_pair/…_eq_pair'` 941-1014,
  `smoothPairIso` 1040, `IsSelfCrossing` 1069, `isSelfCrossing_iff_sameCycle` 1074,
  `reconnect_sameCycle_pair_of_mixed` 1080, `reconnect_sameCycle_of_mixed` 1086,
  `reconnect_sameCycle_refines_of_self` 1098, `Record.sameCycle_of_eqOn_orbit` 1316.
* LinkRecordExtras.lean — `reconnect_sameCycle_or` 280, `not_reconnect_sameCycle_pair_of_self` 274,
  `smooth_comps_ne_of_self` 285, `componentCount_smooth_of_self/mixed` 316-320,
  `componentCount_smooth` 333, `one_le_componentCount_smooth` 341.
* LinkDiagramRecord.lean — `cycBetween` 78, `not_cycBetween_*` 85-95, `cycNext_unique_on` 102,
  `compOf` 164, `visitCoord` 181, `visitCoord_injOn` 189, `nextVisit` 258, `visitSucc` 290,
  `nextVisit_no_between` 335, `nextVisit_ne_self` 355, `nextVisit_eq_self(_iff)` 371-392, `twin` 413,
  `overBit` 470, `record` 500 and the `record_*` rfl-lemmas 520-526, `record_isSelfCrossing_iff` 583,
  `VisitBetween`/`not_visitBetween_nextVisit` 882-899, `ent`-enumeration 912-960 (template),
  `restrictVisit_nextVisit` 1344-1452 (the proof template for `smB_nextVisit`), `restrictRecordIso` 1454.
* LinkRecordExtension.lean — `rexB_cycBetween_rot` 82, `rexB_cycBetween_of_strictMonoOn` 102,
  `rexB_pl_strictMonoOn` 274, `rexB_rot_eq_cyclicOffset` 759.
* Accepted Chapter-1 library — `Polygon.lean` `edge/edgePoint/edgeSegment/edgeInterior/adjacent/incident`
  49-63; `Segment.lean` `det_smul_self` 32, `det_add_right` 36, `intersection_parameter_identity` 47,
  `intersection_parameters_unique` 55; `Crossings.lean` `edgePoint_injective` 88; `G1Consequences.lean`
  `edgePoint_zero/one` 13-16; `RegularLocus.lean` `Regular` 12, `regular_iff_edges` 18;
  `RegularPairs.lean` `RegularPair` 8, `negativeScalar_iff_dot_det` 12; `Traversal.lean`
  `traversalKey` 17, `traversalKey_injective` 31, `traversalBetween` 73; `TraversalRelabel.lean`
  `traversalKey_nonneg` 16.
* Mathlib — `frontier_closedBall`, `interior_closedBall`, `Metric.ball_subset_interior_closedBall`,
  `IsCompact.exists_isMinOn`, `isCompact_Icc`, `convex_ball`, `Convex.segment_subset`,
  `segment_eq_image`, `norm_smul`, `dist_eq_norm`, `Prod.norm_def`, `Finset.exists_min_image`,
  `Fintype.equivFin`, `Quotient.mk_out`, `Quotient.out_eq`, `Equiv.ofBijective`,
  `Equiv.subtypeEquivRight`, `Equiv.subtypeUnivEquiv`, `ZMod.val_add_of_lt`, `ZMod.val_add`,
  `ZMod.val_natCast`, `ZMod.natCast_zmod_val`, `ZMod.val_lt`, `ZMod.val_injective`,
  `Fintype.card_congr`, `Fintype.card_subtype_compl`.

## 4. Dependency order (= file order of the skeleton)
§0 → §1 (`Small`, `exists_small`, ball/segment facts) → §2 (descriptors; `smB_kind_next`,
`smB_kind_injective`, `smB_kind_ofD`, `smB_strand_cases`; `smB_seg_eq`, `smB_dir_eq`) → §3
(`smB_regular`, `smB_tail_off`, `smB_transverse`, `smB_no_triple` → `smoothDiagram`) → §4
(`smB_toD_isCrossing` → `smB_toDCrossing_*` → `smB_ofD_isCrossing` → `smB_crossingEquiv` →
`smB_toD_over` → `smB_crossingParam_eq`, `smB_sign_eq` → `smB_visitEquiv`, `smB_toDVisit_twin`,
`smB_overBit_eq`) → §5 (`smB_compOf_eq`; `smB_exists_monotone_coord` → `smB_visitBetween_iff`;
`smB_reconnect_no_between`, `smB_off_injOn`, `firstReturn_no_between` → `smB_nextVisit`) → §6
(`smoothRecordIso`, counts) → §7 (`smB_outside`, `smB_outer`, `smB_outsideMatch`; `smB_clean`,
`smB_clean₀`; arcs → `smB_orientedSmoothingData`) → §8. §5-§6 and §7 are independent of each
other (two provers can work in parallel after §4).

Definitions whose *well-formedness proof* is a chain lemma (flagged, all in the skeleton):
`smB_ofDCrossing` (uses `smB_ofD_isCrossing`), `smB_toDVisit` (`smB_toD_mem`), `smB_visitEquiv`
(`smB_toDVisit_keep/injective/surjective`), `smB_crossingEquiv` (inverse laws), `smB_outside`,
`smB_outer`, `smB_outsideMatch`, `smB_orientedSmoothingData`, `smoothDiagram`
(`smoothShadow_generic`). `smoothShadow` itself needs no hypothesis.

## 5. The three riskiest steps and fallbacks

1. **§5 cyclic-order bridge** (`smB_exists_monotone_coord` 300, `smB_reconnect_no_between` 190,
   `firstReturn_no_between` 160, `smB_nextVisit` 130). Risk: the piecewise coordinate `G` with the
   wrap at `vo` and the mixed-case shift, four descriptor types, and the general first-return
   lemma. Fallbacks: (a) drop `G`: prove `smB_visitCoord_lt_iff` by direct case analysis on the two
   kinds and label order (25 cases, mechanical); (b) drop `firstReturn_no_between`: prove
   `smB_nextVisit` by the four explicit successor formulas `Record.smooth_succ_val_of_not_mem /
   _of_succ_eq / _of_succ_eq' / _of_succ_eq_pair / _of_succ_eq_pair'` (LinkRecord 941-1014) —
   each case is "the `D₀`-successor of `w` is the lift of `succ v`, `succ vu` or `succ vo`",
   proved by `cycNext_unique_on` with `p := SmoothKeep ∧ same D₀-component` and the two
   `nextVisit_no_between` facts transported by `smB_visitBetween_iff`; (c) mirror
   `restrictVisit_nextVisit` literally with the `ent` enumeration of `D`'s component and the
   return time along `visitSucc` (the reconnect return time is at most `2 +` the number of
   skipped erased occurrences).
2. **§2 shape and position lemmas** (`smB_kind_next` 220, `smB_kind_injective` 130,
   `smB_kind_ofD` 110). Risk: `ZMod.val` arithmetic on the explicit `if`-descriptors with casts
   `ℕ → ZMod k` and the wrap `j.val = k-1`; the `cast` in `smB_au`. Fallbacks: (a) replace the
   `if`-descriptors by list-built ones (`DescrComp.ofList : List (SmVert Γ) → DescrComp Γ`, with a
   once-proved consecutive-pair lemma `pairs_ofList` and `List.getElem_append`), so each shape
   lemma is a `simp` over `List.getElem_map`/`List.getElem_range`; (b) eliminate `smB_au`'s cast by
   stating the self case for the *strand* `u` and using `Sigma.ext_iff`/`HEq` only inside
   `smB_u_eq`; (c) prove `smB_kind_injective` from `smB_strand_cases` + the six `smB_kind_*`
   evaluations + `smB_kind_ofD` (surjectivity of the seven-fold description) and a counting
   argument, instead of direct label arithmetic.
3. **§7 outside match and cleanliness** (`smB_toDPt_ofDPt`/`smB_ofDPt_toDPt` 250,
   `smB_dir_pos_before` 130, `smB_clean₀` 160, `smB_arcCover₀` 200). Risk: many cases (strand of
   `p` ∈ {`o`,`u`,other} × parameter side × frontier vs strictly outside), `strandBefore` at
   vertices, the wrap of `a₀` in the self case (`lUp = 0 < lOm`). Fallbacks: (a) a general lemma
   `Shadow.eval_injOn_unique_seg`: `eval` is injective on traversal points whose plane point lies
   on exactly one edge segment — proves both `Clean.frontier_injOn` at once; (b) prove
   `mem_iff`/`disjoint` of `ArcCover` through `smB_seg_eq` and `Small.edgePt_o_mem_ball_iff`
   uniformly rather than per kind; (c) if the wrap of `a₀` is painful, rotate the descriptor
   sequences `B`/`M` so that `a₀` never wraps (start `B` at `om` instead of `up`: `om, up,
   P(au+1), …, P(ao)`; all other lemmas are rotation-invariant); (d) the direction clauses can use
   `smB_dir_eq_scale` with `dirScale > 0` uniformly once `strandOf (ofDPt p)`'s kind is known.

Risk 4 (form, not proof): the relational `smoothing_record` (see §0). If a consumer insists on it,
either extend `OutsideMatch` with a cyclic-order clause on outside points (then the proof is the
`nextVisit_comm_of_visitBetween_iff` argument of LinkDiagramRecord 1086), or prove that an
eval- and direction-preserving bijection of outside traversal points preserves `traversalBetween`
(a connectedness argument on the outside traversal intervals; ≥ 600 lines). Not planned here.

## 6. Notes for the prover
* Never `unfold`/`show` through `Diagram.record`, `nextVisit`, `compList` or `Fintype.card
  smB_Comps`: `whnf` tries to evaluate the sorted lists/quotients and times out (observed while
  assembling `smoothRecordIso`). Use the `record_*` rfl-lemmas, `smB_visitEquiv_apply_val`, and
  `have … := rfl` casts as in `smB_comp_eq`–`smB_sgn_eq`.
* `Φ w : {v // SmoothKeep vo v}` is only *defeq* to an element of `(smooth).M`; `rw` with
  `Record.smooth_*` lemmas fails at instance transparency — state the needed equation with `rfl`.
* `smoothShadow` needs no hypothesis; `smoothDiagram` needs `Small`. Keep `ε`, `r` explicit.
* All geometry inside `U` should be done in the coordinates `(α, β)` of `P₀ + α do + β du` with
  `coords_unique`; all geometry outside `U` should be inherited from `D` through `smB_seg_eq`.
