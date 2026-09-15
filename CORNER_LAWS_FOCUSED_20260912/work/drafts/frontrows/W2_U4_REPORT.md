# W2_U4 — the geometry core (unit U4, infrastructure for U5 `typeIII_site` and U6 `typeII_move`/`typeI_move`/`crossedCusp_move`)

2026-09-14, prover for unit U4 (PLAN_FINAL.md §3 F1/F2, §4 "L-geo", §5 "U4 geometry core").  File:
`work/drafts/frontrows/W2_U4.lean` = `Skeleton_W1.lean` + ONE inserted block (`diff Skeleton_W1.lean W2_U4.lean`
= `2966a2967,5295`; zero lines removed or changed): the section `/-! ### U4 infrastructure — the geometry core -/`
… `namespace U4 … end U4` (2,328 lines, 190 declarations), placed immediately before the L-geo docstring
(the first consumers, `typeIII_site`, `typeII_move`, …).  No leaf touched: `grep -c sorry` 13 before, 13 after.
Compile `cd work/lean && lake env lean ../drafts/frontrows/W2_U4.lean`: **0 errors**, exactly 13
`declaration uses sorry` warnings (the other units' leaves), no other warning (20 s).  `#print axioms` on
`U4.isDisc_polygon`, `U4.clean_mv`, `U4.generic_of`, `U4.slotDiagramData_of`, `U4.MatchData.moveMatch`,
`U4.arcCover_of`, `U4.Chain.IsChain.before_iff`, `U4.exists_ext_of_no_r`, `U4.realizeAt_diagram_eq`:
`[propext, Classical.choice, Quot.sound]` only.  Naming: namespace `SM.FrontRows.U4` (the plan's `<unit>_` rule
realised as a namespace, as U2 did); the block opens `SM.FrontRealize SM.FrontWord.Letter Equiv` and is a
`noncomputable section`.  Scratch/verification: `/tmp/u4/A.lean` (the block as a standalone module importing a
compiled copy of U2's namespace), `/tmp/u4/full.log`.

## 0. What U4 is, in one paragraph

The plan's route for the geometric rows (F1/F2) needs, for each move, (a) a convex disc `U` hugging the active
strands with every spectator strand outside it, (b) `Clean U D` for the diagrams involved, (c) the arcs of `U`
(`ArcCover`) with their traversal order, (d) for the length-changing moves a *vertex-moved* diagram `D` on the
strands of `realize W` (generic, crossings = the kept `σ` columns, so that U2's `vertexMovedRecordIso'` gives its
record) and (e) a `MoveMatch U D (realize W)` / `MoveMatch U (realize W) (realize W')`.  U4 delivers all five as
GENERIC tools whose hypotheses are finite, slot-level checks: a disc is a `polygon L` cut by a list of half-planes;
every piece of a slot diagram is classified `PieceIn`/`PieceOut` by two inequalities per half-plane (`SegIn`/`SegOut`
— the "parallel-offset spectator argument" is one `SegOut` witness per spectator piece); a moved diagram is any
`mv : Slot W → Plane` (`vertsOf`, `shadowMv`); its genericity and crossing set follow from a pairwise
`MeetSpec` that is automatic for pieces in different columns and for unchanged pairs (`GenericData`,
`generic_of`, `slotDiagramData_of`); `Clean` follows from the classification (`clean_mv`); the arcs are slot
chains (`Chain`, `IsChain`, `arcCover_of`, `before_iff`); the move match follows from a slot bijection that
commutes with `next` on outside pieces (`MatchData`, `moveMatch`).  The realization itself is the case
`mv = pt` (`realizeAt_diagram_eq : (realizeAt pl hW hne).diagram = U2.mkDiagram … (vertsOf … (fun u => pt pl W u.1)) …`
by `rfl`).

## 1. Layout of the block (W2_U4.lean line numbers)

| lines | section | content |
|---|---|---|
| 2967-2984 | docstring, `namespace U4`, opens | |
| 2985-3173 | A. `Polygon` | `HalfPlane` (`f`, `cl`, `op`, `interior_cl`), `polygon`, `interior_polygon`, `mem_frontier_polygon_iff`, `isDisc_polygon`, the constructors `xle/xge/yle/yge/below/above` with `@[simp]` `f_*`/`b_*` |
| 3175-3309 | B. `Segments` | `segPt`, `SegIn`, `SegOut` and their consequences |
| 3311-3489 | C. `SlotDiagram` | `vertsOf`, `shadowMv`, `slotMv`, `strandMv`, `travMv`, `vertexPt`, edge/eval/seg/adjacency lemmas, `Unch`, `segPt_unch`, `realizeAt_diagram_eq` |
| 3491-3603 | D. `Classify` | `PieceIn`, `PieceOut`, `frontier_injOn_mv`, `ExitsMv`, `clean_mv`, `pieceOut_of_extCol` |
| 3605-4083 | E. `Generic` | `SigmaMeet`, `MeetSpec`, `meetSpec_of_col_ne`, `meetSpec_of_unch`, `GenericData`, `generic_of`, `ovMv`, `isCrossing_mv_iff`, `slotDiagramData_of` |
| 4085-4618 | F. `Match` | `MatchData`, `ψStr`, `ψPt`, `ψFin`, `SigmaCorr`, `MatchData.outEquiv`, `crossMap`, `crossEquiv`, `moveMatch` |
| 4620-5066 | G. `Arcs` | `cycBetween_key(')`, `cycBetween_key2(')`, `Chain`, `Chain.toArc`, `IsChain`, `inner_iff`, `mem_iff`, `before_iff`, `isArc`, `arcsOf`, `arcCover_of` |
| 5068-5183 | H. `Exits` | `exists_cusps_of_no_ext`, `exists_ext_of_no_r`, `exists_ext_of_no_l`, `exitsMv_of_ext` |
| 5185-5290 | I. `Congr` | `nextPair_congr`, `prevPair_congr`, `pt_congr`, `isSlot_congr`, `sameSlotEquiv`, `sameSlotEquiv_next`, `colOf_congr`, `xsign_congr` |

Section variables (Lean includes a section variable only when the statement mentions it): in C-E
`(pl : Placement) {W : Word} (hW : W.Closed) (hne : W ≠ []) (mv : Slot W → Plane)` (+ `(L : List HalfPlane)` in
D, `(K : ℕ → Prop)` in E); in F `(L) (pl) {W W'} (hW hW') (hne hne') (mv mv') (ψ : Slot W ≃ Slot W')`, then
`{L hW hW' mv mv' ψ}` for the `MatchData.*` lemmas (so `M.outside_iff pl hne hne' p`); in G `(L) (pl) {W} (hW)
(hne) (mv)`, inside `namespace Chain` `(c : Chain W)` then `{c} {L hW mv}` for the `IsChain.*` lemmas (so
`h.inner_iff pl hne p`, `h.isArc pl hne`).  Exact signatures of the consumer-facing declarations are copied below.

## 2. The API, by consumer task

### 2.1 The disc (`polygon L`, section A)

```lean
structure HalfPlane where a : Plane; b : ℝ; ha : a ≠ 0          -- the closed half-plane {q | a₁ q₁ + a₂ q₂ ≤ b}
def HalfPlane.f (h) (q : Plane) : ℝ := h.a.1 * q.1 + h.a.2 * q.2
def polygon : List HalfPlane → Set Plane                        -- ⋂ of the closed half-planes ([] ↦ univ)
theorem mem_polygon_iff L q : q ∈ polygon L ↔ ∀ h ∈ L, h.f q ≤ h.b
theorem mem_interior_polygon_iff L q : q ∈ interior (polygon L) ↔ ∀ h ∈ L, h.f q < h.b
theorem mem_frontier_polygon_iff L q : q ∈ frontier (polygon L) ↔ q ∈ polygon L ∧ ∃ h ∈ L, h.f q = h.b
theorem isDisc_polygon (L) {a b c d : ℝ} (hbox : ∀ q ∈ polygon L, a ≤ q.1 ∧ q.1 ≤ b ∧ c ≤ q.2 ∧ q.2 ≤ d)
    (hint : ∃ q : Plane, ∀ h ∈ L, h.f q < h.b) : IsDisc (polygon L)
-- constructors, each with @[simp] lemmas `f_xle : (xle b).f q = q.1`, `b_xle : (xle b).b = b`, etc.:
HalfPlane.xle b   -- {x ≤ b}        f q = q.1,          b
HalfPlane.xge a   -- {a ≤ x}        f q = -q.1,         -a
HalfPlane.yle d   -- {y ≤ d}        f q = q.2,          d
HalfPlane.yge c   -- {c ≤ y}        f q = -q.2,         -c
HalfPlane.below c s  -- {y ≤ c + s x}   f q = -s * q.1 + q.2,   c
HalfPlane.above c s  -- {c + s x ≤ y}   f q = s * q.1 - q.2,    -c
```
Recipe: `U := polygon [xge (pl.x k), xle (pl.x (k+3)), yle (…), above (…), yge (…)]`; `isDisc_polygon` with the
box from the two `x` lines and the `y` bounds and an explicit interior point; every membership question about a
concrete point is `simp` + `linarith` (`mem_polygon_iff`, `mem_interior_polygon_iff`, then `List.mem_cons`,
`forall_eq_or_imp`, the `f_*`/`b_*` simp lemmas).  For type III the band `[x_k, x_{k+3}] × [−(m+2)−¼, −m+¼]` is
`[xge (pl.x k), xle (pl.x (k+3)), yge (-(m+2) - 1/4), yle (-m + 1/4)]`; for type II (variant `l_{m−1} σ_m σ_{m−1}`,
plan §4) `[xge (x k), xle (x (k+3)), yle (-(m-1) + 3/4), above (-m + 1/2 + 2 * x k) (-2), yge (-(m+1) - 1/2)]`
(the slanted line `y ≥ -m + 1/2 − 2(x − x_k)` runs parallel to the pushed-down spectator `pass p (p+2)` half a unit
above it — F1's parallel-offset argument — and the horizontal `y ≥ −(m+1)−½` separates the lower arm from the
spectator at `−(m+2)`).

### 2.2 Pieces relative to the disc (sections B, D)

```lean
abbrev segPt (p₀ p₁ : Plane) (t : ℝ) : Plane := p₀ + t • (p₁ - p₀)      -- segPt_zero, segPt_one, segPt_fst, segPt_snd
def SegIn  L p₀ p₁ : Prop := ∀ h ∈ L, h.f p₀ ≤ h.b ∧ h.f p₁ ≤ h.b ∧ (h.f p₀ < h.b ∨ h.f p₁ < h.b)
def SegOut L p₀ p₁ : Prop := ∃ h ∈ L, h.b ≤ h.f p₀ ∧ h.b ≤ h.f p₁ ∧ (h.b < h.f p₀ ∨ h.b < h.f p₁)
SegIn.mem_interior (0 < t < 1) : segPt … t ∈ interior (polygon L);  SegIn.left_mem/right_mem/mem (ends and segment in polygon L)
SegOut.notMem (0 < t < 1) : segPt … t ∉ polygon L;  SegOut.left_notMem_interior/right_notMem_interior/notMem_interior
SegOut.eq_end_of_mem : segPt … t ∈ polygon L → t = 0 ∨ t = 1;  not_segIn_of_segOut;  SegIn.symm; SegOut.symm
segIn_of_interior_left (p₀ ∈ interior) (p₁ ∈ polygon) : SegIn;  segOut_of (h ∈ L) (…) : SegOut;  segOut_of_lt
def PieceIn  L hW mv (u : Slot W) : Prop := SegIn  L (mv u) (mv (next hW u))
def PieceOut L hW mv (u : Slot W) : Prop := SegOut L (mv u) (mv (next hW u))
theorem pieceOut_of_extCol {a b} (ha : HalfPlane.xge (pl.x a) ∈ L) (hb : HalfPlane.xle (pl.x b) ∈ L) {u}
    (hu : Unch pl hW mv u) (hcol : colOf u + 1 ≤ a ∨ b ≤ colOf u) : PieceOut L hW mv u
```
The classification hypothesis `hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u` is what U5/U6 verify per slot:
exterior columns by `pieceOut_of_extCol`; block pieces by their shape (`piece_spec`, `shapeOf`, `pt_cut`/`pt_cusp`,
`segPt_unch`/`segPt_pt` turn an unchanged piece into `piecePt`, whose ends are `pl.A k (shape.left/right)`) and one
`segOut_of` per spectator, `SegIn` by the inequalities for the active pieces.  Distinct ends have distinct x
(`pt_fst_ne_pt_next_fst`), so the strictness clause of `SegOut` for a vertical line is automatic.

### 2.3 The moved slot diagram (section C) and its record data (section E)

```lean
def vertsOf pl hW hne (mv : Slot W → Plane) : (shadowOf pl hW hne).Vertices := fun i j => mv (idxEquiv hW ⟨i, j⟩)
abbrev shadowMv pl hW hne mv : Shadow := (shadowOf pl hW hne).withVertices (vertsOf pl hW hne mv)
theorem vertsOf_pt : vertsOf pl hW hne (fun u => pt pl W u.1) = (shadowOf pl hW hne).vertices   -- rfl
theorem realizeAt_diagram_eq : (realizeAt pl hW hne).diagram =
    U2.mkDiagram pl hW hne (vertsOf pl hW hne (fun u => pt pl W u.1)) (generic pl hW hne)
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem                          -- rfl
theorem realizeAt_data' : U2.SlotDiagramData pl hW hne (vertsOf … (fun u => pt pl W u.1)) (generic pl hW hne)
      (realizeAt pl hW hne).overStrand (realizeAt pl hW hne).overStrand_mem (fun _ => True)
abbrev slotMv  (s : (shadowMv …).Strand) : Slot W := idxEquiv hW s          -- slot at the tail of a strand
abbrev strandMv (u : Slot W) : (shadowMv …).Strand := U2.stStrand pl hW hne (vertsOf …) u
abbrev travMv (u : Slot W) (t : Set.Ico 0 1) : (shadowMv …).Pt              -- the point of `u`'s strand at parameter `t`
abbrev vertexPt (u : Slot W) : Pt := travMv u 0;   theorem eval_vertexPt : eval (vertexPt u) = mv u
theorem eval_travMv u t : eval (travMv u t) = segPt (mv u) (mv (next hW u)) t.val
theorem eval_mv p : eval p = segPt (mv (slotPtMv p)) (mv (next hW (slotPtMv p))) p.2.2.val
theorem dir_mv s : dir s = mv (next hW (slotMv s)) - mv (slotMv s);  tail_mv; head_mv; edgePoint_mv
theorem mem_seg_mv_iff / mem_interior_mv_iff : q ∈ seg s ↔ ∃ t ∈ [0,1] / (0,1), q = segPt (mv (slotMv s)) (mv (next …)) t
theorem adjacent_mv_iff s t : Adjacent s t ↔ slotMv t = slotMv s ∨ slotMv t = next hW (slotMv s) ∨ slotMv t = prev hW (slotMv s)
def Unch pl hW mv (u : Slot W) : Prop := mv u = pt pl W u.1 ∧ mv (next hW u) = pt pl W (next hW u).1
theorem segPt_unch (hu : Unch pl hW mv u) t : segPt (mv u) (mv (next hW u)) t = piecePt pl u (if xsign u then t else 1 - t)
theorem segPt_pt u t : segPt (pt pl W u.1) (pt pl W (next hW u).1) t = piecePt pl u (if xsign u then t else 1 - t)
```
Genericity and crossing set (section E):
```lean
def SigmaMeet pl hW mv K (u v) : Prop := Unch pl hW mv u ∧ Unch pl hW mv v ∧ colOf u = colOf v ∧ K (colOf u) ∧
    ∃ m, letterAt W (colOf u) = .σ m ∧ ((shapeOf u = .pass m (m+1) ∧ shapeOf v = .pass (m+1) m) ∨ (shapeOf u = .pass (m+1) m ∧ shapeOf v = .pass m (m+1)))
def MeetSpec pl hW mv K (u v) : Prop := ∀ τ τ', 0 ≤ τ → τ ≤ 1 → 0 ≤ τ' → τ' ≤ 1 →
    segPt (mv u) (mv (next hW u)) τ = segPt (mv v) (mv (next hW v)) τ' →
    (u = v ∧ τ = τ') ∨ (v = next hW u ∧ τ = 1 ∧ τ' = 0) ∨ (u = next hW v ∧ τ = 0 ∧ τ' = 1) ∨
    (τ = 1/2 ∧ τ' = 1/2 ∧ SigmaMeet pl hW mv K u v)
structure GenericData pl hW mv K : Prop where
  inj : Function.Injective mv
  xcoord : ∀ u, (mv u).1 = (pt pl W u.1).1                          -- vertices move vertically only
  meet : ∀ u v, u ≠ v → colOf u = colOf v → MeetSpec pl hW mv K u v     -- same-column pairs only
theorem meetSpec_of_col_ne (hinj) (hx) (hne' : colOf u ≠ colOf v) : MeetSpec …     -- different columns: automatic
theorem meetSpec_of_unch (hu : Unch … u) (hv : Unch … v)
    (hK : ∀ k m hk hℓ, Unch pl hW mv (σSlotA hW hk hℓ) → Unch pl hW mv (σSlotB hW hk hℓ) → K k) : MeetSpec …  -- unchanged pairs
theorem MeetSpec.symm; SigmaMeet.symm
theorem generic_of (d : GenericData pl hW mv K) : (shadowMv pl hW hne mv).Generic
def ovMv (x : (shadowMv …).Crossing) : Strand                        -- the descending (`U2.isDesc`) strand of the crossing
theorem ovMv_mem x : ovMv … x ∈ x.val
theorem isCrossing_mv_iff (d) (hK : ∀ k m hk hℓ, K k ↔ Unch … (σSlotA hW hk hℓ) ∧ Unch … (σSlotB hW hk hℓ)) x :
    (shadowMv …).IsCrossing x ↔ ∃ k m hk hℓ, K k ∧ x = U2.σpair pl hW hne (vertsOf …) hk hℓ
theorem slotDiagramData_of (d : GenericData pl hW mv K) (hK : ∀ k m hk hℓ, K k ↔ Unch … (σSlotA …) ∧ Unch … (σSlotB …)) :
    U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) (generic_of pl hW hne mv K d) (ovMv pl hW hne mv) (ovMv_mem pl hW hne mv) K
```
So U6's `D := U2.mkDiagram .std hW hne (vertsOf .std hW hne mv) (generic_of … d) (ovMv …) (ovMv_mem …)`, and
`U2.vertexMovedRecordIso' X P Y P' hP hE hW hW' .std hne (vertsOf …) (generic_of …) (ovMv …) (ovMv_mem …)
(slotDiagramData_of … d hK) hpass hexit hexit' hnoσ W' hW'eq hne'` is its record isomorphism with `realize W'`
(`K := ExtCol X P`; `hK`: a `σ` column is exterior iff both its crossing pieces are unchanged — true because the
moved strand carries one strand of every block crossing).  U6 verifies `GenericData.meet` only for same-column pairs
`u ≠ v`: unchanged pairs by `meetSpec_of_unch`, pairs with a moved piece by hand (for type II: the three lifted
through-strand pieces against the two cusp pieces of their column — nine pairs, each `linarith` on the two
`segPt` coordinate equations, using `pt_cut`/`pt_cusp` and the shapes; adjacent pairs with `next`, the
`segPt_fst_injective` lemma pins `τ` from the x-coordinates).

### 2.4 `Clean` (section D) and the exit criterion (section H)

```lean
def ExitsMv L hW mv : Prop := ∀ i : Fin (numComp hW), ∃ (j : ZMod (period hW (rep hW i))) (t : Set.Ico 0 1),
    segPt (mv (idxEquiv hW ⟨i, j⟩)) (mv (next hW (idxEquiv hW ⟨i, j⟩))) t.val ∉ polygon L
theorem exitsMv_of_sameCycle (hex : ∀ u, ∃ v, (nextPerm hW).SameCycle u v ∧ PieceOut L hW mv v) : ExitsMv L hW mv
theorem clean_mv (hinj : Function.Injective mv) (hcl : ∀ u, PieceIn L hW mv u ∨ PieceOut L hW mv u) (hex : ExitsMv L hW mv)
    (hgen) (ov) (hov) : Clean (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov)
theorem exists_cusps_of_no_ext hW (a b) (u) (h : ∀ v, SameCycle u v → a ≤ colOf v ∧ colOf v < b) :
    (∃ v, SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m, letterAt W v.1.1 = .r m) ∧ a ≤ v.1.1 ∧ v.1.1 < b) ∧
    (∃ v, SameCycle u v ∧ v.1.2 = 0 ∧ (∃ m d, letterAt W v.1.1 = .l m d) ∧ a ≤ v.1.1 ∧ v.1.1 < b)
theorem exists_ext_of_no_r hW (a b) (hno : ∀ k, a ≤ k → k < b → ∀ m, letterAt W k ≠ .r m) (u) :
    ∃ v, SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)                   -- and exists_ext_of_no_l
theorem exitsMv_of_ext (L pl mv) {a b} (ha : xge (pl.x a) ∈ L) (hb : xle (pl.x b) ∈ L)
    (hunch : ∀ v, (colOf v + 1 ≤ a ∨ b ≤ colOf v) → Unch pl hW mv v)
    (hex : ∀ u, ∃ v, SameCycle u v ∧ (colOf v + 1 ≤ a ∨ b ≤ colOf v)) : ExitsMv L hW mv
```
Type III (`σσσ`), type II (`l σ σ` / `σ σ r`), crossed cusp (`l σ` / `σ r`): `exists_ext_of_no_r` or `_no_l` on the
block `[|X|, |X|+|P|)` gives `hex`.  Type I (`l σ r`): `exists_cusps_of_no_ext` says a non-exiting component
contains a block right cusp and a block left cusp — the only ones are `(k+2, 0)` and `(k, 0)`, whose component
reaches `(k+3, m−1)` → an exterior piece (U6 computes `next` on the five block slots).  Frontier injectivity needs
nothing beyond the classification and `mv` injective (a frontier point of a classified diagram is a vertex:
`frontier_pt_mv`).

### 2.5 The move match (section F)

```lean
structure MatchData L hW hW' mv mv' (ψ : Slot W ≃ Slot W') : Prop where
  cl  : ∀ u,  PieceIn L hW  mv  u  ∨ PieceOut L hW  mv  u
  cl' : ∀ u', PieceIn L hW' mv' u' ∨ PieceOut L hW' mv' u'
  out_iff : ∀ u, PieceOut L hW mv u ↔ PieceOut L hW' mv' (ψ u)
  pt_eq   : ∀ u, mv u ∉ interior (polygon L) → mv' (ψ u) = mv u
  int_iff : ∀ u, mv u ∈ interior (polygon L) ↔ mv' (ψ u) ∈ interior (polygon L)
  next_eq : ∀ u, PieceOut L hW mv u → ψ (next hW u) = next hW' (ψ u)
def SigmaCorr L hW hW' mv ψ (K K' : ℕ → Prop) : Prop :=
  ∀ k m (hk : k < W.length) (hℓ : letterAt W k = .σ m), K k → PieceOut L hW mv (σSlotA hW hk hℓ) →
    ∃ k' m' (hk' : k' < W'.length) (hℓ' : letterAt W' k' = .σ m'), K' k' ∧
      ψ (σSlotA hW hk hℓ) = σSlotA hW' hk' hℓ' ∧ ψ (σSlotB hW hk hℓ) = σSlotB hW' hk' hℓ'
def MatchData.moveMatch (M : MatchData L hW hW' mv mv' ψ) (pl) (hne) (hne')
    (hgen) (ov) (hov) (K) (data : U2.SlotDiagramData pl hW hne (vertsOf pl hW hne mv) hgen ov hov K)
    (hgen') (ov') (hov') (K') (data' : U2.SlotDiagramData pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov' K')
    (hσ : SigmaCorr L hW hW' mv ψ K K') (hσ' : SigmaCorr L hW' hW mv' ψ.symm K' K)
    (e : Fin (numComp hW) ≃ Fin (numComp hW'))
    (he : ∀ u, mv u ∉ interior (polygon L) → U2.slotComp hW' (ψ u) = e (U2.slotComp hW u)) :
    MoveMatch (polygon L) (U2.mkDiagram pl hW hne (vertsOf pl hW hne mv) hgen ov hov)
      (U2.mkDiagram pl hW' hne' (vertsOf pl hW' hne' mv') hgen' ov' hov')
-- call: M.moveMatch pl hne hne' hgen ov hov K data hgen' ov' hov' K' data' hσ hσ' e he
-- pieces: M.outEquiv pl hne hne' (the point correspondence, (M.outEquiv … p).1 = ψPt pl hW hW' hne hne' mv mv' ψ p.1),
--   M.crossEquiv … (the outer-crossing correspondence, val = ψFin … x.1.val = image under ψStr),
--   M.eval_ψPt_of_outside, M.dir_ψPt, M.dir_before_ψPt, M.ψPt_over, M.ψPt_under, M.crossingPoint_crossMap, M.crossingParam_crossMap
theorem crossingPoint_notMem_interior_iff L pl hW hne mv (hcl) (hgen) (x) {s} (hs : s ∈ x.val) :
    (shadowMv …).crossingPoint x ∉ interior (polygon L) ↔ PieceOut L hW mv (slotMv pl hW hne mv s)   -- inner ↔ its pieces are inside
```
Two instantiations.  **U6 (D vs `realize W`, same word):** `W' = W`, `ψ = Equiv.refl _`, `mv' = fun u => pt pl W u.1`,
`e = Equiv.refl _` (`he` is `rfl`), `data' := realizeAt_data'` with `K' := fun _ => True`; `out_iff`/`pt_eq`/`int_iff`
are: a piece is outside in `D` iff in `realize W` (the moved pieces are inside in both), vertices not in the open
disc are unmoved, moved vertices stay in the open disc; `next_eq` is `rfl`; `hσ` (exterior `σ` columns map to
themselves) is trivial, `hσ'` says an outer crossing of `realize W` (both pieces outside) is an exterior column
— the block `σ` columns have a moved (hence inside) piece, so their crossings are inner by
`crossingPoint_notMem_interior_iff`.  The result has type `MoveMatch U D (mkDiagram … (vertsOf … pt) …)`, which is
`MoveMatch U D (realizeAt pl hW hne).diagram` by `realizeAt_diagram_eq` (`rfl`; `realize W = realizeAt .std W.closed h`
by `realize_eq_realizeAt`).  **U5 (`realize W` vs `realize W'`, |P| = |P'|):** `mv = pt`, `mv' = pt'`, `ψ :=
sameSlotEquiv W W' h` (section I: the type-III words have the same slot pairs — `isSlot_congr` with equal lengths,
equal cut lengths (`σ` preserves them) and equal letter kinds); `pt_eq` by `pt_congr` (only the letter index of a
cusp column enters, and no cusp lies in the block), `next_eq` by `sameSlotEquiv_next` + `nextPair_congr` (outside
pieces: the bits at exterior cuts agree by `bit_ext`/`cut_ext` (β2, `SameEffect`), the position maps of the block
`σ` letters agree off the three active positions — `posR_σ`/`posL_σ`), `K = K' = fun _ => True` with
`data = realizeAt_data' …`, `hσ`/`hσ'` by the same congruences (`σSlotA` unfolds to the pair `(k, m)`/`(k+1, m+1)`
by the bit), and `e`/`he` the component bijection: on outside vertices `slotComp' (ψ u) = e (slotComp u)` — for U5
this is U2's conjugate-first-return machinery (`U2.cycleEquiv`, `U2.cycleEquiv_mk`, `U2.slotComp_eq_equivFin`) with
the passage of the three strands through the band, OR, simpler, the observation that `ψ` restricted to the outside
slots commutes with the first return to the outside slots (the block sends entry position `m, m+1, m+2` to exit
position `m+2, m+1, m` in BOTH words), which is exactly `U2.conj_of_passage`'s conclusion for the identity exterior
correspondence.  U4 does not build `e` for the two-word case (it is combinatorial, not geometric; see §4).

### 2.6 The arcs (section G)

```lean
structure Chain (W : Word) where u₀ : Slot W; n : ℕ; hn : 0 < n           -- the pieces u₀, next u₀, …, next^[n-1] u₀
def Chain.slot (c) hW (j : ℕ) : Slot W := (next hW)^[j] c.u₀;  slot_zero; slot_succ : c.slot hW (j+1) = next hW (c.slot hW j)
def Chain.toArc (c) pl hW hne mv : (shadowMv …).Arc        -- component of u₀, start = tail of u₀'s strand, stop = tail n steps later
theorem Chain.eval_startPt : eval (c.toArc …).startPt = mv c.u₀;  eval_stopPt : eval (c.toArc …).stopPt = mv (c.slot hW c.n)
theorem Chain.startPt_eq : startPt = vertexPt … c.u₀;  stopPt_eq : stopPt = vertexPt … (c.slot hW c.n)
theorem Chain.toArc_ne (h : c.u₀ ≠ c'.u₀) : c.toArc … ≠ c'.toArc …
structure Chain.IsChain L hW mv (c) : Prop where
  pieceIn : ∀ j, j < c.n → PieceIn L hW mv (c.slot hW j)
  vertex_interior : ∀ j, 0 < j → j < c.n → mv (c.slot hW j) ∈ interior (polygon L)
  out_prev : PieceOut L hW mv (prev hW c.u₀)
  out_stop : PieceOut L hW mv (c.slot hW c.n)
theorem IsChain.isArc (h) pl hne : (shadowMv …).IsArc (polygon L) (c.toArc pl hW hne mv)
theorem IsChain.mem_iff (h) pl hne p : (c.toArc …).Mem p ↔
    (∃ j, j < c.n ∧ ∃ t, p = travMv pl hW hne mv (c.slot hW j) t) ∨ p = vertexPt pl hW hne mv (c.slot hW c.n)
theorem IsChain.inner_iff (h) pl hne p : (c.toArc …).Inner p ↔ ∃ j, j < c.n ∧ ∃ t, p = travMv … (c.slot hW j) t ∧ (0 < j ∨ 0 < t.val)
theorem IsChain.mem_of_slot (h) pl hne (hj : j < c.n) t : (c.toArc …).Mem (travMv … (c.slot hW j) t)
theorem IsChain.inner_of_slot (h) pl hne (hj : j < c.n) t (ht : 0 < t.val) : (c.toArc …).Inner (travMv … (c.slot hW j) t)
theorem IsChain.before_iff (h) pl hne (hj : j < c.n) (hj' : j' < c.n) t t' (hp : 0 < j ∨ 0 < t.val) (hq : 0 < j' ∨ 0 < t'.val) :
    (c.toArc …).Before (travMv … (c.slot hW j) t) (travMv … (c.slot hW j') t') ↔ (j < j' ∨ (j = j' ∧ t.val < t'.val))
theorem IsChain.n_lt_period; entry_frontier; stop_frontier; entry_mem; stop_mem; slot_mem
def arcsOf pl hW hne mv (cs : List (Chain W)) : Set Arc := {a | ∃ c ∈ cs, a = c.toArc pl hW hne mv};  mem_arcsOf
theorem arcCover_of (cs : List (Chain W)) (hall : ∀ c ∈ cs, c.IsChain L hW mv) (hcl : ∀ u, PieceIn … u ∨ PieceOut … u)
    (hcover : ∀ u, PieceIn L hW mv u → ∃ c ∈ cs, ∃ j, j < c.n ∧ c.slot hW j = u)
    (hdisj : ∀ c ∈ cs, ∀ c' ∈ cs, c ≠ c' → ∀ j, j < c.n → ∀ j', j' < c'.n → c.slot hW j ≠ c'.slot hW j')
    (htouch : ∀ u, PieceOut L hW mv u → mv u ∈ polygon L → PieceIn L hW mv (prev hW u)) :
    (shadowMv pl hW hne mv).ArcCover (polygon L) (arcsOf pl hW hne mv cs)
```
The `RIIIData`/`RIIData`/`RIData` fields: `cover := arcCover_of [a, b, c] …` after rewriting `{a.toArc, b.toArc,
c.toArc}` as `arcsOf … [a, b, c]` (`Set.ext`, `List.mem_cons`), `ab := Chain.toArc_ne (entry slots differ)`,
`a_start := by rw [Chain.eval_startPt, Chain.eval_startPt]; exact (pt_eq …)`, `OverOn a x := a.Mem (visitPt (overVisit
x))`: `visitPt (overVisit x) = ⟨s.1, (s.2, ⟨cp, _, _⟩)⟩` with `s = overStrand x = strandMv … (σSlotA …)` (from the
`SlotDiagramData.overStrand` field), which is `travMv … (σSlotA …) ⟨cp, _, _⟩` definitionally, and `σSlotA … =
c.slot hW j` for the right `j` — then `IsChain.mem_of_slot`; `BeforeOn a x y` from `IsChain.before_iff` with the two
visits' `j`'s (the crossing parameters are in `(0,1)`, `Diagram.crossingParam_pos/lt_one`, so `hp`/`hq` are the `0 <
t` branches); for the realization the parameter is `1/2` (`crossingParam_eq_half`), so equal-`j` comparisons never
arise for distinct crossings.  `inner_iff`/`inner_iff'` of the site structures: `crossingPoint_notMem_interior_iff`
+ `isCrossing_mv_iff`/`eq_crossingOf`.  `no_inner` (RI/RII, the `D` side): every crossing of `D` is an exterior `σ`
pair (`slotDiagramData_of … .cross`), whose pieces are outside (`pieceOut_of_extCol`), so
`crossingPoint_notMem_interior_iff`.

### 2.7 Equal-length congruences (section I, for U5)

```lean
theorem nextPair_congr W W' (k p) (h0 : p = 0 → letterAt W k = letterAt W' k) (h0b : p = 0 → ∀ q, bit W k q = bit W' k q)
    (hb : p ≠ 0 → bit W k p = bit W' k p) (hR : p ≠ 0 → bit W k p = true → (letterAt W k).posR p = (letterAt W' k).posR p)
    (hL : p ≠ 0 → bit W k p = false → (letterAt W (k-1)).posL p = (letterAt W' (k-1)).posL p) : nextPair W (k, p) = nextPair W' (k, p)
theorem prevPair_congr … (the roles of hR/hL exchanged: rightward slots use posL of k−1, leftward slots posR of k)
theorem pt_congr W W' pl (k p) (h0 : p = 0 → (letterAt W k).idx = (letterAt W' k).idx) : pt pl W (k, p) = pt pl W' (k, p)
theorem isSlot_congr W W' (k p) (hlen : W.length = W'.length) (hcut : (cut W k).length = (cut W' k).length)
    (h0 : (letterAt W k).isCrossing = (letterAt W' k).isCrossing) : IsSlot W (k, p) ↔ IsSlot W' (k, p)
def sameSlotEquiv W W' (h : ∀ s, IsSlot W s ↔ IsSlot W' s) : Slot W ≃ Slot W'     -- identity on the pairs; sameSlotEquiv_val (simp)
theorem sameSlotEquiv_next hW hW' h u (hn : nextPair W u.1 = nextPair W' u.1) : sameSlotEquiv W W' h (next hW u) = next hW' (sameSlotEquiv W W' h u)
theorem colOf_congr W W' (k p) hu hu' (hb : p ≠ 0 → bit W k p = bit W' k p) : colOf ⟨(k,p), hu⟩ = colOf ⟨(k,p), hu'⟩
theorem xsign_congr … (hb) (h0 : p = 0 → letterAt W k = letterAt W' k) : xsign ⟨(k,p), hu⟩ = xsign ⟨(k,p), hu'⟩
```

## 3. Proof notes (what the tools actually prove, for the reviewer)

- **Half-planes.** `interior_cl : interior h.cl = h.op` by the standard argument (`Metric.eventually_nhds_iff` on
  `q + t • a`, `f_a_pos : 0 < h.f h.a`); `interior_polygon` by induction with `interior_inter`; compactness of the
  polygon from a bounding box (`Metric.isCompact_of_isClosed_isBounded`).
- **Classification ⇒ Clean.** A traversal point of a classified diagram on the frontier has parameter `0` (an inside
  piece's open segment is in the open polygon, an outside piece's open segment misses the closed polygon), so
  `frontier_injOn` reduces to injectivity of `mv` (`frontier_pt_mv`, `frontier_injOn_mv`).  This is the general
  form of β2's `frontier_injOn_blockRect`.
- **Genericity.** `regular`: the x-components of the edges are the realization's (`xcoord`), nonzero
  (`dir_slot_fst_ne_zero`); at a cut slot consecutive edges have the same x-sign (`xsign_next_iff`,
  `dir_slot_fst_pos_iff`), at a cusp the two arm ends share their x-coordinate
  (`pt_prev_fst_eq_pt_next_fst_of_cusp`), so antiparallel would force `r = −1` and `mv (prev u) = mv (next u)`,
  against injectivity and `next_next_ne`.  `tail_off`/`transverse`/`no_triple`: the meeting specification with
  `τ = 0`, with arbitrary parameters, with two interior parameters (the third case leaves only the `σ` clause,
  whose two partners have the same shape, hence coincide by `slot_eq_of_piece_eq`).  Different columns meet only at
  a shared vertex (`affine_eq_max/min` on the x-coordinates: the common x is a column boundary, attained only at an
  end), unchanged pairs are the realization's `common_point`.
- **Crossing set.** `isCrossing_mv_iff` from `MeetSpec` (⇒) and from `σ_meet`/`not_adjacent_of_σ` on unchanged `σ`
  pairs (⇐, needs `K k → Unch A ∧ Unch B`); the sign is computed from `dir_slot_eq`/`Shape.vec_pass`
  (`det = ±2 w k`), matching the printed rule `bit k m = bit k (m+1)`.
- **Move match.** The point map is "same strand label, same parameter" through the slot bijection; outside points
  correspond because outside pieces are literally equal (`pt_eq` at both ends + `next_eq`) and inside pieces have
  their open segments in the open polygon on both sides; the directions at points strictly outside are those of
  outside pieces (the arriving direction at a tail vertex outside the polygon is that of the previous piece, which
  is outside since its head is outside the polygon).  Outer crossings are the `σ` pairs whose pieces are outside
  (`crossingPoint_notMem_interior_iff`); `ψFin` maps the strand pair; the two crossing points coincide (both are
  common points of the same two segments, `Generic.common_point_unique`) and so do the crossing parameters
  (`segPt_injective`, the edge being nonzero by genericity); the component clause is the hypothesis `he` on vertices
  not in the open polygon (an outside point's slot is an outside piece or an inside piece at its frontier tail).
- **Arcs.** The cyclic order of `TraversalPoint k` is read on keys `label.val + t`; `cycBetween_key`/`cycBetween_key2`
  (pure arithmetic: `add_mod_cases`, then `omega` after the real inequalities are turned into integer ones by
  `nat_lt_add_iff` etc.) give `Inner ↔ (j < n ∧ (0 < j ∨ 0 < t))` and `Before ↔ (j < j' ∨ (j = j' ∧ t < t'))`.
  `n < period` from the chain data (`IsChain.n_lt_period`).  `arcCover_of`: a point of the polygon on an outside
  piece is that piece's tail (`SegOut.eq_end_of_mem`), which `htouch` makes the stop of a chain; two chains sharing
  a point share a piece (or one's stop is the other's inside piece, or both stops coincide and then so do the
  previous pieces).
- **Exits.** A cycle with no exterior piece has a vertex of maximal `xcoord2`, which is a right cusp (`xcoord2_next`:
  a rightward step increases, a leftward step decreases `xcoord2`; the x-direction flips exactly at cusps,
  `xsign_next_iff`; `xsign_cusp_l/r`), and one of minimal `xcoord2`, a left cusp.

## 4. What U4 does NOT provide (deliberately, or out of budget) — the consumers' remaining work

1. **The concrete half-plane lists, the moved vertices `mv`, and the piece classification** for each pattern
   (U5: the band; U6: the hexagons of PLAN_FINAL §4 and the lifted/zigzag/exchanged vertices).  Every such fact is
   a finite check with `pt_cut`, `pt_cusp`, `piece_spec`, `shapeOf`, `segPt_unch` and `linarith`; the tools above
   turn the checks into `IsDisc`, `Clean`, `Generic`, `SlotDiagramData`, `MoveMatch`, `ArcCover`.
2. **`MeetSpec` for pairs containing a moved piece** (U6; same column only, `meetSpec_of_col_ne` does the rest).
3. **The component bijection `e` for two different words** (U5): U4 states the hypothesis `he` on the vertices
   outside the open disc; U5 builds `e` from U2's `cycleEquiv` (conjugate first returns to the outside slots) or by
   any direct argument.  For U6 (`ψ = Equiv.refl`) `e = Equiv.refl _` and `he` is `rfl`.
4. **The `SlotDiagramData` of `realize W`** is `realizeAt_data'` (= U2's `realizeAt_data`, restated on `vertsOf pt`).
5. **`RIData`/`RIIData`/`RIIIData` assembly** (the remaining fields — `start_eq`/`a_start` via `Chain.eval_startPt`,
   `sep_*`, `same_over`, `top_*`, `rev_*` via `IsChain.mem_of_slot`/`before_iff`, `inner_iff(')`/`no_inner` via
   `crossingPoint_notMem_interior_iff`, `kink`/`x₁`/`x₂`/`xab` … via `U2.σcross`-style crossings
   `⟨U2.σpair … hk hℓ, (isCrossing_mv_iff …).2 ⟨k, m, hk, hℓ, hK, rfl⟩⟩` or `crossingOf` on the realization).
6. Nothing in U4 is specific to a placement; `pl` is a parameter everywhere (`realize` uses `.std`).

## 5. Gotchas recorded for the consumers

1. **Strand types.**  `(shadowMv pl hW hne mv).Strand`, `(shadowOf pl hW hne).Strand`, `(realizeAt pl hW hne).Γ.Strand`
   and `Idx hW` are definitionally but not syntactically equal.  Stay inside the `shadowMv` vocabulary
   (`slotMv`, `strandMv`, `travMv`, `vertexPt`, `dir_mv`, `mem_seg_mv_iff`); to bring in a fact about the realization
   stated with `strandOfSlot`/`(realizeAt …).Γ.dir`, restate it with `have … := …` (accepted by defeq) or reprove
   from `dir_slot_eq`/`piecePt` (this is how `generic_of`'s `transverse` and `slotDiagramData_of`'s `sgn` are done;
   `rw` across the two typings fails).  `realizeAt_diagram_eq` is `rfl`, so `show`/`exact` convert
   `(realize W).diagram` goals to the `mkDiagram … (vertsOf … pt)` form after `rw [realize_eq_realizeAt]`.
2. **Section variables.**  `PieceIn L hW mv u`, `PieceOut L hW mv u`, `Unch pl hW mv u`, `MeetSpec pl hW mv K u v`,
   `GenericData pl hW mv K`, `MatchData L hW hW' mv mv' ψ`, `SigmaCorr L hW hW' mv ψ K K'`, `ExitsMv L hW mv`,
   `Chain.IsChain L hW mv c` (as `c.IsChain L hW mv`); the `MatchData.*` and `IsChain.*` lemmas take `pl hne (hne')`
   explicitly and infer the rest from `M`/`h`.
3. **`Chain` is over `W` only**; `c.slot hW j`, `c.toArc pl hW hne mv`.  The arc's traversal points are
   `travMv pl hW hne mv (c.slot hW j) t`; `Chain.travMv_slot_eq` rewrites them to `⟨(c.toArc …).i, ((c.toArc …).start.1 + j, t)⟩`.
4. **`MeetSpec`'s `σ` clause carries `τ = τ' = 1/2`** (in the tail-to-head parametrization of BOTH pieces); consumers
   never prove it directly — it only arises through `meetSpec_of_unch`.
5. **`hK` in `slotDiagramData_of` is an `↔`**: exterior columns must have both crossing pieces unchanged (true for
   the vertex-moved `D`: only block vertices move), and block `σ` columns must have a changed piece.
6. `Set.mem_setOf_eq` is deprecated in this Mathlib (`Set.mem_ofPred_eq`); `push_neg` → `push Not`; `if_pos` →
   `ite_eq_left`; `omega` needs the bounds `B < k` explicitly when reasoning about `%`.

## 6. Declarations (file order; `theorem`/`def`/`structure`, 190 in total)

A: `HalfPlane`, `HalfPlane.f/cl/op`, `f_add/f_sub/f_smul/f_segPt`, `continuous_f`, `isClosed_cl`, `isOpen_op`,
`op_subset_cl`, `convex_cl`, `f_a_pos`, `interior_cl`, `mem_interior_cl_iff`, `polygon`, `mem_polygon_iff`,
`interior_polygon`, `mem_interior_polygon_iff`, `isClosed_polygon`, `convex_polygon`, `interior_polygon_subset`,
`mem_frontier_polygon_iff`, `mem_frontier_polygon_of`, `notMem_interior_of_mem_frontier`, `mem_of_mem_frontier`,
`isDisc_polygon`, `HalfPlane.xle/xge/yle/yge/below/above` + `f_*`, `b_*`.
B: `segPt`, `segPt_zero/one/fst/snd`, `segPt_fst_injective`, `segPt_injective`, `segPt_reverse`, `SegIn`, `SegOut`,
`SegIn.symm/mem_interior/left_mem/right_mem/mem`, `SegOut.symm/notMem/left_notMem_interior/right_notMem_interior/
notMem_interior/eq_end_of_mem`, `not_segIn_of_segOut`, `segIn_of_interior_left/right`, `segOut_of`, `segOut_of_lt`.
C: `vertsOf`, `shadowMv`, `vertsOf_pt`, `shadowMv_pt`, `slotMv`, `slotMv_stStrand`, `stStrand_slotMv`, `slotMv_injective`,
`tail_mv`, `head_mv`, `dir_mv`, `edgePoint_mv`, `slotPtMv`, `eval_mv`, `mem_seg_mv_iff`, `mem_interior_mv_iff`,
`adjacent_mv_iff`, `incidentTail_mv_of`, `strandMv`, `travMv`, `slotPtMv_travMv`, `eval_travMv`, `travMv_slotPtMv`,
`vertexPt`, `eval_vertexPt`, `Unch`, `unch_pt`, `segPt_piecePt`, `segPt_pt`, `segPt_unch`, `pt_fst_ne_pt_next_fst`,
`pt_fst_mem`, `pt_next_fst_mem`, `realizeAt_diagram_eq`, `realizeAt_data'`.
D: `PieceIn`, `PieceOut`, `not_pieceIn_of_pieceOut`, `frontier_pt_mv`, `frontier_injOn_mv`, `ExitsMv`,
`exitsMv_of_sameCycle`, `exits_mv`, `clean_mv`, `pieceOut_of_extCol`.
E: `SigmaMeet`, `SigmaMeet.symm`, `MeetSpec`, `MeetSpec.symm`, `affine_eq_max/min`, `meetSpec_of_col_lt/ne`,
`piecePt_param_injective`, `segPt_unch_eq_pt`, `meetSpec_of_unch`, `GenericData`, `GenericData.meetSpec`,
`pt_prev_fst_eq_pt_next_fst_of_cusp`, `generic_of`, `ovMv`, `ovMv_mem`, `ovMv_eq_of_σpair`, `isCrossing_mv_iff`,
`K_of_σpair`, `slotDiagramData_of`.
F: `MatchData`, `ψStr`, `slotMv_ψStr`, `ψStr_symm_ψStr`, `ψStr_injective`, `ψStr_strandMv`, `ψPt`, `ψPt_travMv`,
`slotPtMv_ψPt`, `ψPt_param`, `ψPt_symm_ψPt`, `eval_ψPt`, `ψFin`, `ψFin_pair`, `ψFin_symm_ψFin`, `ψFin_σpair`,
`slotMv_pred`, `pieceOut_of_notMem`, `crossingPoint_notMem_interior_iff`, `SigmaCorr`, `MatchData.symm/mv_eq_of_out/
mv_next_eq_of_out/segPt_eq_of_out/pieceIn_of_not_out/pieceIn'_of_not_out/outside_iff/eval_ψPt_of_outside/outEquiv/
outEquiv_apply/pieceOut_of_eval_notMem/dir_ψPt/dir_before_ψPt/crossMap/crossMap_val/seg_eq_of_out/outer_spec/
crossingPoint_crossMap/crossingParam_crossMap`, `pt_ext'`, `MatchData.ψPt_over/ψPt_under/crossEquiv/moveMatch`.
G: `nat_lt_add_iff`, `nat_add_lt_iff`, `nat_add_lt_add_iff`, `cycBetween_key'`, `cycBetween_key`, `cycBetween_key2'`,
`cycBetween_key2`, `Chain`, `Chain.slot/slot_zero/slot_succ/strandMv_slot/toArc/toArc_i/startPt_eq/stopPt_eq/
eval_startPt/eval_stopPt/toArc_ne/IsChain/period_eq/k_eq/key_start/key_stop/key_pt/travMv_slot_eq`,
`Chain.IsChain.entry_notMem_interior/stop_notMem_interior/entry_mem/stop_mem/entry_frontier/stop_frontier/
n_lt_period/slot_mem/inner_iff/mem_iff/mem_of_slot/inner_of_slot/before_iff/isArc`, `arcsOf`, `mem_arcsOf`, `arcCover_of`.
H: `colOf_of_cusp`, `exists_cusps_of_no_ext`, `exists_ext_of_no_r`, `exists_ext_of_no_l`, `exitsMv_of_ext`.
I: `nextPair_congr`, `prevPair_congr`, `pt_congr`, `isSlot_congr`, `sameSlotEquiv`, `sameSlotEquiv_val`,
`sameSlotEquiv_symm_val`, `sameSlotEquiv_next`, `colOf_congr`, `xsign_congr`.
