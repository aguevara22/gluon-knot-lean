# U_S7D_REPORT — unit U110-D (coefficient transport for spectators / relocated carriers; prefix `s7d_`), 2026-09-15

File: `work/drafts/corner/U_S7D.lean` (copy of `Statements_FINAL.lean` + 550 lines, inserted inside `section VertexEdge`
immediately before the docstring of `s7_sliding_law_at`, the first leaf that consumes them — U110-E; U110-F/K consume
them for the bigon branch).
Check: `cd work/lean && lake env lean ../drafts/corner/U_S7D.lean` — **0 errors, 0 new warnings**, 14 `declaration uses
sorry` warnings (the 10 leaves of the other units + the 4 row theorems of §6; this is a HELPER unit, it owns no leaf).
`grep -c sorry`: 16 before → 16 after.  `diff Statements_FINAL.lean U_S7D.lean | grep -c '^<'` = 0 (nothing removed or
changed; only helper text added).  No definition, structure, statement, name or docstring changed; no import added; no
`open` added (all CB names are written `CB.…`).  Name clash scan: `s7d_` occurs nowhere under work/lean.
Axioms (`#print axioms`, scratch copy): every `s7d_` lemma that mentions `homfly`/`cornerHomfly`/`cornerCoefficient` =
[propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness] (through `P_eq_homfly` /
`presentations`, exactly as `cornerHomfly_ne_zero`); the list / record / key lemmas = standard axioms only.

## 0. What this unit provides (the interface for U110-A/B/E/F/K), in one paragraph

PLAN §3.3 names for U110-D "coefficient transport for spectators / relocated carriers (RecordIso via the CB record
bridge, or Deform)" without fixing statements.  The route chosen is the RECORD route, fully general: **two carriers
`q` (of a decomposition `S` of a generic `P : LabelledTuple n`) and `q'` (of `T` of a generic `Q : LabelledTuple m`,
any `m` — the halves have different sizes) have equal `cornerHomfly`, `carrierCrossingCount`, `cornerSlot` and
`cornerCoefficient` as soon as (i) their abstract restricted Gauss records `CB.gaussRecord (CB.cg hn hP)
(carrierCrossings hn hP S q)` and `CB.gaussRecord (CB.cg hm hQ) (carrierCrossings hm hQ T q')` are isomorphic
(`RecordIso`) and (ii) their real rotations `carrierRotation` agree.**  The record isomorphism is manufactured from a
plain visit map `φ : Visit P → Visit Q` by three interchangeable hypothesis packages: the mapped restricted Gauss list
is a ROTATION of the target's (`s7d_gaussRecordIso`), or `φ` is strictly increasing in the traversal key on the
carrier's visits (`s7d_gaussList_eq_of_strictMono`), or increasing up to ONE cyclic cut at a threshold `c`
(`s7d_gaussList_isRotated_of_cut`: the labelling of a half starts at the contact, and a contact at `M = 0` wraps the
key) — plus twin compatibility `φ (visitTwin v) = visitTwin (φ v)` and preservation of the positive over bit
`CB.positiveOverBit`, for which three sufficient conditions are given (determinant-sign equivalence, positive
rescaling of both edge directions, equal `crossingSign`).  The traversal key is decoded as "edge label, then edge
parameter" (`s7d_geometricVisitKey_lt_iff`, `s7d_strictMono_of_edgewise`), the form of `VertexLocalData.visit_order`
(lem:wall-sides (V), SM/VertexSides.lean:16-28).  `Deform` is NOT needed for coefficient transport: rotation equality
has to come from geometry anyway (U110-A/I: lem:rot (ii) along the regular family, or principal-angle addition), and
with it the record route closes `c(q) = c(q')` combinatorially.  As a by-product the same machinery gives a
`Deform`-free proof of the `homfly` hypothesis of the accepted `MarkTransport.cornerCoefficient_transport`
(CChamber.lean:481) for ANY full mark transport that preserves the over bits (`s7d_homfly_transport`,
`s7d_cornerCoefficient_transport`) — e.g. CSilent's `sideTransport` with `sides_markTurn_eq`'s sign clause.

## 1. Proved (all `s7d_`, all inside `section VertexEdge` before `s7_sliding_law_at`; `{n} [NeZero n]` from the section)

### 1.1 List layer (standard axioms)
* `s7d_next_map (l : List α) (f) (hnd : (l.map f).Nodup) (x) (hx : x ∈ l) : (l.map f).next (f x) _ = f (l.next x hx)`.
* `s7d_gaussList_eq_of_strictMono (hcP hcQ X Y φ) (hmem : ∀ w, w.1 ∈ Y ↔ ∃ v, v.1 ∈ X ∧ φ v = w) (hmono : ∀ v w, v.1 ∈ X →
  w.1 ∈ X → key v < key w → key' (φ v) < key' (φ w)) : CB.gaussList hcQ Y = (CB.gaussList hcP X).map φ` (both are the
  strictly key-sorted lists of the same members: `CB.kl2_gaussList_pairwise_lt`, `List.perm_ext_iff_of_nodup`,
  `List.Perm.eq_of_pairwise`).  Here `key := geometricVisitKey hcP`, `key' := geometricVisitKey hcQ`.
* `s7d_sorted_eq_filter_append (key c l) (hl : l.Pairwise (key · < key ·)) : l = l.filter (key · < c) ++ l.filter (!…)`.
* `s7d_gaussList_isRotated_of_cut (hcP hcQ X Y φ c) (hmem) (hmono : … key v < key w → (key w < c ∨ c ≤ key v) → key' (φ v)
  < key' (φ w)) (hcut : … key v < c → c ≤ key w → key' (φ w) < key' (φ v)) : (CB.gaussList hcQ Y).IsRotated
  ((CB.gaussList hcP X).map φ)` — order preserved inside each block `key < c` / `key ≥ c`, the upper block comes first
  in `Q`.
* `s7d_isRotated_filterMap`, `s7d_isRotated_filter` — rotations pass through `filterMap`/`filter` (Mathlib has neither).
* `s7d_markList_filterMap (hn hP) : (markList hn hP).filterMap Sum.getRight? = geometricGaussList (CB.cg hn hP)`.
* `s7d_mem_iff_of_equiv (X Y) (φ : Visit P ≃ Visit Q) (hXY : ∀ v, (φ v).1 ∈ Y ↔ v.1 ∈ X) (w) : w.1 ∈ Y ↔ ∃ v, v.1 ∈ X ∧ φ v = w`.

### 1.2 Key decoding
* `s7d_geometricVisitKey_lt_iff (hc) (v w) : key v < key w ↔ (v.2.val.val < w.2.val.val ∨ (v.2.val = w.2.val ∧
  visitParameter v < visitParameter w))`.
* `s7d_strictMono_of_edgewise (hcP hcQ X φ) (hedge : ∀ v, v.1 ∈ X → (φ v).2.val = v.2.val) (hpar : ∀ v w, v.1 ∈ X → w.1 ∈ X
  → v.2.val = w.2.val → param v < param w → param (φ v) < param (φ w)) : ∀ v w, … key v < key w → key' (φ v) < key' (φ w)`
  (same `n`: `P Q : LabelledTuple n`).

### 1.3 Over bits
* `s7d_positiveOverBit_eq_of_det_pos_iff (v w) (h : 0 < det (edge Q w.2) (edge Q (twin w).2) ↔ 0 < det (edge P v.2)
  (edge P (twin v).2)) : CB.positiveOverBit w = CB.positiveOverBit v`.
* `s7d_det_smul_smul (c d u w) : det (c • u) (d • w) = (c * d) * det u w`.
* `s7d_positiveOverBit_eq_of_smul (v w) (hc : 0 < c) (hd : 0 < d) (h1 : edge Q w.2 = c • edge P v.2) (h2 : edge Q
  (twin w).2 = d • edge P (twin v).2) : bits equal` (cut edges of a half; corner edges `corner_polygons.2.1`).
* `s7d_positiveOverBit_eq_of_crossingSign (v w) (h : crossingSign Q w.2 (twin w).2 = crossingSign P v.2 (twin v).2) : bits equal`.

### 1.4 The record isomorphism and the coefficient transport
* `s7d_gaussRecordIso (hcP hcQ X Y φ) (hrot : (CB.gaussList hcQ Y).IsRotated ((CB.gaussList hcP X).map φ)) (htwin : ∀ v,
  v.1 ∈ X → φ (visitTwin v) = visitTwin (φ v)) (hbit : ∀ v, v.1 ∈ X → CB.positiveOverBit (φ v) = CB.positiveOverBit v) :
  RecordIso (CB.gaussRecord hcP X) (CB.gaussRecord hcQ Y)` (a `def`; `Φ := Equiv.ofBijective` of `φ` restricted —
  injective by nodup of the rotated list, surjective by membership; `succ_eq` by `CB.gaussSucc_val`,
  `List.isRotated_next_eq`, `s7d_next_map`; `pair_eq` by `htwin`; signs all `1`).
* `s7d_cornerHomfly_eq_of_recordIso (hn hm hP hQ hS q hT q') (h : Nonempty (RecordIso (gaussRecord … (carrierCrossings … q))
  (gaussRecord … (carrierCrossings … q')))) : cornerHomfly hn hP S q hS = cornerHomfly hm hQ T q' hT` — `P_eq_homfly`
  twice, `presentations` with `positiveLiftRecordIso.trans (h.some.trans positiveLiftRecordIso.symm)`.
* `s7d_carrierCrossingCount_eq_of_recordIso … : carrierCrossingCount hn hP S q = carrierCrossingCount hm hQ T q'`
  (`RecordIso.card_M_eq`, `CB.kl1_card_retained` = twice the crossings, on both sides).
* `s7d_cornerSlot_eq_of_recordIso … (hrot : carrierRotation hn hP S q = carrierRotation hm hQ T q') : cornerSlot … = cornerSlot …`.
* `s7d_cornerCoefficient_eq_of_recordIso … (h) (hrot) : cornerCoefficient hn hP S q hS = cornerCoefficient hm hQ T q' hT`.
* `s7d_cornerCoefficient_eq_of_gaussList_rotated … (φ) (hrot) (htwin) (hbit) (hr) : c(q) = c(q')` — the list form at
  `X := carrierCrossings hn hP S q`, `Y := carrierCrossings hm hQ T q'`.
* `s7d_cornerCoefficient_eq_of_strictMono … (φ) (hmem) (hmono) (htwin) (hbit) (hr) : c(q) = c(q')` — the key-monotone form.
* `s7d_cornerCoefficient_eq_of_cut … (φ c) (hmem) (hmono) (hcut) (htwin) (hbit) (hr) : c(q) = c(q')` — the cut form.
* `s7d_cornerProduct_eq_of_equiv (hn hm hP hQ hS hT) (e : Component hn hP S ≃ Component hm hQ T) (hcoef : ∀ q, c(q) = c(e q)) :
  cornerProduct hn hP S hS = cornerProduct hm hQ T hT`.

### 1.5 Full mark transports (SM/CChamber.lean `MarkTransport`), `Deform`-free
* `s7d_gaussList_transport (τ : MarkTransport hn hP hQ) (X) : (CB.gaussList (CB.cg hn hQ) (τ.support X)).IsRotated
  ((CB.gaussList (CB.cg hn hP) X).map τ.visit)` (from `τ.markList_rotated` through `s7d_markList_filterMap`,
  `s7d_isRotated_filterMap`, `s7d_isRotated_filter`, `List.filter_map`, `τ.visit_fst`, `τ.mem_support`).
* `s7d_homfly_transport (τ) (hS) (q) (hbit : ∀ v, v.1 ∈ carrierCrossings hn hP S q → CB.positiveOverBit (τ.visit v) =
  CB.positiveOverBit v) : homfly (positiveLift hn hQ (τ.support S) (τ.component S q) _) = homfly (positiveLift hn hP S q hS)`.
* `s7d_positiveOverBit_transport (τ X) (hsgn : ∀ v, v.1 ∈ X → crossingSign Q (τ.visit v).2 (τ.visit (twin v)).2 =
  crossingSign P v.2 (twin v).2) : ∀ v, v.1 ∈ X → bits equal`.
* `s7d_cornerCoefficient_transport (τ) (hS) (q) (hbit) (hrot : carrierRotation hn hQ (τ.support S) (τ.component S q) =
  carrierRotation hn hP S q) : cornerCoefficient hn hQ (τ.support S) (τ.component S q) _ = cornerCoefficient hn hP S q hS`
  = `τ.cornerCoefficient_transport hS q hrot (s7d_homfly_transport …)`.

## 2. Not proved / not attempted (and why)

* No leaf belongs to this unit; nothing of U110-D's PLAN description is left open at the level of coefficient transport.
* The `Deform` alternative (CS3 §E / `deform_positiveLift_path`) was NOT built: it is strictly more expensive (a
  continuous family of corner polygons with constant crossing set and genericity at every time) and unnecessary once
  the record route exists — the only geometric input the record route needs is the rotation equality, which the
  `Deform` route needs too (`carrierRotation_path`).
* Not in this unit (they are U110-A/B's content, stated as the HYPOTHESES `hmem`/`hmono`/`hcut`/`htwin`/`hbit`/`hr` of
  §1.4): the contact-wall visit map itself on persistent visits, the ownership correspondence (which carrier of `P₊`
  corresponds to which carrier of `P₋`, and to which carrier of `T_i` on the half `λ_i`), the persistence of the visit
  order (`VertexLocalData.visit_order`), the sign persistence of the persistent crossings (`crossingSign_eq` along the
  germ, as in CSilent `sides_markTurn_eq`), and the rotation equality (lem:rot (ii) / principal-angle addition).

## 3. Notes for U110-A / U110-B / U110-E / U110-F (how to consume)

1. **Spectator carriers at the wall (`x₋ ∉ S`, sliding step (1), bigon ineligible `T`).**  Take `φ := ` the persistent
   visit transport (`contactVisitTransport`, VertexSides.lean:16-28, or the canonical `visitTransport` on the unaffected
   crossings).  The visits of the carrier's crossings all keep their edges (`hedge`) and their order on each edge
   (`hpar` from `visit_order`), so `s7d_strictMono_of_edgewise` gives `hmono` and `s7d_cornerCoefficient_eq_of_strictMono`
   applies.  CAUTION: a spectator carrier may have the contact crossing `x₋ = {a, M−1}` as one of its OWN self-crossings
   (unselected, both visits on it); then `φ` must relocate `x₋ ↦ x₊ = {a, M}` and the visit on edge `M−1` (parameter
   near `1`) moves to edge `M` (parameter near `0`).  Its key still moves monotonically relative to every other visit
   (no visit lies in the contact window on edges `M−1`, `M`: `visit_windows`) EXCEPT when `M = 0`, where the key wraps
   from `≈ n` to `≈ 0`: use the cut form `s7d_cornerCoefficient_eq_of_cut` with `c := ` the key of that visit.  The over
   bit at the relocated visit is preserved because the crossing sign is: for a sliding wall the path `M−1 → M → M+1`
   crosses the line of edge `a` once, in the same direction on both sides (`SlidingCrossingPattern`), so
   `det(edge a, edge (M−1))` on `P₋` and `det(edge a, edge M)` on `P₊` have the same sign — use
   `s7d_positiveOverBit_eq_of_crossingSign` or `_of_det_pos_iff`.
2. **Relocated carriers to the halves (sliding step (2), bigon eligible `T`).**  `Q := firstHalf/secondHalf g.center M a`
   with `hm := (contactHalfSizes_bounds hn h.1).i.1`.  The half's labelling starts at the contact vertex, so the key
   order of the retained visits is the parent's cyclic order cut at `a`: use the cut form with `c := ` the key of the
   cut (e.g. `(a : ZMod n).val + r`, `r` the contact parameter on edge `a`).  The two cut edges are sub-segments of the
   parent's edges `a` and `M−1`/`M` with the same direction up to a positive factor — `s7d_positiveOverBit_eq_of_smul`
   for visits on them; visits on retained edges have literally equal directions (`c = d = 1`).
3. **Assembling `cornerProduct`.**  `s7d_cornerProduct_eq_of_equiv` needs an `Equiv` of carriers and equal coefficients
   carrier by carrier; the `Equiv` is U110-B's carrier correspondence.  For the state sums themselves the accepted
   `MarkTransport.cornerStateSum_transport` does not apply at a contact wall (the full mark lists are NOT rotations of
   each other: the vertex mark `M` and the contact visit swap), so U110-E has to reindex `uniformDecompositions` by hand
   (device of `cornerStateSum_transport`: `Finset.sum_nbij` on the underlying sets, `cornerStateSum_eq_sum_independentSupports`).
4. **Rotation equality `hr`** is a hypothesis everywhere; it is the ONLY geometric input the coefficient needs beyond
   the record data.  Sources: `carrierRotation_path`/`turn_transportedCornerPolygon_path` (CChamber PathTransport) for
   families with constant mark list; for the contact wall U110-A/I (eq. s7c:turn-short-a/b, rotation ledger).
5. **Why `Nonempty (RecordIso …)` and a `def` for the iso**: `presentations` consumes `Nonempty`; the `def`
   `s7d_gaussRecordIso` is kept as data so U110-G/H can also read off occurrence bijections if needed (`.Φ`).

## 4. Mathlib / library pitfalls met

* `List.filter_append_perm` is stated with `fun x => !p x`, not `decide (¬ …)`; the split lemma follows that form.
* `List.Perm.eq_of_pairwise` needs pointwise antisymmetry `r x y → r y x → x = y`; for strict `<` on keys pass
  `fun _ _ _ _ hxy hyx => absurd (hxy.trans hyx) (lt_irrefl _)`.
* `Fintype.card (CB.gaussRecord hc X).M` carries the structure's own `mFin` instance; rewriting it with
  `CB.gaussRecord_M` fails (motive not type correct).  Use `Fintype.card_congr (Equiv.refl _)` to move to the default
  instance on `{v : Visit P // v.1 ∈ X}` before `CB.kl1_card_retained`.
* `CB.gaussPair_val`'s second rewrite fails on the subtype coercion (`Crossing P` vs `{s // IsCrossing P s}` under
  `implicit` transparency); both sides are `rfl`, so `show φ (visitTwin v.1) = visitTwin (φ v.1)` and `exact htwin`.
* Mathlib has no `IsRotated.filter`/`IsRotated.filterMap`; both are 5-liners via `isRotated_iff_mod`,
  `rotate_eq_drop_append_take`, `take_append_drop`, `isRotated_append`.
* `geometricVisitKey hc v = ↑(v.2.val.val) + visitParameter v` is `rfl` (through `traversalKey` and
  `geometricVisitPosition`); `crossingParameter_interior_of_geometry` gives `0 < param < 1` (needed for the key decoding).
* `ZMod.val_injective` needs `[NeZero n]`, so the key decoding keeps the section instance (the bit/list lemmas use
  `omit [NeZero n] in` to silence the unused-variable linter).
* All CB names are in namespace `SM.CB` (`CB.gaussRecord`, `CB.gaussList`, `CB.cg`, `CB.positiveOverBit`,
  `CB.positiveLiftRecordIso`, `CB.kl0_*`, `CB.kl1_*`, `CB.kl2_*`); Statements_FINAL opens only `Link Carrier`.
