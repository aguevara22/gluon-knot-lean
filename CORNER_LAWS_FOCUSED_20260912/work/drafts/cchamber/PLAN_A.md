# PLAN A — prop:C-chamber (chamber constancy of the corner state sum)

Target: `work/drafts/CChamber_statement.lean` (`SM.C_chamber : CChamberData`), source
reference/SM/sm-4-knotlaws.tex:36-99. Skeleton: `work/drafts/cchamber/Skeleton_A.lean`
(570 lines; typechecks with `lake env lean`, 61 `sorry` obligations, `C_chamber` proved from the
chain). Tag A emphasis: reuse the accepted geometric-records transport machinery
(`crossingTransport`/`visitTransport`/`markTransport`, `CrossingParameterOrderAgrees`,
`geometric_visitKey_lt_transport`, `geometric_interlaces_transport`, persistence lemmas) so that
the carrier correspondence across polygons costs one abstract structure (`MarkEquiv`) plus purely
combinatorial lemmas; keep new *geometric* lemmas to: continuity of the transported corners,
constancy of signs along a path, the `Deform` of positive diagrams, and one `Reparam` (cyclic
relabelling).

## 0. The route in one paragraph

Two polygons `P, Q` whose marked traversal circles (`Carrier.markCycle`: original vertices +
crossing visits in traversal order, a `Cycle`) correspond under a bijection `e` of marks that is
induced by a bijection of crossings/visits/vertex-labels and carries independent supports to
independent supports (`MarkEquiv`) have literally corresponding carriers: `smoothingSuccessor`
commutes with `e` (because `selectedMarkPerm` does and `markSuccessor` is `Cycle.next` of the
marked circle), so `Component` transports (`Quotient.congr`), owners/true corners/corner cycles
transport, retained crossings transport, and the corner polygon of the transported carrier agrees
— up to a cyclic relabelling `shift m` (the cut of the corner list at label zero may move) — with
the *transported corner tuple* `E.cornerTuple S q := j ↦ eval_Q (e (corner_j of q))`. All four
per-carrier invariants that enter `def:C` (rotation `r_Q`, `m_Q`, uniformity, the coefficient of
`H⁺_Q`) are invariant under `shift` (`rotationNumber_shift`, `turn_shift`, and a `Reparam` for the
positive diagram), so `C(Q) = C(P)` once the transported corner tuples have the rotation,
uniformity and `homfly` of the original carriers (`cornerStateSum_eq_of_markEquiv`). Two
instances: (i) along a continuous family `F : unitInterval → GenericTuple n`, `markTransport`
(accepted) is a `MarkEquiv` from `F 0` to `F t` (crossing set constant and same-edge parameter
orders constant, `SM.chambers`; the marked circle is then transported *in order*), the transported
corner tuple `cornerFamily t` is continuous in `t`, regular, so its rotation is constant
(`rotationNumber_family_constant`), its turn signs are constant (continuous nonzero determinants),
and the positive diagrams along the family form a `Deform` (same strand labels, same crossing
pairs by persistence + connectedness, over data kept, positivity by sign constancy), so `homfly`
is constant (`homfly_planar`); (ii) for the cyclic shift `shift a P`, `crossingShiftEquiv`/
`visitShiftEquiv` give a `MarkEquiv` (marked circle rotated: `sorted_map_cut_rotation`) whose
transported corner tuple *is* the old corner polygon. Finally `C` is locally constant on
`GenericTuple n` (labelled chambers open + path connected), cyclically invariant, hence descends to
a locally constant `polygonStateSum` on `GenericPolygon n`, constant on connected components.

## 1. Dependency order (numbers = order of proving; ⟵ = uses)

```
0  TupleAgree.{eq, rotationNumber_eq, regular_iff, uniform_iff, polyComp_eq}
1  MarkEquiv.ev_twin ⟵ visitTwin_unique
2  MarkEquiv.selectedMarkPerm_comm ⟵ 1, selectedVisitTwin_of_mem/_of_not_mem, mem_support
3  MarkEquiv.cycle_next_map (pure Cycle lemma)
4  MarkEquiv.succ ⟵ 3, E.cycle
5  MarkEquiv.smoothingSuccessor_comm ⟵ 2, 4
6  MarkEquiv.smoothingSuccessor_eq ⟵ 5
7  MarkEquiv.sameCycle_iff ⟵ 6 (permCongrHom, map_zpow)
   MarkEquiv.component (def) ⟵ 7 ; component_owner (rfl)
8  MarkEquiv.isTrueCorner_iff ⟵ mem_support, ev_fst
9  MarkEquiv.componentCycle_map ⟵ E.cycle, component_owner (Cycle.filter_map)
10 MarkEquiv.componentCornerCycle_map ⟵ 9, 8
11 MarkEquiv.ccpCornerList_rotated ⟵ 10 (ccpCornerList_coe, Cycle.coe_eq_coe, Cycle.map_coe)
12 MarkEquiv.ccpCornerCount_eq ⟵ 11
13 MarkEquiv.cornerPolygon_agree ⟵ 11, 12 (List.getElem_rotate, getElem_map)
14 MarkEquiv.carrierCrossings_map ⟵ component_owner, ev_fst, mem_support
15 MarkEquiv.carrierCrossingCount_eq ⟵ 14
16 uniformTurns_shift ; 17 single_generic_shift ; 18 crossingGeometry_of_single_generic
19 homfly_positiveDiagram_shift (Reparam)        [RISK 1]
20 MarkEquiv.carrierRotation_eq ⟵ 13, 0, rotationNumber_shift
21 MarkEquiv.carrierUniform_iff ⟵ 13, 0, 16
22 MarkEquiv.cornerTuple_generic ⟵ 13, 0, 17, carrierShadow_generic
23 MarkEquiv.cornerHomfly_eq ⟵ 13, 0, 19, homfly_positiveDiagram_congr
24 MarkEquiv.cornerSlot_eq ⟵ 15, 20 ; 25 cornerCoefficient_eq ⟵ 23, 24
26 MarkEquiv.cornerProduct_eq ⟵ 25 (Fintype.prod_equiv E.component)
27 MarkEquiv.uniformDecomposition_iff ⟵ 21 ; 28 uniformDecompositions_eq ⟵ 27, E.indep
29 cornerStateSum_eq_of_markEquiv ⟵ 26, 28, card_support
30 markTransport_key_lt_iff ⟵ geometric_visitKey_lt_transport, traversalKey_lt_iff
31 markList_transport ⟵ 30 (List.Perm.eq_of_pairwise)
32 isDecomposition_transport ⟵ geometric_interlaces_transport
   transportMarkEquiv (def) ⟵ 31, 32 ; markTransport_self
33 cornerFamily_continuous ⟵ generic_family_edgeParameter_continuous, continuous_vertex
34 cornerFamily_zero ⟵ markTransport_self
35 cornerFamily_regular ⟵ 13, 0, regular_shift, ccpCornerPolygon_regular
36 cornerFamily_rotation ⟵ 33, 35, rotationNumber_family_constant, 34
37 cornerFamily_turn ⟵ 33, 35, turn_det, continuousAt_sign_of_ne_zero, PreconnectedSpace.constant
38 cornerFamily_uniform_iff ⟵ 37 ; 39 cornerFamily_generic ⟵ 22
40 cornerFamily_isCrossing_iff ⟵ 18, 39, crossing_support_persists_of_geometry   [RISK 2]
41 cornerFamily_det_sign ⟵ 33, 39 (transverse), 40
42 cornerFamily_deform ⟵ 33, 39, 40, 41, eq_positiveDiagram_of_isPositive          [RISK 2]
43 cornerFamily_homfly ⟵ 42, homfly_planar, 34, homfly_positiveDiagram_congr
44 family_leftTurns ⟵ generic_family_chi_constant
45 cornerStateSum_family ⟵ 29 with E := familyMarkEquiv, 36, 38, 43, 44
46 cornerStateSum_path ⟵ 45, Path.source/target
47 markPosition_shiftMark ⟵ visitPosition_shift ; 48 markList_shift_rotated ⟵ 47, sorted_map_cut_rotation
   shiftMarkEquiv (def) ⟵ 48, independentSupports_shift
49 shiftMarkEquiv_cornerTuple ⟵ 47, traversalEvaluation_shift
50 cornerStateSum_shift ⟵ 29 with E := shiftMarkEquiv, 49, leftTurns_shift, carrierShadow = single
51 cornerStateSum_locallyConstant ⟵ 46, labelledChambers_open_pathConnected
52 cornerStateSum_cyclic ⟵ 50 ; polygonStateSum (def) ⟵ 52
53 polygonStateSum_locallyConstant ⟵ 51 (IsLocallyConstant.iff_continuous + continuous_quotient_lift, or isOpen_coinduced)
54 C_chamber ⟵ 53, IsLocallyConstant.apply_eq_of_isPreconnected  (PROVED in the skeleton)
```

## 2. Every lemma: statement, sketch, estimate

Notation as in the skeleton: `hn : 3 ≤ n`, `[NeZero n]`, `hP : Generic P`, `hQ : Generic Q`,
`E : MarkEquiv hn hP hQ`, `E.e := Equiv.sumCongr E.eV E.ev : Mark P ≃ Mark Q`,
`E.support S := S.map E.ec.toEmbedding`.

### Part 0 — `TupleAgree` (index-free comparison of tuples of equal size)  [~36 lines]

`def TupleAgree {k k'} (T : LabelledTuple k) (T' : LabelledTuple k') : Prop := k = k' ∧ ∀ j : ℕ, T (j : ZMod k) = T' (j : ZMod k')`

- `TupleAgree.eq [NeZero k] {T T' : LabelledTuple k} (h : TupleAgree T T') : T = T'` — funext `j`, rewrite `j = ((j.val : ℕ) : ZMod k)` (`ZMod.natCast_zmod_val`), apply `h.2`. (8)
- `TupleAgree.rotationNumber_eq [NeZero k] [NeZero k'] (h) : rotationNumber T = rotationNumber T'` — `obtain ⟨rfl, _⟩ := h; rw [h.eq]`. (6)
- `TupleAgree.regular_iff`, `TupleAgree.uniform_iff` (`(∃ τ ≠ 0, ∀ j, turn T j = τ) ↔ (∃ τ ≠ 0, ∀ j, turn T' j = τ)`) — same pattern. (6+6)
- `TupleAgree.polyComp_eq (hk : 3 ≤ k) (hk' : 3 ≤ k') (h) : (⟨k, hk, T⟩ : PolyComp) = ⟨k', hk', T'⟩` — `obtain ⟨rfl, _⟩`, `haveI : NeZero k := ⟨by omega⟩`, `congr 1; exact h.eq`. (10)

### Part 1 — `MarkEquiv` and its combinatorial consequences  [~224 lines]

```
structure MarkEquiv (hn) (hP : Generic P) (hQ : Generic Q) where
  ec : Crossing P ≃ Crossing Q
  ev : Visit P ≃ Visit Q
  ev_fst : ∀ v, (ev v).1 = ec v.1
  eV : ZMod n ≃ ZMod n
  cycle : (markCycle hn hP).map (Equiv.sumCongr eV ev) = markCycle hn hQ
  indep : ∀ S, IsDecomposition hn hQ (S.map ec.toEmbedding) ↔ IsDecomposition hn hP S
```
(Proved inline: `mem_support` = `Finset.mem_map'`, `card_support` = `Finset.card_map`, `decomposition`, `e_inl/e_inr` rfl, `component_owner` rfl.)

1. `ev_twin (v) : E.ev (visitTwin v) = visitTwin (E.ev v)` — `visitTwin_unique (E.ev v) (E.ev (visitTwin v))`: same crossing by `ev_fst` twice + `visitTwin_crossing`; distinct by `E.ev.injective` + `visitTwin_ne`. (12)
2. `selectedMarkPerm_comm (S a) : E.e (selectedMarkPerm S a) = selectedMarkPerm (E.support S) (E.e a)` — `cases a`; vertex: rfl; visit `v`: `by_cases hv : v.1 ∈ S`, rewrite `selectedVisitTwin_of_mem/_of_not_mem` on both sides using `mem_support` + `ev_fst` (`(E.ev v).1 = E.ec v.1 ∈ E.support S ↔ v.1 ∈ S`), then `ev_twin`. (15)
3. `cycle_next_map (f injective) (s : Cycle α) (hs hs' a ha ha') : (s.map f).next hs' (f a) ha' = f (s.next hs a ha)` — `induction s using Quotient.inductionOn`; on a list `l`: `Cycle.map_coe`, `Cycle.next` on `↑l` is `List.next`; write `a = l[i]` (`List.mem_iff_getElem`), `List.next_getElem` on both sides, `List.getElem_map`. (25)
4. `succ (a) : E.e (markSuccessor hn hP a) = markSuccessor hn hQ (E.e a)` — unfold `markSuccessor_apply, nextMark`; `markCycle hn hQ = (markCycle hn hP).map E.e` (`E.cycle.symm`, needs a `Cycle.next` congruence lemma along an equality of cycles — `subst`-style helper `cycle_next_congr`); then lemma 3 with `E.e.injective`. (15)
5. `smoothingSuccessor_comm (S a)` — `smoothingSuccessor = (selectedMarkPerm S).trans markSuccessor`; `simp [Equiv.trans_apply, E.selectedMarkPerm_comm, E.succ]`. (6)
6. `smoothingSuccessor_eq (S) : smoothingSuccessor hn hQ (E.support S) = E.e.permCongr (smoothingSuccessor hn hP S)` — `Equiv.ext`; `Equiv.permCongr_apply`; take `b = E.e a`, use 5 and `Equiv.symm_apply_apply`. (8)
7. `sameCycle_iff (S a b) : (ρ_S).SameCycle a b ↔ (ρ_{S'}).SameCycle (E.e a) (E.e b)` — rewrite 6; `SameCycle` is `∃ i : ℤ, (f ^ i) x = y`; `(E.e.permCongr f) ^ i = E.e.permCongr (f ^ i)` via `Equiv.permCongrHom E.e` and `map_zpow`; then `Equiv.permCongr_apply`, `Equiv.symm_apply_apply`, `E.e.injective.eq_iff`. (20)
   - `component (S) : Component hn hP S ≃ Component hn hQ (E.support S) := Quotient.congr E.e (E.sameCycle_iff S)` (def, compiles).
8. `isTrueCorner_iff (S a) : IsTrueCorner (E.support S) (E.e a) ↔ IsTrueCorner S a` — `cases a`; vertex trivial; visit: `isTrueCorner_visit`, `ev_fst`, `mem_support`. (6)
9. `componentCycle_map (S q) : (componentCycle hn hP S q).map E.e = componentCycle hn hQ (E.support S) (E.component S q)` — unfold `componentCycle` (filter of `markCycle` by `owner = q`); `Cycle.filter_map`; rewrite `E.cycle`; the predicates agree: `owner hQ S' (E.e m) = E.component S q ↔ owner hP S m = q` by `component_owner` and `(E.component S).injective.eq_iff` (as in `geoComponentMarkList_eq_generic`, FlatCarriersDefs.lean:688). Needs a `Cycle.filter_congr` (prove via `Quotient.inductionOn` + `List.filter_congr`). (20)
10. `componentCornerCycle_map` — `componentCornerCycle = componentCycle.filter IsTrueCorner`; `Cycle.filter_map`, 9, 8. (12)
11. `ccpCornerList_rotated (S q) : ((ccpCornerList hn hP S q).map E.e).IsRotated (ccpCornerList hn hQ S' q')` — `Cycle.coe_eq_coe.mp`: `↑((L).map e) = Cycle.map e ↑L` (`Cycle.map_coe`) `= (componentCornerCycle P q).map e` (`ccpCornerList_coe`) `= componentCornerCycle Q q'` (10) `= ↑(ccpCornerList Q q')` (`ccpCornerList_coe`). (10)
12. `ccpCornerCount_eq` — `(IsRotated.perm 11).length_eq`, `List.length_map`. (6)
13. `cornerPolygon_agree (S q) : ∃ m : ZMod k, TupleAgree (ccpCornerPolygon hn hQ S' q') (shift m (E.cornerTuple S q))` — from 11 obtain `r` with `ccpCornerList Q q' = ((ccpCornerList P q).map E.e).rotate r`; take `m := (r : ZMod k)`; first component is 12; for `j : ℕ`: `ccpCornerPolygon Q q' (j : ZMod k') = eval_Q (markPosition (ccpCornerList Q q')[j % k'])` (`ccpCornerMark`, `ZMod.val_natCast`), `List.getElem_rotate`, `List.getElem_map`, and on the right `shift m (cornerTuple) j = cornerTuple (j + m) = eval_Q (markPosition (E.e (ccpCornerList P q)[(j + r) % k]))` (`ZMod.val_add`, `ZMod.val_natCast`); the two indices agree mod `k`. (35)
14. `carrierCrossings_map (S q) : carrierCrossings hn hQ S' q' = (carrierCrossings hn hP S q).map E.ec.toEmbedding` — `Finset.ext`; `x' = E.ec x` by surjectivity; `mem_carrierCrossings` both sides; `x ∉ S ↔ E.ec x ∉ S'` (`mem_support`); visits of `E.ec x` are `E.ev v` for the visits `v` of `x` (`ev_fst`, surjectivity of `E.ev` and `(E.ev v).1 = E.ec v.1 = E.ec x ↔ v.1 = x`); owners by `component_owner` + injectivity. (30)
15. `carrierCrossingCount_eq` — `Finset.card_map`. (4)

### Part 2 — shift invariance of the four corner-polygon invariants  [~245 lines]

16. `uniformTurns_shift (m : ZMod k) (T) : (∃ τ ≠ 0, ∀ j, turn (shift m T) j = τ) ↔ (∃ τ ≠ 0, ∀ j, turn T j = τ)` — `turn_shift` and reindexing `j ↦ j + m` (`Equiv.addRight`). (10)
17. `single_generic_shift (hk) (m) (T) : (single ⟨k, hk, shift m T⟩).Generic ↔ (single ⟨k, hk, T⟩).Generic` — one direction via `Shadow.single_generic_of` (LinkPositiveLift.lean:160): `Regular` by `regular_shift`, `tail_off`/`transverse`/`no_triple` by `edgeSegment_shift`, `edgeInterior_shift`, `edge_shift`, `shift` of labels (`incident`, `adjacent` are translation invariant: `remote_add` pattern), and the label-level facts of the other shadow extracted through `single_seg`, `single_incidentTail_iff`, `single_adjacent_iff`, `single_interior`, `single_dir`; other direction by `shift (-m)` + `shift_add`. Alternative: the `StrandMap` of 19 with `generic_pullback`. (45)
18. `crossingGeometry_of_single_generic (hk) (h : (single ⟨k,hk,T⟩).Generic) : CrossingGeometry T` — edges nonzero from `h.regular 0 i` (`RegularPair.1`); for remote `i j` and `x ∈ seg i ∩ seg j`: `det ≠ 0` from `h.transverse` (remote ⇒ ¬adjacent via `single_adjacent_iff`), interiority from `h.tail_off` (if `x` is an endpoint of `E_i` it is a vertex on the non-incident edge `E_j`; `remote` excludes incidence) — small case analysis on the parameter `t ∈ {0,1}`; `G2` from `h.no_triple` via `single_interior`. (40)
19. **`homfly_positiveDiagram_shift (hk) (m) (T) (h₁ h₂) : homfly ((single ⟨k,hk,shift m T⟩).positiveDiagram h₁) = homfly ((single ⟨k,hk,T⟩).positiveDiagram h₂)`** — build `sm : StrandMap (single ⟨k,hk,shift m T⟩) (single ⟨k,hk,T⟩)` with `toFun ⟨i, j⟩ := ⟨i, j + m⟩`, `f := id`, `sgn := 1`, `vert := toFun`; fields from `edgeSegment_shift`, `edgeInterior_shift`, `edge_shift`, label translation invariance of `adjacent`/`incident`. Then `D₂ := positiveDiagram (single T) h₂`, `D₂.pullback sm hreg` is a diagram on the shifted shadow, positive by `pullback_isPositive_iff` (sgn = 1), hence `= positiveDiagram (shifted) h₁` (`eq_positiveDiagram_of_isPositive`). Build `ReparamData (D₂.pullback sm hreg) D₂`: `e := Equiv.refl (Fin 1)`, `φ 0 := traversalShiftEquiv (-m)` (point `(j, t) ↦ (j + m, t)`), `between` from `traversalBetween_shift`, `eval_eq` from `traversalEvaluation_shift`, `over_map`/`over_surj`: the over visit of the pullback at `x` is the strand `s` with `sm.toFun s = D₂.overStrand (sm.mapCrossing x)` (`toFun_pullback_overStrand`); its `visitPt` has parameter `crossingParam`, which is the unique parameter of the (common, `crossingPoint_mapCrossing` with `f = id`) crossing point on that edge (`edgePoint_injective`, edge nonzero), so `φ (visitPt (overVisit x)) = visitPt (overVisit (mapCrossing x))`; surjectivity of `mapCrossing` (`mapCrossing_surjective`, `toFun` surjective). Conclude `homfly_planar (PlanarIsotopic.of_reparam ⟨r⟩)`. Template: `ReparamData.reverse` (LinkMoves.lean:2385). (150)

### Part 2' — invariants of the transported carrier  [~50 lines]

20. `carrierRotation_eq (S hS q) : carrierRotation hn hQ S' q' = rotationNumber (E.cornerTuple S q)` — 13 gives `m` with `TupleAgree (ccpCornerPolygon Q q') (shift m cornerTuple)`; `TupleAgree.rotationNumber_eq`, `rotationNumber_shift`. (`carrierRotation = rotationNumber ∘ ccpCornerPolygon`.) (10)
21. `carrierUniform_iff (S hS q)` — `CarrierUniform` unfolds to the `∃ τ` form; `TupleAgree.uniform_iff`, 16. (10)
22. `cornerTuple_generic (S hS q) : (single ⟨_, ccpCornerCount_ge_three hn hP hS q, E.cornerTuple S q⟩).Generic` — `carrierShadow_generic hn hQ S' q' (E.decomposition hS)` is `(single (carrierPolyComp ..)).Generic`; `TupleAgree.polyComp_eq` rewrites the `PolyComp` to `⟨k, hk, shift m cornerTuple⟩`; then 17. (15)
23. `cornerHomfly_eq (S hS q) : cornerHomfly hn hQ S' q' (E.decomposition hS) = homfly ((single ⟨_, _, E.cornerTuple S q⟩).positiveDiagram (E.cornerTuple_generic S hS q))` — `cornerHomfly = homfly (positiveLift ..) = homfly ((carrierShadow ..).positiveDiagram _)` (rfl); `homfly_positiveDiagram_congr` with the `PolyComp` equality of 22; then 19. (15)

### Part 3 — assembly  [~119 lines]

24. `cornerSlot_eq (S hS q) (hrot : rotationNumber (E.cornerTuple S q) = carrierRotation hn hP S q) : cornerSlot hn hQ S' q' = cornerSlot hn hP S q` — `cornerSlot = 1 - m_Q - |round r_Q|`; 15 and `carrierRotationInt = round carrierRotation`, 20, `hrot`. (10)
25. `cornerCoefficient_eq (S hS q) (hrot) (hhom : ∀ h, homfly ((single ⟨_,_,E.cornerTuple S q⟩).positiveDiagram h) = cornerHomfly hn hP S q hS) : cornerCoefficient hn hQ S' q' (E.decomposition hS) = cornerCoefficient hn hP S q hS` — `cornerCoefficient_eq_coeffAt`, 24, 23, `hhom _`. (12)
26. `cornerProduct_eq (S hS) (hrot : ∀ q, …) (hhom : ∀ q h, …) : cornerProduct hn hQ S' (E.decomposition hS) = cornerProduct hn hP S hS` — `Fintype.prod_equiv (E.component S)` with 25. (12)
27. `uniformDecomposition_iff (S hS) (huni : ∀ q, (∃ τ …cornerTuple…) ↔ CarrierUniform hn hP S q) : UniformDecomposition hn hQ S' ↔ UniformDecomposition hn hP S` — `∀ q'` over `Component Q S'` via `(E.component S).forall_congr_left`, 21, `huni`. (15)
28. `uniformDecompositions_eq (huni : ∀ S hS q, …) : uniformDecompositions hn hQ = (uniformDecompositions hn hP).map (Finset.mapEmbedding E.ec.toEmbedding).toEmbedding` — `Finset.ext`; every `S' = E.support S` (`Finset.map` surjective onto by `E.ec.symm`); `mem_uniformDecompositions` both sides; `E.indep`; 27 (uniformity only needed when `S` is a decomposition, which both sides provide). (25)
29. `cornerStateSum_eq_of_markEquiv (E) (hL : leftTurns Q = leftTurns P) (hrot) (huni) (hhom) : cornerStateSum hn hQ = cornerStateSum hn hP` — unfold; `hL`; convert both attached sums to sums of a total function `g` over `uniformDecompositions` (`Finset.sum_attach`, the `dite` device of `cornerStateSum_eq_sum_independentSupports`, CornerStateSum.lean); rewrite 28 and `Finset.sum_map`; termwise: `card_support`, 26. (45)

### Part 4 — paths  [~443 lines]

Section `Transport` (variables `hs : ∀ s, IsCrossing P s ↔ IsCrossing Q s`, `ho : CrossingParameterOrderAgrees P Q`):

30. `markTransport_key_lt_iff (a b) : markKey hn hP.1 a < markKey hn hP.1 b ↔ markKey hn hQ.1 (markTransport hs a) < markKey hn hQ.1 (markTransport hs b)` — `markKey = traversalKey ∘ markPosition`; `traversalKey_lt_iff` (Traversal.lean:46): edge label comparison first (labels preserved: `visitTransport_edge`, vertices fixed), then parameters on a common edge: vertex/vertex trivial, vertex/visit (0 < param, both sides), visit/visit = `geometric_visitParameterOrder` (GeometricTransport.lean:14) with `generic_crossingGeometry`; or directly `geometric_visitKey_lt_transport` + `geometricVisitKey_eq_generic`. (35)
31. `markList_transport : (markList hn hP).map (markTransport hs) = markList hn hQ` — `List.Perm.eq_of_pairwise` (antisymmetry `markKey_injective`), sortedness of the mapped list from `markList_sorted` + 30 (`List.pairwise_map`), `List.perm_ext_iff_of_nodup` (`markList_nodup`, `Nodup.map`, `mem_markList`); pattern `geoMarkList_eq_generic` (FlatCarriersDefs.lean:644). (20)
32. `isDecomposition_transport (S) : IsDecomposition hn hQ (transportSupport hs S) ↔ IsDecomposition hn hP S` — `mem_independentSupports_iff` both sides; `geometric_interlaces_transport` (GeometricInterlacement.lean:69) + `geometricInterlaces_iff_generic` (:36) with `generic_crossingGeometry`; `Finset.mem_map'`/surjectivity of `crossingTransport`. (20)
   - `transportMarkEquiv : MarkEquiv hn hP hQ` — `ec := crossingTransport hs`, `ev := visitTransport hs`, `ev_fst := rfl`, `eV := refl`, `cycle` from 31 (`Cycle.map_coe`, `congrArg`), `indep := 32`. `transportMarkEquiv_e : … .e = markTransport hs` (rfl, since `markTransport := Equiv.sumCongr (Equiv.refl _) (visitTransport hs)`). (6)
- `markTransport_self (hs : ∀ s, IsCrossing P s ↔ IsCrossing P s) (a) : markTransport hs a = a` — `cases a`; visit: `Sigma.ext`/`Subtype.ext` rfl. (6)

Section `Family` (`F : unitInterval → GenericTuple n`, `hF : Continuous F`; `family_crossing_iff`, `family_order_agrees` proved from `SM.chambers`' ingredients; `familyMarkEquiv t := transportMarkEquiv …`; `cornerFamily S q t := (familyMarkEquiv t).cornerTuple S q : LabelledTuple k`, `k = ccpCornerCount hn (F 0).2 S q`):

33. `cornerFamily_continuous : Continuous (cornerFamily hn hF S q)` — `continuous_pi`; fix `j`, `a := ccpCornerMark (F 0) q j`; `cases a`: vertex `i`: `t ↦ (F t).1 i` (`continuous_apply ∘ continuous_subtype_val ∘ hF`); visit `v` with `v.1.val = {i, j'}` (`crossing_support_partner`): the value is `crossingPoint (crossingTransport (hs t) v.1) = edgePoint (F t) i (edgeParameter (F t) i j')` (`visitPosition_evaluation`, `crossingParameter_eq_of_support_pair`), continuous by `generic_family_edgeParameter_continuous` (ChamberPaths.lean:26), `continuous_vertex`, `continuous_edge`. (45)
34. `cornerFamily_zero : cornerFamily hn hF S q 0 = ccpCornerPolygon hn (F 0).2 S q` — funext; `markTransport_self`; `ccpCornerPolygon_apply`. (12)
35. `cornerFamily_regular (hS) (t) : Regular (cornerFamily t)` — 13 for `familyMarkEquiv t` gives `m`, `TupleAgree.regular_iff`, `ccpCornerPolygon_regular` at `F t` (decomposition by `E.decomposition hS`), `regular_shift`. (12)
36. `cornerFamily_rotation (hS) (t) : rotationNumber (cornerFamily t) = carrierRotation hn (F 0).2 S q` — `rotationNumber_family_constant` (RotationContinuity.lean) with 33, 35, `PreconnectedSpace unitInterval`; at `t = 0` use 34. (10)
37. `cornerFamily_turn (hS) (t) (j) : turn (cornerFamily t) j = turn (ccpCornerPolygon (F 0) q) j` — `turn_det`; `t ↦ det (edge (cF t) (j-1)) (edge (cF t) j)` continuous (33), nonzero for all `t` (`turn ≠ 0`: 13 + `ccpCornerPolygon_turn_ne_zero` at `F t` + `turn_shift`), so `sign ∘ det` is continuous (`continuousAt_sign_of_ne_zero`) hence constant (`PreconnectedSpace.constant`); 34 at `t = 0`. Pattern: `generic_family_crossingOrder_constant`. (35)
38. `cornerFamily_uniform_iff (hS) (t)` — 37 + `CarrierUniform` unfolding. (12)
39. `cornerFamily_generic (hS) (t) : (single ⟨_, _, cornerFamily t⟩).Generic` — 22. (10)
40. **`cornerFamily_isCrossing_iff (hS) (t) (s) : IsCrossing (cornerFamily t) s ↔ IsCrossing (cornerFamily 0) s`** — the map `t ↦ {s | IsCrossing (cornerFamily t) s}` is locally constant: at `t₀`, `crossing_support_persists_of_geometry (18 (39 t₀))` gives a neighbourhood of `cornerFamily t₀` in `LabelledTuple k` on which crossing supports agree; pull back along 33 (`ContinuousAt.eventually`); `IsLocallyConstant.iff_exists_open` + `IsLocallyConstant.apply_eq_of_preconnectedSpace` (values in `Set (Finset (ZMod k))`). (40)
41. `cornerFamily_det_sign (hS) (t) (a b) (hab : IsCrossing (cornerFamily 0) {a, b}) : sign (det (edge (cF t) a) (edge (cF t) b)) = sign (det (edge (cF 0) a) (edge (cF 0) b))` — det continuous (33), nonzero at every `t` (`(39 t).transverse` through `single_adjacent_iff`/`single_seg`/`single_dir`, using 40 to know `{a,b}` is a crossing at `t`), sign constant as in 37. (30)
42. **`cornerFamily_deform (hS) (t) : Deform (D₀) (D_t)`**, `D_r := (single ⟨k, hk, cornerFamily r⟩).positiveDiagram (39 r)` — `DeformData D₀ D_t` with `γ r := fun _ => cornerFamily (Set.projIcc 0 1 zero_le_one (r * t))`; `continuous`: 33 ∘ `continuous_projIcc` ∘ `continuous_mul_const`; `start`: `Set.projIcc_of_mem` (`0 * t = 0`) + `D₀.Γ.vertices = fun _ => cornerFamily 0` (rfl); `generic`: `withVertices (single C) (fun _ => V) = single ⟨k, hk, V⟩` (rfl) then 39; `crossings`: `single_isCrossing_iff` both sides + 40; `stop`: `D_t = D₀.deform (γ 1) _ _` by `eq_positiveDiagram_of_isPositive` — shadow equality rfl (after `1 * t = t`, `projIcc_of_mem`), positivity: the over strand of the deformed diagram at `x` is `D₀.overStrand ⟨x.val, _⟩`, so `IsPositive` there is `0 < det (dir over) (dir under)` evaluated on `cornerFamily t`; the under strand is `other`, which is label-determined (`eq_pair_other`); the pair is a crossing of `cornerFamily 0` (40), so by 41 the sign equals the sign at `0`, which is `+1` (`positiveDiagram_isPositive`). (90)
43. `cornerFamily_homfly (hS) (t) (h) : homfly ((single ⟨_,_,cornerFamily t⟩).positiveDiagram h) = cornerHomfly hn (F 0).2 S q hS` — `homfly_planar (PlanarIsotopic.of_deform (42 t))` (proof-irrelevant `h` via `homfly_positiveDiagram_congr rfl`), and `homfly D₀ = cornerHomfly` by `homfly_positiveDiagram_congr` with `carrierShadow (F 0) q = single ⟨k, hk, ccpCornerPolygon (F 0) q⟩` (rfl) and 34. (20)
44. `family_leftTurns (t) : leftTurns (F t).1 = leftTurns (F 0).1` — `leftTurns = card (filter (turn = 1))`, `turn = chi (i-1) i (i+1)`, `generic_family_chi_constant`; `Finset.filter_congr`. (12)
45. `cornerStateSum_family (t) : cornerStateSum hn (F t).2 = cornerStateSum hn (F 0).2` — 29 with `E := familyMarkEquiv hn hF t`, `hL := 44`, `hrot := 36`, `huni := 38`, `hhom := 43` (all after `cornerFamily` unfolds to `E.cornerTuple`, rfl). (20)
46. `cornerStateSum_path (γ : Path P Q) : cornerStateSum hn P.2 = cornerStateSum hn Q.2` — `45 hn γ.continuous 1`, then `simpa using` with `Path.source`/`Path.target` (motive `fun R : GenericTuple n => cornerStateSum hn R.2`, as in `rotationNumber_path_constant`). (8)

### Part 5 — cyclic relabelling  [~78 lines]

`shiftMark a := Equiv.sumCongr (Equiv.subRight a) (visitShiftEquiv a P) : Mark P ≃ Mark (shift a P)`.

47. `markPosition_shiftMark (m) : markPosition hn hQ.1 (shiftMark a m) = traversalShift a (markPosition hn hP.1 m)` — `cases m`; vertex: rfl (`(i - a, 0)`); visit: `visitPosition_shift` (VisitRelabel/GaussVisits). (10)
48. `markList_shift_rotated : ((markList hn hP).map (shiftMark a)).IsRotated (markList hn hQ)` — `sorted_map_cut_rotation` (SortedCut.lean:9) with `k := markKey hP`, `t := markKey hQ`, `N := n`, `a := a.val`; injectivity `markKey_injective`; sortedness `markList_sorted`; permutation by `List.perm_ext_iff_of_nodup` + `mem_markList` + bijectivity; bounds `traversalKey_nonneg`/`traversalKey_lt_size`; the key law from 47 + `traversalKey_shift`. Pattern: `gaussList_shift_rotation` (GaussRelabel.lean:27). (30)
   - `shiftMarkEquiv : MarkEquiv hn hP hQ` — `ec := crossingShiftEquiv a P`, `ev := visitShiftEquiv a P`, `ev_fst := rfl` (`visitShift_crossing`), `eV := Equiv.subRight a`, `cycle` from 48 (`Cycle.coe_eq_coe.mpr`, `Cycle.map_coe`), `indep := independentSupports_shift hn hP a` (`crossingSupportShift a S = S.map (crossingShiftEquiv a P).toEmbedding` definitionally). (6)
49. `shiftMarkEquiv_cornerTuple (S q) : (shiftMarkEquiv hn hP a).cornerTuple S q = ccpCornerPolygon hn hP S q` — funext; 47; `traversalEvaluation_shift` (Traversal.lean:89). (12)
50. `cornerStateSum_shift : cornerStateSum hn hQ = cornerStateSum hn hP` — 29 with `E := shiftMarkEquiv`, `hL := leftTurns_shift`, `hrot`/`huni` by rewriting 49 (`carrierRotation`, `CarrierUniform` unfold), `hhom`: after 49 the diagram is `(single ⟨k, hk, ccpCornerPolygon P q⟩).positiveDiagram h = positiveLift hn hP S q hS` up to the proof argument (`homfly_positiveDiagram_congr rfl`). (20)

### Part 6 — descent  [~44 lines]

51. `cornerStateSum_locallyConstant : IsLocallyConstant (fun R : GenericTuple n => cornerStateSum hn R.2)` — `IsLocallyConstant.iff_exists_open`: for `R`, take `U := labelledChamber R` (open, path connected: `labelledChambers_open_pathConnected hn R`), `R ∈ U` (`mem_connectedComponent`); for `R' ∈ U`, `(hpc.joinedIn R hR R' hR').joined.somePath : Path R R'`, then 46. (20)
52. `cornerStateSum_cyclic (R R') (h : ∃ k, R'.1 = shift k R.1) : cornerStateSum hn R.2 = cornerStateSum hn R'.2` — `obtain ⟨k, hk⟩`; `R' = ⟨shift k R.1, _⟩` (`Subtype.ext`); 50 (proof-irrelevance of the `Generic` argument: rewrite via `congrArg (fun R : GenericTuple n => cornerStateSum hn R.2)`). (12)
   - `polygonStateSum := Quotient.lift (fun R => cornerStateSum hn R.2) (fun R R' h => 52 R R' h)` (compiles: `genericCyclicSetoid = (cyclicSetoid n).comap Subtype.val` unfolds to `∃ k, R'.1 = shift k R.1`); `polygonStateSum_mk` rfl.
53. `polygonStateSum_locallyConstant : IsLocallyConstant (polygonStateSum hn)` — `IsLocallyConstant.iff_continuous` (ℤ discrete) both for `f` and for the lift; `continuous_quotient_lift` (or `isOpen_coinduced` on each fiber: `mk ⁻¹' (g ⁻¹' s) = f ⁻¹' s`). (12)
54. `C_chamber` — PROVED in the skeleton: `IsLocallyConstant.apply_eq_of_isPreconnected (53) isPreconnected_connectedComponent mem_connectedComponent h`, then `polygonStateSum_mk`.

### Totals

Proof lines to write ≈ 36 + 224 + 245 + 50 + 119 + 443 + 78 + 44 ≈ **1240**; with the 570 skeleton
lines of statements/docstrings the finished file is ≈ 1300–1400 lines (could be split into
`CChamberTransport.lean` (Parts 0–3), `CChamberPath.lean` (4), `CChamberShift.lean` (5, 19),
`CChamber.lean` (6)). 61 `sorry` obligations; 85 declarations in the chain.

## 3. Reuse list (file:line, all accepted unless marked)

Chambers / paths
- `SM.chambers` ChamberPaths.lean:73; `generic_family_chi_constant` :9, `generic_family_crossing_constant` :13, `generic_family_edgeParameter_continuous` :26, `generic_family_crossingOrder_constant` :38.
- Chambers.lean: `GenericTuple` :14, `genericCyclicSetoid` :16, `GenericPolygon` :19, `polygonProjection` :21, `labelledChamber` :24, `chamber` :28, `labelledChambers_open_pathConnected` :46, `continuous_generic_chi` :54, `crossing_iff_of_chi_eq` :73, `edgeParameter` :87, `crossingParameter_eq_edgeParameter` :110.
- GenericTopology.lean: `continuous_vertex` :12, `continuous_edge` :15, `generic_persists` :115, `isOpen_Generic` :134. GenericCurveChamber.lean:10 (connectivity-argument pattern).

Geometric-records transport (the tag-A core reuse)
- CrossingTransport.lean: `crossingTransport` :12, `visitTransport` :18, `visitTransport_crossing` :24, `visitTransport_edge` :27, `crossing_support_partner` :30, `crossingParameter_eq_of_support_pair` :41, `visitParameter_eq_of_support_pair` :52.
- GeometricTransport.lean: `CrossingParameterOrderAgrees` :10, `geometric_visitParameterOrder` :14, `geometric_visitKey_lt_transport` :30, `geometric_visitKey_le_transport` :42.
- GeometricRecords.lean: `geometricGaussList_transport` :35 (pattern), `GeometricRecordsAgree` :55, `geometric_records_persist` :63.
- GeometricVisits.lean: `geometricVisitPosition_eq_generic` :59, `geometricVisitKey_eq_generic` :63.
- GeometricInterlacement.lean: `geometricInterlaces_iff_generic` :36, `geometric_interlaces_transport` :69, `geometricInterlacementTransportIso` :86.
- CrossingGeometry.lean: `CrossingGeometry` :11, `generic_crossingGeometry` :24.
- GeometricCrossingStability.lean: `crossing_support_persists_of_geometry` :35. GeometricOrderStability.lean: `geometric_parameter_order_persists` :13, `geometric_crossing_signs_persist` :47.
- FlatCarriersDefs.lean (sorry-free defs): `markTransport` :536, `transportSupport` :541; proof patterns `geoMarkList_eq_generic` :644 (`List.Perm.eq_of_pairwise`), `geoComponentEquivGeneric` :676 (`Quotient.congrRight`), `geoComponentMarkList_eq_generic` :688 (`List.filter_congr`). (The transport *theorems* of that file are only stated inside the bundle structures — not proved; we prove our own.)

Carrier lane
- CarrierMarks.lean: `Mark` :31, `markPosition` :35, `markPosition_evaluation_vertex/visit` :48/:53, `markPosition_injective` :59, `markKey` :78, `markKey_injective` :88, `markList` :96, `markList_nodup` :103, `mem_markList` :109, `markList_sorted` :115.
- CarrierSuccessor.lean: `markCycle` :34, `nextMark` :49, `markSuccessor` :77, `markSuccessor_apply` :84, `markSuccessor_getElem` :93.
- CarrierVisitTwin.lean: `visitTwin` :34, `visitTwin_crossing` :38, `visitTwin_ne` :41, `visitTwin_unique` :60, `selectedVisitTwin` :80, `selectedVisitTwin_of_mem` :83, `_of_not_mem` :87.
- CarrierSmoothing.lean: `selectedMarkPerm` (+ `_vertex`, `_visit`), `smoothingSuccessor`, `Component`, `owner`, `owner_eq_iff`, `owner_surjective`, `componentFintype`.
- CarrierFilteredCycles.lean: `componentCycle` :40, `componentCycle_eq_filtered_markList` :46, `mem_componentCycle`. CarrierTrueCorners.lean: `IsTrueCorner` :44, `isTrueCorner_visit`, `componentCornerCycle` :84, `componentCornerCycle_nodup`. CarrierClosedTrace.lean: `componentMarkList` :59.
- CarrierCornerPolygon.lean: `ccpCornerList` :317, `ccpCornerList_coe` :321, `ccpCornerCount` :341, `ccpCornerCount_neZero` :345, `ccpCornerMark` :350, `ccpCornerPolygon` :357, `ccpCornerPolygon_apply` :361, `ccpCornerPolygon_turn_ne_zero` :579, `ccpCornerPolygon_regular` :679, `ccpCornerCount_ge_three` :691.
- CarrierCrossings.lean: `carrierCrossings` :56, `carrierCrossingCount` :62, `mem_carrierCrossings` :66.
- UniformDefinition.lean: `CarrierUniform` :27, `UniformDecomposition` :37, `carrierRotation` :42. DecompositionDefinition.lean: `IsDecomposition` :15. InterlaceSupports.lean: `mem_independentSupports_iff` :39, `crossingSupportShift` :76, `independentSupports_shift` :83. InterlaceRelabel.lean: `interlaces_shift` :31.
- CornerStateSum.lean: `carrierRotationInt`, `carrierRotationInt_cast`, `cornerSlot`, `cornerHomfly`, `cornerCoefficient`, `cornerCoefficient_eq_coeffAt`, `uniformDecompositions`, `mem_uniformDecompositions`, `cornerProduct`, `cornerStateSum`, `cornerStateSum_eq_sum_independentSupports` (the `dite` sum device).

Rotation / chirotope / regular locus
- RotationContinuity.lean: `continuous_rotationNumber_family`, `rotationNumber_family_constant`, `rotationNumber_path_constant`. RotationNumber.lean: `rotationNumber` :10, `rotationNumber_integer` :45, `rotationNumber_shift` :53. RegularLocus.lean: `Regular` :12, `regular_shift` :61, `principalTurn_shift` :68.
- Chirotope.lean: `chi` :10, `turn` :13, `leftTurns` :16, `turn_det` :87, `chi_shift` :100, `turn_shift` :103, `leftTurns_shift` :107.

Traversal / relabelling
- Traversal.lean: `TraversalPoint` :12, `traversalEvaluation` :14, `traversalKey` :17, `traversalKey_lt_iff` :46, `traversalShift` :86, `traversalEvaluation_shift` :89. TraversalRelabel.lean: `traversalShiftEquiv` :10, `traversalKey_nonneg` :16, `traversalKey_lt_size` :19, `traversalKey_shift` :61, `traversalBetween_shift` :74.
- Polygon.lean: `shift` :21, `shift_add` :29, `cyclicSetoid` :34, `edge_shift` :71, `edgePoint_shift` :75, `edgeSegment_shift`. Generic.lean: `edgeInterior_shift` :21, `generic_shift` :45, `G1` :11, `G2` :14.
- CrossingEquiv.lean: `crossingShiftEquiv` :36, `mem_crossingShift` :48, `crossingPoint_shift` :52, `crossingParameter_shift` :60, `crossingSign_shift` :72, `remote_add` :16. VisitRelabel.lean: `visitShiftEquiv` :18, `visitShift_crossing` :24, `visitKey_shift` :30 (uses `visitPosition_shift`). GaussRelabel.lean: `gaussList_shift_rotation` :27 (pattern). SortedCut.lean: `sorted_map_cut_rotation` :9.

Link layer
- LinkDiagram.lean: `PolyComp` :61, `Shadow` :83, `Strand` :96, `seg/interior/dir` :99-106, `Adjacent` :142, `IncidentTail` :147, `IsCrossing` :246, `Crossing` :251, `other` :315, `eq_pair_other` :325, `crossingPoint` :372, `Generic` :394, `Diagram` :490, `IsPositive` :547, `sign` :552, `StrandMap` :752, `isCrossing_map_iff`, `mapCrossing` :815, `other_mapCrossing`, `crossingPoint_mapCrossing`, `generic_pullback`, `mapCrossing_surjective`, `crossingEquiv` :895, `Diagram.pullback` :910, `toFun_pullback_overStrand`, `pullback_isPositive_iff`, `crossingParam` :1413, `visitPt` :1435, `Shadow.single` :1589, `singleStrandEquiv` :1594, `single_adjacent_iff` :1614, `single_incidentTail_iff` :1622, `single_seg` :1630, `single_interior`, `single_dir`, `single_isCrossing_iff` :1640, `singleCrossingEquiv` :1659, `single_crossingPoint`, `single_generic_of_generic`.
- LinkMoves.lean: `Shadow.Vertices` :217, `vertices` :220, `withVertices` :224, `ReparamData` :370, `Reparam` :387, `Diagram.deform` :429, `deform_overStrand` :443, `DeformData` :462, `Deform` :478, `PlanarIsotopic` :516, `PlanarIsotopic.of_reparam` :519, `.of_deform` :522; template `ReparamData.reverse` :2385, `reverse_overStrand` :2300.
- LinkPositiveLift.lean: `Shadow.positiveDiagram` :93, `positiveDiagram_isPositive` :111, `eq_positiveDiagram_of_isPositive` :128, `single_generic_of` :160, `carrierPolyComp` :211, `carrierShadow` :218, `ccpCornerPolygon_tail_off` :531, `ccpCornerPolygon_transverse` :541, `ccpCornerPolygon_no_triple` :556, `carrierShadow_generic` :580, `positiveLift` :596, `positiveLift_Γ`, `eq_positiveLift_of_isPositive` :633, `carrierCrossingEquiv` :799.
- LinkInterfaces.lean: `homfly` :131, `homfly_planar` :382.

Mathlib
- `IsLocallyConstant.iff_exists_open`, `.apply_eq_of_isPreconnected`, `.apply_eq_of_preconnectedSpace`, `.iff_continuous`, `continuous_quotient_lift`/`isOpen_coinduced`, `isPreconnected_connectedComponent`, `mem_connectedComponent`, `IsPathConnected.joinedIn`, `JoinedIn.joined`, `Joined.somePath`, `Path.source/target`, `PreconnectedSpace.constant`, `continuousAt_sign_of_ne_zero`, `continuous_pi`, `continuous_projIcc`, `Set.projIcc_of_mem`;
- `Quotient.congr`, `Quotient.lift`, `Equiv.permCongr(_apply)`, `Equiv.permCongrHom`, `map_zpow`, `Equiv.sumCongr_apply`, `Equiv.subRight`;
- `List.Perm.eq_of_pairwise`, `List.perm_ext_iff_of_nodup`, `List.pairwise_map`, `List.next_getElem`, `List.getElem_map`, `List.getElem_rotate`, `List.length_rotate`, `List.IsRotated.{perm,map,filter}`, `List.isRotated_next_eq`, `List.filter_map`, `List.filter_congr`, `Cycle.coe_eq_coe`, `Cycle.map_coe`, `Cycle.filter_coe`, `Cycle.filter_map`, `Cycle.next`;
- `Finset.mem_map'`, `Finset.card_map`, `Finset.sum_map`, `Finset.sum_attach`, `Finset.mapEmbedding`, `Fintype.prod_equiv`, `ZMod.natCast_zmod_val`, `ZMod.val_natCast`, `ZMod.val_add`.

## 4. The three riskiest steps and fallbacks

**Risk 1 — `homfly_positiveDiagram_shift` (lemma 19, ~150 lines): `Reparam` for a cyclic relabelling.**
`PlanarIsotopic = EqvGen (Reparam ∨ Deform)` and `Deform` keeps strand labels, so cyclic
invariance of `homfly (positiveLift …)` *must* go through `ReparamData` (component bijection,
`TraversalPoint` bijection preserving `traversalBetween`, same trace, over occurrences carried both
ways). `over_map/over_surj` need `visitPt` (through `Diagram.crossingParam`, a `Classical.choose`)
of the pulled-back diagram versus the original — pinned down by uniqueness of the parameter of a
point on a nonzero edge (`edgePoint_injective`) and `crossingPoint_mapCrossing` (`f = id`).
Fallbacks: (a) prove a general lemma "a `StrandMap` with `f = id`, `sgn = 1`, bijective on strands
and label-shifting the traversal points induces a `Reparam` between `D.pullback m` and `D`" (the
`reverse` construction at LinkMoves.lean:2385 is a worked example of the bookkeeping); (b) if the
rotation-freedom in the *path* case becomes the obstacle, prove exact (rotation-free) corner-list
equality there (`markList_transport` is already order preserving: `componentMarkList` and
`ccpCornerList` transport as *lists*, `List.filter_map`), so 19 is used only in Part 5; (c) last
resort: split `C_chamber` into labelled-chamber constancy (Parts 0–4, 6 without 52) and the
cyclic-invariance lemma, and leave the latter as the single remaining `sorry`, clearly flagged.

**Risk 2 — `cornerFamily_isCrossing_iff` + `cornerFamily_deform` (lemmas 40–42, ~160 lines).**
The `Deform` needs the *literal* crossing pairs of the corner polygon constant along the family and
positivity preserved. Route: `crossingGeometry_of_single_generic` (18) + `crossing_support_persists_of_geometry`
give local constancy, connectedness of `unitInterval` gives constancy; positivity by the sign of
a continuous nonzero determinant. Fallbacks: (a) derive the crossing pairs combinatorially: the
crossings of the carrier shadow are `carrierCrossings` (`carrierCrossingEquiv`) and a crossing
lies on the corner-polygon edges of the blocks containing its two visits (`mark_block`,
`carrierCrossing_edges`, LinkPositiveLift.lean:676/:722), all of which transport under `MarkEquiv`;
(b) use `IsPreconnected.subset_isClopen` per pair `{a, b}` (the set of `t` where `{a,b}` crosses
is clopen by persistence); (c) for the `DeformData` bookkeeping, keep the path on `unitInterval`
and only clamp at the end with `Set.projIcc`, as in the skeleton.

**Risk 3 — dependent-type friction in `MarkEquiv.cornerPolygon_agree` / `componentCycle_map` (lemmas 9–13, ~85 lines).**
`ccpCornerCount` depends on the polygon; the transported corner list is a *rotation* of the mapped
list, so indices live in different `ZMod`s and a rotation offset appears. `TupleAgree` (ℕ-indexed
agreement, `subst`-friendly) plus `shift m` isolates this; the index arithmetic (`ZMod.val_natCast`,
`ZMod.val_add`, `List.getElem_rotate`) is routine but fiddly. Fallbacks: (a) state agreement at the
level of plane-point lists `((ccpCornerList …).map (eval ∘ markPosition))` and prove the invariants
(`rotationNumber`, `Regular`, uniform turns, shadow genericity, `homfly`) as functions of a
`List Plane` invariant under `List.IsRotated` — one lemma per invariant, then no `ZMod` casts;
(b) for `Cycle.next` under `map`, if `cycle_next_map` resists, prove `succ` directly from list
indices (`markSuccessor_getElem` on both sides with `markList hQ = ((markList hP).map e).rotate r`,
`List.getElem_rotate`, `List.getElem_map`) and derive `E.cycle`-free versions (make `succ` the
structure field and derive `componentCycle_map` from `componentCycle_eq_filtered_markList` +
`List.IsRotated.filter`).

Minor risks: `markTransport_key_lt_iff` bridging `visitKey`/`geometricVisitKey` (use
`geometricVisitKey_eq_generic`); instance/decidability mismatches around `Finset.filter` in
`uniformDecompositions_eq` (state via `mem_uniformDecompositions`, never unfold the filter);
`Quotient.lift` hypothesis form for `genericCyclicSetoid` (compiles in the skeleton as `∃ k, R'.1 = shift k R.1`).
