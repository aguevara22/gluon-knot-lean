# U_KL1_REPORT — unit KL1 (carrier record bridge), prover report

File: `work/drafts/cb/U_KL1.lean` (copy of Skeleton_FINAL.lean; only the KL1 leaves' `sorry` bodies replaced,
plus `kl1_`-helpers inserted immediately before the leaf, namespace `SM.CB`, after `variable (hn) (hP)`).
Check: `cd work/lean && lake env lean ../drafts/cb/U_KL1.lean` — **0 errors**, 14 s. `grep -c sorry`: 18 before → 16
after (the 16: the module docstring at line 10 and the leaves of KL0/KL2/KL3/T1/GL/AS). Diff against the skeleton:
the only removed text is the two `:= sorry` tails; 770 lines added. No definition, statement, name or docstring changed.

## Leaves

| leaf | status | body |
|---|---|---|
| `positiveLiftRecordIso hn hP hT q : RecordIso (positiveLift hn hP T q hT).record (gaussRecord (cg hn hP) (carrierCrossings hn hP T q))` | **PROVED** | `where e := Equiv.ofUnique (Fin 1) Unit; Φ := kl1_occEquiv hn hP hT q; comp_eq := Subsingleton.elim (α := Unit); succ_eq := kl1_succ (via gaussSucc_val); pair_eq := kl1_toVisit_twin (via gaussPair_val); bit_eq := kl1_bit; sgn_eq := positiveLift_sign` |
| `positiveLiftRecordIso_val hn hP hT q v : (occVisit _ _ (ι.Φ v)).1 = (carrierCrossingEquiv hn hP T q hT v.1).val` | **PROVED** | `kl1_toVisit_crossing hn hP hT q v` (the `Φ` unfolds definitionally: `kl1_occEquiv_apply` is `rfl`) |

Leaves left: none. No leaf needed a stronger hypothesis; no counterexample.

Axioms (checked with a temporary `#print axioms`, removed): `kl1_occEquiv`, `kl1_succ` and every helper: `propext,
Classical.choice, Quot.sound` only. `positiveLiftRecordIso` / `_val`: additionally `sorryAx`, **only through the KL0 black
boxes** (`gaussSucc_val`, `gaussPair_val`, and the sorried laws inside `gaussRecord`'s type). Nothing of KL1 is sorried.

## Route actually taken (differs from PLAN_FINAL §4 in one respect)

Everything is proved on the **SM Carrier lane directly** (no `geoPositiveLift` / `geoPositiveLift_eq_generic` transfer):
LinkPositiveLift.lean already provides `nonadjacent_meet`, `mark_block`, `block_mark_eq`, `param_eq_of_corner`,
`consecutive_meet`, `BlockInterior.visit_edge`, `carrier_selfIntersection_not_corner` for `positiveLift` itself, and
CarrierCornerPolygon.lean's `ccpCornerPolygon_block` gives the block data **with strictly increasing slot parameters**
(`(ccpOutSlot (ρ^r c_j)).2.val < (ccpOutSlot (ρ^(r+1) c_j)).2.val`) and `Q(j+1) − Q j = C • edge P e_j`, `C > 0`. The
inherited-order fact (`TracedSuccessor` in the plan) is the accepted SM-lane `componentMarkList_getElem_successor`
(CarrierClosedTrace.lean:88): `ρ_T ML[i] = ML[(i+1) % N]` on `ML = componentMarkList = markList.filter (owner = q)`,
which is sorted by `markKey` (`markList_sorted`). The Gauss-list side uses `geometricGaussList (cg hn hP) = gaussList hn hP`
(`geometricGaussList_eq_generic`, `rfl`) so `gaussList hc X = (gaussList hn hP).filter (·.1 ∈ X)`, strictly sorted by
`visitKey` (`gaussList_sorted`, `gaussList_nodup`, `visitKey_injective`).

### The occurrence bijection `Φ` (kl1_toVisit / kl1_occEquiv)
Shadow visit `(x, s)` ↦ the P-visit `w` of `c := carrierCrossingEquiv x` with `w.2.val = e_{s.2}` (the original edge of
the block `s.2`), whose twin lies on the block edge of the other strand (`kl1_visit_exists`, from `nonadjacent_meet` +
`generic_crossingPoint_injective`); unique by `visit_eq_or_twin` + `visitTwin_edge_ne` (`kl1_visit_unique`). Injective
(`kl1_toVisit_injective`: two strands of one `x` would put `w` and `τ w` on the same edge); bijective by cardinality
(`kl1_card_retained`: `Equiv.subtypeSigmaEquiv` + `visits_per_crossing`; `card_visit_eq_two_mul`,
`card_carrierShadow_crossing`). Spec lemmas: `kl1_toVisit_crossing`, `kl1_toVisit_edge`, `kl1_toVisit_twin_edge`,
`kl1_toVisit_twin` (Φ (twin v) = visitTwin (Φ v)), `kl1_occEquiv_apply` (rfl).

### bit_eq (kl1_bit)
`positiveOverBit (Φ v) = D.overBit v`: `det(dir s, dir (other s)) = (C·C') det(edge P e_s, edge P e_{s'})` with
`ccpCornerPolygon_edge` (positive multiples), `ccp_det_smul_smul`, `mul_pos_iff_of_pos_left`; then `s = overStrand x ↔
0 < det(dir s, dir (other s))` from `positiveLift_isPositive` and `det_swap`.

### succ_eq (the heart; kl1_succ)
`Φ (D.nextVisit v) = L_X.next (Φ v)` via `cycNext_unique` on `D.visitCoord` (Q-key). Ingredients:
* `kl1_sorted_next_no_between`: in a list strictly sorted by a real key, nothing is cyclically strictly between `x` and
  `l.next x` (list version of the accepted `sorted_next_no_cyclic_between`; `List.next_getElem`,
  `List.pairwise_iff_getElem`).
* **Q-key on all marks of `q`** (`kl1_pos`, `kl1_key`): block position `(j, r)` from `mark_block` and Q-parameter `t` with
  `pos m = edgePoint Q j t`, `0 ≤ t < 1` (`kl1_pos_exists`; `t = 1` excluded by `param_eq_of_corner` — it would make
  `m` a corner `c_{j+1}` with `j = j+1`); `kl1_key m = j.val + t`; uniqueness `kl1_pos_unique` (`block_mark_eq`,
  `edgePoint_injective`).
* **Local step** `kl1_key_lt_succ`: `ρ_T m ≠ c_0 → kl1_key m < kl1_key (ρ_T m)`. Same block: both slot parameters lie on
  `e_j`, increase (`ccpCornerPolygon_block`), and `edgePoint Q j u = edgePoint P e_j (τ₀ + u·C)` makes `t` an increasing
  affine function of the slot parameter. Next corner: `ρ_T m = c_{j+1}`, key `= (j+1).val = j.val + 1 > j.val + t`
  (`ZMod.val_add`, `ZMod.val_one_eq_one_mod`, `ZMod.val_eq_zero`; `j + 1 ≠ 0` because `c_{j+1} ≠ c_0`).
* **Cycle indexing from `c_0`**: `kl1_pow_markList_zero` (`ρ^i ML[0] = ML[i % N]`), `kl1_pow_corner`
  (`ρ^i c_0 = ML[(i₀+i) % N]` with `c_0 = ML[i₀]`), `kl1_exists_idx` (every mark of `q` is `ρ^i c_0`, `i < N`),
  `kl1_idx_injective`; `kl1_keyIdx_strictMono` (Q-key strictly increasing in `i < N`, by the local step);
  `kl1_markKey_lt` / `kl1_pkey_strictMono` (P-key strictly increasing along `ML`).
* **Strand = block** (`kl1_block_of_visit`): the block index of `Φ v` is the strand of `v` — the crossing point lies on
  both Q-edges; adjacent distinct edges meet only at a corner (`consecutive_meet`, contradiction with
  `carrier_selfIntersection_not_corner`), non-adjacent ones give (`nonadjacent_meet`) `w` and `τ w` on the same edge.
  Hence `kl1_visitCoord_eq`: `D.visitCoord v = kl1_key (Sum.inr (Φ v))` (`crossingParam_spec`, `edgePoint_injective`).
* **Cyclic-order transfer** (`kl1_cyc_transfer`): `cycBetween` of Q-keys of shadow visits ⇒ `cycBetween` of P-keys of
  their P-visits, through `kl1_cycBetween_of_strictMono` (strictly monotone key ↔ index betweenness) and
  `kl1_cycBetween_shift` (rotation invariance of index betweenness, `add_mod_cases` + omega).

## Helpers added (all in `SM.CB`, prefix `kl1_`, before the leaf; 48 declarations)
kl1_blockEdge, kl1_visit_exists, kl1_visit_unique, kl1_toVisit, kl1_toVisit_crossing, kl1_toVisit_edge,
kl1_toVisit_twin_edge, kl1_toVisit_twin, kl1_toVisit_injective, kl1_card_retained, kl1_toVisit_bijective, kl1_occEquiv,
kl1_occEquiv_apply, kl1_bit, kl1_cycBetween_shift_aux, kl1_cycBetween_shift, kl1_cycBetween_of_strictMono,
kl1_sorted_next_no_between, kl1_two_le_length, kl1_pow_markList_zero, kl1_corner_mem_markList, kl1_pow_corner,
kl1_exists_idx, kl1_idx_injective, kl1_pairwise_lt, kl1_markKey_lt, kl1_pos_exists, kl1_pos, kl1_pos_spec,
kl1_pos_unique, kl1_key, kl1_key_congr, kl1_key_lt_succ, kl1_keyIdx, kl1_keyIdx_strictMono, kl1_owner,
kl1_block_of_visit, kl1_visitCoord_eq, kl1_visitCoord_eq_idx, kl1_pkey, kl1_pkey_eq, kl1_pkey_strictMono,
kl1_visitKey_eq_idx, kl1_cyc_transfer, kl1_mem_gaussList, kl1_gaussList_pairwise, kl1_compOf_eq, kl1_succ.

## Black boxes used (other units)
`gaussSucc_val`, `gaussPair_val` (KL0) only — both applied after a `show` that unfolds `(gaussRecord hc X).succ` /
`.pair` to `gaussSucc hc X` / `gaussPair hc X` (a plain `rw` does not see through the `def gaussRecord`). No other
unit's leaf is touched. `gaussSucc_val` needs `hv : v.1 ∈ gaussList hc X`: supplied by `kl1_mem_gaussList`
(`List.mem_filter`, `mem_geometricGaussList`).

## Pitfalls met (Lean 4.34.0-rc2 / this Mathlib), for the porter
1. **Transparency**: with `v : (positiveLift ..).Γ.Visit`, `x`/`s` carry the `positiveLift` type and every `rw` on
   shadow-level terms fails ("target not type-correct under implicit transparency"). All helpers are therefore stated on
   `(carrierShadow hn hP T q hT).Visit` (definitionally equal; `positiveLift_Γ` is `rfl`) and the leaf uses them by
   defeq. Mixed `D.overStrand x` / `Γ.dir s` goals are closed with `subst`/`exact`/`linarith` on syntactically identical
   atoms, never `rw`.
2. `generalize e = x at h ⊢` did **not** rewrite the hypotheses; use `set`, or (as done) an arithmetic aux lemma over
   variables (`kl1_cycBetween_shift_aux`). `omega` treats `(s + a) % N` (variable modulus) as an atom — supply the
   `add_mod_cases` disjunction and, crucially, the bounds `a' < N` (lost when abstracting).
3. Instances: `Subsingleton (Fin D.Γ.c)` and `Unique D.record.comps` are not found (`D.Γ.c` is not syntactically `1`);
   use `Subsingleton.elim (α := Fin 1)`, `Equiv.ofUnique (Fin 1) Unit`, `Subsingleton.elim (α := Unit)`.
4. `rw` with `hcorner : ρ m = c_{j+1}` inside `kl1_pos (ρ m) hm'` fails (proof-dependent motive) — compose equalities
   (`f1.trans hcorner`) instead; `set` must come **after** `unfold kl1_key`, else the goal keeps the unabstracted term.
5. `add_lt_add_left` here has the shape `b < c → b + a < c + a`; used `add_lt_add_of_le_of_lt le_rfl`.
6. `dif_pos` is deprecated (linter) — `split_ifs`. `self_eq_add_right`-style names are unstable; `linear_combination` on
   `ZMod k` works (`h1 : (1 : ZMod k) = 0 := by linear_combination -hj`).
7. `pairwise_lt_of_pairwise_le_nodup` (GeoMarkTransport.lean) is not accessible under the opened namespaces; reproved
   as `kl1_pairwise_lt` (one line). `getElem_congr_of_eq` is taken from `SM.GeoCarrier` (GeoPositiveLift.lean, imported
   through the skeleton's imports); a port module should import `SM.GeoPositiveLift` or inline it (3 lines).

## For the assembler / executor
* `positiveLiftRecordIso_val` holds by unfolding: `(positiveLiftRecordIso hn hP hT q).Φ v = kl1_toVisit hn hP hT q v` is
  `rfl`. Useful extra facts for GL/consumers: `kl1_toVisit_edge` (the P-visit lies on the original edge of the strand's
  block), `kl1_toVisit_twin` (`Φ ∘ twin = visitTwin ∘ Φ` at the level of `Visit P`), `kl1_block_of_visit`
  (strand = block), `kl1_visitCoord_eq` (Q-key of a shadow visit).
* PLAN §4 acceptance checks: "Φ preserves crossing points" is `positiveLiftRecordIso_val` + `crossingPoint_carrierCrossingEquiv`
  (`crossingPoint (occVisit (Φ v)).1 = Γ.crossingPoint v.1`). The `S = ∅` / `record_of_single_polygon` check was not run
  separately (the theorem is proved for every independent `T`, including `∅`).
* Port target `SM/CBCarrierRecord.lean`: the block is self-contained given the skeleton's imports (`CV.X1`,
  `CV.PieceCurve`, `SM.MarkedProducts`, `SM.CornerStateSum`) plus the KL0 declarations (`gaussList`, `gaussSucc`,
  `gaussSucc_val`, `gaussPair`, `gaussPair_val`, `positiveOverBit`, `gaussRecord`, `occVisit`). Two pre-existing
  skeleton warnings remain (unused `hT` in the AS leaf `exists_visit_of_mem_carrierCrossings`; deprecated
  `Set.mem_setOf_eq` in `record_iso_blockRecord`) — not KL1's.
