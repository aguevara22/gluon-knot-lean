# R176W2_OUTER_REPORT — the OUTER unit of row 176 (`r176o_`): the outer carriers of `S_full`

Prover subagent, 2026-09-15 22:35–23:35 UTC / 6:35–7:35pm ET.  File: `work/drafts/moves/R176W2_OUTER.lean`
(= `R176_Port_draft.lean` lines 1–6336 byte-identical + the `r176o_` appendix, lines 6338–7981, inside
`namespace RProof` before the final `end`/`end RProof`).  Compile: `cd work/lean && lake env lean
../drafts/moves/R176W2_OUTER.lean` → **exit 0, 0 errors** (~27 s); warnings: the inherited LEDGER
unused-section-variable note + `linter.unusedSectionVars` notes on the blanket-`include` sections of the appendix
(cosmetic).  `grep -c sorry`: **1 before, 1 after** — the single hit is the prose of the frozen header docstring
(line 1, "33 `sorry` leaves"); no `sorry` term anywhere.  Nothing under `work/lean` written; no `lake build`.
`#print axioms` (scratch copy): `r176o_outer_carriers_L_u`, `r176o_outer_carriers_L_v_proof`,
`r176o_outer_carriers_L_corrected_proof` → `[propext, Classical.choice, Quot.sound]` only.

## 0. Result

**The geometric identification is closed — but the frozen Prop `r176_outer_carriers_L` is FALSE as stated (rule 3),
so it is not proved; its corrected form is stated and PROVED, and the composition is replayed on it.**

| item | status |
|---|---|
| `r176_outer_carriers_L` at `y = lift u'` (the `Or.inl` disjunct of `_hy`) | **PROVED**: `r176o_outer_carriers_L_u` (line 7332) — the Prop's body with `_hy : y = est_liftCrossing … hu'` |
| `r176_outer_carriers_L` at `y = lift v'` (the `Or.inr` disjunct) | **FALSE as stated** (§2); corrected shape `r176o_OuterDataL'` (7421) + Prop `r176o_outer_carriers_L_v` (7474), **PROVED**: `r176o_outer_carriers_L_v_proof` (7545) |
| corrected Prop `r176o_outer_carriers_L_corrected` (7505) = the split statement | **PROVED**: `r176o_outer_carriers_L_corrected_proof` (7605) |
| the composition on the corrected statement | replayed: `r176o_portDataRest_case1 / _labelled / _of_uniform / r176o_est_port_relation_weak_uniform_of_curl_mixed / r176o_extreme_transport_of_curl_mixed (hcurl : r176s_curl_removal) (hmixed' : r176o_mixed_bridge') (hmixed : r176_mixed_bridge) : RowShape @ExtremeTransportData` (7715–7981); bodies byte-identical to the `r176_` originals except the `hy`-split in `_case1` |
| new black box | `r176o_mixed_bridge'` (7619): `r176_mixed_bridge` word for word with `O : r176o_OuterDataL'` (MIXED unit, see §4) |
| new connector | `r176o_smoothData_of'` (7658): `r176_smoothData_of` for `O : r176o_OuterDataL'` (`i := r176s_DA_j`, `j := r176s_DA_i`, `mixed` via `mixedSignSum_comm`) |

The row is therefore reduced to `r176s_curl_removal`, `r176_mixed_bridge` and `r176o_mixed_bridge'`; no
outer-carrier hypothesis remains.  The frozen `r176_outer_carriers_L`, `r176_OuterDataL`, `r176_smoothData_of`,
`r176_portDataRest_*` and `r176_extreme_transport_of_curl_outer_mixed` are untouched (and `r176_OuterDataL`,
`r176_smoothData_of` are reused as they stand for the `u'`-half).

## 1. The geometry, as proved (R176_SMOOTH_REPORT §2.2 made precise)

Coordinates (the LEDGER's): `P' = E.curve t'`, `hP = geomAt E t' ht'.1`, `T = S' = transportSupport hs (Q ∪ {j})`,
`q = q₀'`, the six local visits `ua = (u',a), uc = (u',c), ja = (j',a), jb = (j',b), vb = (v',b), vc = (v',c)`,
`Sf = r176l_Sf T u' v'`, children `L1 = owner_Sf vc` (kinked), `L2 = owner_Sf ua` (clean), `Z = owner_Sf ja`.
Successor facts from the LEDGER (case 1, `u' <_a j'`): `ρ ua = ja` (`hρa`), `ρ jb = vb` (`hρb`), and the forced
orientation `ρ vc = uc` (`hρc := (r176l_lt_c_of_indep …).2`); hence on the carrier orbit `ρ_T` of `q`
(`geoSmoothingSuccessor hP T`): `ρ_T ua = ja`, `ρ_T ja = vb`, `ρ_T vc = uc`.

**Orbit coordinates.**  With `N = (geoComponentMarkList hP T q).length` and `k` the index of `ua` from `uc`
(`r176o_exists_k`: `0 < k < N`, `ρ_T^k uc = ua`), the six marks sit at `uc = 0, ua = k, ja = k+1, vb = k+2, …,
vc = N-1` and `k + 3 < N` (`r176o_pow_ja/vb/vc`, `r176o_k_bounds`).  The two children in these coordinates:
* `owner_Sf m = L2 ↔ m = ua ∨ ∃ i, 0 < i < k ∧ ρ_T^i uc = m` (`r176o_owner_L2_iff`): `ρ_Sf` and `ρ_T` agree off
  the four visits of `u', v'` (`r176o_succSf_eq_succT`), `ρ_Sf ua = ρ uc = ρ_T uc`, so the `ρ_Sf`-orbit of `ua`
  follows the `ρ_T`-orbit of `uc` until it returns to `ua` (`r176o_orbit_transfer`, `r176o_sameCycle_transfer_iff`).
* `owner_Sf m = L1 ∨ m = vb ↔ k < i` for `m = ρ_T^i uc ≠ ja` (`r176o_between_ua_uc_iff_L1`), from
  `r176l_owner_Sf_cases`, `r176l_mem_Z` and the L2 description.

**lem:carrierword in usable form** (`r176o_cyc_iff`, §O1): for any mark `a` of `q` and `i j l < N`,
`cycBetween (key (ρ_T^i a)) (key (ρ_T^j a)) (key (ρ_T^l a)) ↔ cyc(i, j, l)` — from `CV.markList_getElem_pow`,
`CV.markList_key_lt_iff`, `CV.rotate_cyc_iff` (PieceIntrinsic §2); with `r176o_pow_inj` (orbit indices `< N` are
unique) and `r176o_exists_pow`.  Combined with `r176s_crossKeep_KA_iff_key` (arcs read on the parent keys) and
`CV.crossKeep_liftBlock_iff`, every arc identity becomes index arithmetic (`omega`).

**`y = lift u'`, `v₀ ↦ uc`** (so `τ v₀ ↦ ua`): `A = (uc → ua)` = the open orbit arc `(0, k)` = `L2 ∖ {ua}`;
`B = (ua → uc)` = `(k, N)` = `{ja, vb} ∪ (L1 ∖ {vc}) ∪ {vc}`.  Hence
`K_A = liftBlock (retained L2)` (`r176o_KA_eq`), `K_B = liftBlock (retained L1) ∪ {lift v'}` (`r176o_KB_eq`),
`lift v' ∉ liftBlock (retained L1)` (`r176o_r_not`), and the `B`-restricted successor of the `vc`-occurrence is
the `vb`-occurrence (`r176o_r_curl`: a `K_B`-occurrence strictly between `vc` and `vb` would have orbit index in
`(k, k+2)`, i.e. be `ja ∈ T`).  The event-level theorem `r176o_outer_carriers_L_u` assembles `r176_OuterDataL`
with `v₀` the occurrence over `uc` (`CV.liftVisit_surjective`), `hv₀` via `CV.liftVisit_fst`/`Equiv.eq_symm_apply`,
`subA/subB` from `r176l_sub_L2/L1`.

**`y = lift v'`, `v₀ ↦ vb`** (so `τ v₀ ↦ vc`): `A = (vb → vc)` = `(k+2, N-1)` = `L1 ∖ {vc}`,
`B = (vc → vb)` = `{uc} ∪ (L2 ∖ {ua}) ∪ {ua, ja}`: `K_A = liftBlock (retained L1)`, `K_B = liftBlock (retained L2)
∪ {lift u'}`, kink `lift u'`, curl at the `ua`-occurrence (`r176o_KA_eq'`, `r176o_KB_eq'`, `r176o_r_not'`,
`r176o_r_curl'`, from `r176o_between_vb_vc_iff_L1`, `r176o_between_vc_vb_iff_L2`).

## 2. Why the frozen Prop is false at `y = lift v'` (rule 3)

`r176_OuterDataL` fixes `Λ_B := L1` (kinked) and `Λ_A := L2` (clean) and demands `K_A(v₀) = liftBlock (retained
L2)` for an occurrence `v₀` of `y`.  At `y = lift v'` the two occurrences are over `vb` and `vc`:
* `v₀ ↦ vc`: `A = (vc → vb)` contains both occurrences of `lift u'` (orbit indices `0` and `k`), so
  `lift u' ∈ K_A`; but `liftLabel (lift u') = u' ∈ Sf` is not retained by any child, so `lift u' ∉ liftBlock
  (retained L2)` — `KA_eq` fails outright.
* `v₀ ↦ vb`: `K_A = liftBlock (retained L1)`, which equals `liftBlock (retained L2)` only when both children have
  no retained crossing (then `K_B = {lift u'}` and the data degenerately exists).
So the Prop holds at `y = lift v'` only in that degenerate case and is false in general.  The composition DOES use
this disjunct: `r176_portDataRest_labelled` (line 6010) handles case 2 (`j' <_a u'`) by relabelling
`(a,b,c) ↦ (b,a,c)`, `(u,v) ↦ (v,u)` and calling `_case1 … _ (Or.inr rfl)`, i.e. with `y` the lift of the NEW `v'`.
Corrected statement: `r176o_outer_carriers_L_corrected` = the same binders, conclusion
`(y = lift u' → Nonempty (r176_OuterDataL …)) ∧ (y = lift v' → Nonempty (r176o_OuterDataL' …))`, where
`r176o_OuterDataL'` is `r176_OuterDataL` with `L1 ↔ L2` exchanged in `KA_eq`, `KB_eq`, `r_not` (`subA`, `subB`
unchanged).  Both halves are proved (`r176o_outer_carriers_L_corrected_proof`).

## 3. What the composition needs changed (done here as `r176o_` replays; the assembler may adopt them verbatim)

1. `r176_portDataRest_case1`: replace `obtain ⟨O⟩ := hout … y hy; have D := r176_smoothData_of … O hSf' (hmixed … O)` by the
   `Nonempty`-valued split of §O7 (`r176o_portDataRest_case1`, line 7715): `rcases hy` — `Or.inl`: `O` from
   `r176o_outer_carriers_L_u`, `D` from `r176_smoothData_of … O hSf' (hmixed … (Or.inl hy) O)`; `Or.inr`: `O` from
   `r176o_outer_carriers_L_v_proof`, `D` from `r176o_smoothData_of' … O hSf' (hmixed' … (Or.inr hy) O)`; then
   `obtain ⟨D⟩`.  (The split must produce `Nonempty (r176l_SmoothData …)`, not the data itself: `rcases` on
   `hy : _ ∨ _` cannot eliminate into `Type`.)  Everything after `D` is unchanged.
2. Hypothesis change along the chain: `(hout : r176_outer_carriers_L)` → `(hmixed' : r176o_mixed_bridge')` in
   `_case1`, `_labelled`, `_of_uniform`, `r176_est_port_relation_weak_uniform_of_curl_outer_mixed`,
   `r176_extreme_transport_of_curl_outer_mixed` (replays: `r176o_portDataRest_labelled` 7846, `_of_uniform` 7904,
   `r176o_est_port_relation_weak_uniform_of_curl_mixed` 7964, `r176o_extreme_transport_of_curl_mixed` 7975).
   Once the two bridges are proved the row is `RProof.extreme_transport := r176o_extreme_transport_of_curl_mixed
   <curl> <mixed'> <mixed>`.
3. `r176_smoothData_of` is reused as is for the `u'`-half; the `v'`-half uses `r176o_smoothData_of'` (§O6): the
   SmoothData of `(Λ₁ = L1, Λ₂ = L2)` with `i := r176s_DA_j` (the `A`-class, now the clean `L1`: `poly₁` by
   `r176s_homfly_of_liftBlock` + `r176s_knotRestrictIso_j` from `KA_eq`) and `j := r176s_DA_i` (the `B`-class, now the
   kinked `L2`: `poly₂` by `r176s_homfly_of_liftBlock_curl` + `r176s_knotRestrictIso_i` from `KB_eq, r_not, r_curl`),
   `ij := (r176s_DA_ij …).symm`, `mixed := (mixedSignSum_comm _ _ _).trans hmixed`.

## 4. Black boxes / other units

* `r176o_mixed_bridge'` (**MIXED unit**, OPEN, `def … : Prop`, no `sorry`): `r176_mixed_bridge` with
  `O : r176o_OuterDataL'` — `mixedSignSum (r176s_DA D₊ y) (r176s_DA_i … O.v₀ O.hv₀) (r176s_DA_j … O.v₀ O.hv₀) =
  #(r176l_mixedSet … L1 L2)`.  Same route as `r176_mixed_bridge` (R176_ASSEMBLY_REPORT §5 #3); the per-visit
  readings `r176o_between_vb_vc_iff_L1` / `r176o_between_vc_vb_iff_L2` (and, for the `u'`-half,
  `r176o_between_uc_ua_iff_L2` / `r176o_between_ua_uc_iff_L1`) are exactly the "a crossing is mixed iff its two
  parent visits are owned by different children" bridge that unit needs.
* `r176s_curl_removal` and `r176_mixed_bridge`: untouched (SMOOTH / MIXED).
* No other unit's Prop was used or altered; no new `sorry`.

## 5. Inventory of the appendix (55 declarations, lines 6338–7981)

| § | declarations | content |
|---|---|---|
| O0 (6340) | `r176o_add_mod_inj`, `r176o_unrotate`, `r176o_pow_mul_add_fix`, `r176o_pow_mod_fix`, `r176o_sameCycle_iff_pow`, `r176o_orbit_transfer`, `r176o_sameCycle_transfer_iff`, `r176o_crossing_set_ext` | ℕ-rotation arithmetic; `SameCycle f x y ↔ ∃ i < p, f^i x = y` given `f^p x = x`; orbit transfer between two permutations that agree along an orbit; crossing-set extensionality via `CrossKeep` |
| O1 (6414) | `r176o_pow_length_fixes`, `r176o_pow_mod`, `r176o_exists_pow`, `r176o_pow_apply_getElem`, `r176o_pow_inj`, `r176o_cyc_iff` | GENERAL (any independent `T`, any carrier `q`): the `ρ_T`-orbit indexed from any mark, and cyclic key order = orbit order (lem:carrierword, from PieceIntrinsic §2) — library candidate (`CV/PieceIntrinsic` neighbourhood) |
| O2 (6483) | `r176o_cycBetween_rotate`, `r176o_uc_ne_ua`, `r176o_ja_ne_uc`, `r176o_vb_ne_uc`, `r176o_vb_ne_vc`, `r176o_owner_ja`, `r176o_exists_k`, `r176o_pow_vc`, `r176o_succSf_eq_succT`, `r176o_pow_ja`, `r176o_pow_vb`, `r176o_k_bounds`, `r176o_owner_L2_iff`, `r176o_between_uc_ua_iff`, `r176o_between_ua_uc_iff`, `r176o_between_uc_ua_iff_L2`, `r176o_between_ua_uc_iff_L1` | the labelled corner on the orbit (LEDGER's `section L3`/`Children` binders with `hP := hG.cg`, blanket `include`; uniform argument list `hG hT q hab hac hbc hj hu hv hjT huq hvq hρa hρb hρc hSf [hk0 hkN hk]`) |
| O3 (6738) | `r176o_KA_eq`, `r176o_KB_eq`, `r176o_r_not`, `r176o_r_curl` | the four arc identities at `v₀ ↦ uc` on `geoPositiveLift hn hG hT q` |
| O5 (6980) | `r176o_between_vb_vc_iff_L1`, `r176o_between_vc_vb_iff_L2`, `r176o_KA_eq'`, `r176o_KB_eq'`, `r176o_r_not'`, `r176o_r_curl'` | the mirrored identities at `v₀ ↦ vb` |
| O4 (7322) | `r176o_outer_carriers_L_u`, `r176o_OuterDataL'`, `r176o_outer_carriers_L_v`, `r176o_outer_carriers_L_corrected`, `r176o_outer_carriers_L_corrected_of_v`, `r176o_outer_carriers_L_v_proof`, `r176o_outer_carriers_L_corrected_proof` | the event level (the `r176l_portDataRest_case1` preamble replayed: `hXL, hρa, hlt_b, hρb, hnb_c, hSf, hρc`) |
| O6 (7610) | `r176o_mixed_bridge'`, `r176o_smoothData_of'` | the mirrored bridge Prop and connector |
| O7 (7706) | `r176o_portDataRest_case1`, `_labelled`, `_of_uniform`, `r176o_est_port_relation_weak_uniform_of_curl_mixed`, `r176o_extreme_transport_of_curl_mixed` | the composition replayed |

Proof-engineering notes: `CarrierGeometry`/`CrossingGeometry` are Props, so `hG.cg`, `geomAt E t' ht'.1` and any
`GeoIndependent` proof are interchangeable by proof irrelevance (this is what lets the `geoPositiveLift hn hG hT q`
lemmas discharge the `CV.carrierDiagram … (est_S'_ind …)` fields verbatim).  `r176s_KB ρ v₀` unfolds to
`r176s_KA ρ (ρ.pair v₀)` with `ρ.pair v₀ = D.twin v₀` (`record_pair_apply`, rfl), so the `B`-arc is read with
`r176s_crossKeep_KA_iff_key … (D.twin v₀)`.  The `local instance 2000 r176l_decEq` is re-declared in each
section that names `r176l_Sf`.  Reassessment rule: no lemma took two failed attempts; the only detours were
Lean-syntactic (variable `include`s, a notation that does not compose with `.`-projection, a structure-instance
parse quirk replaced by the anonymous constructor).

## 6. Final checks (23:29 UTC / 7:29pm ET)

* `lake env lean ../drafts/moves/R176W2_OUTER.lean`: exit 0, 0 errors; 7984 lines; `head -6336` byte-identical to
  `R176_Port_draft.lean` (`cmp`); 55 `r176o_` declarations; `grep -c sorry` = 1 (line-1 prose, unchanged).
* `#print axioms` (scratch copy): `r176o_outer_carriers_L_corrected_proof` → standard only;
  `r176o_smoothData_of'` → standard + `SM.lit_homfly, SM.lp_lm, …` (as `r176_smoothData_of`);
  `r176o_extreme_transport_of_curl_mixed` → standard + `SM.lit_homfly, SM.lit_homfly_descent, …` (the registered
  literature axioms, as `r176_extreme_transport_of_curl_outer_mixed`); no `sorryAx`.
* Note for the pod: another agent was running `lake build RProof.GenericSelected` in `work/lean` at 23:24 UTC; one
  compile transiently failed with a missing `SM/CarrierFloor.olean` and succeeded on retry — not a defect of this file.
