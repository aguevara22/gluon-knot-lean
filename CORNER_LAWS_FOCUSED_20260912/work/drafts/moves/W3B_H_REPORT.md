# W3B_H — Wave 3b, Unit H (the 177 (6) record side) — report

File: `work/drafts/moves/W3B_H.lean` (8923 lines; copy of `W3_A1_Assembled.lean` 7827 lines + Unit H material).
Written 2026-09-15, 22:01–23:0x UTC (18:01–19:0x ET), bounded window (audit A-177-1).  Compile from `work/lean`:
`lake env lean ../drafts/moves/W3B_H.lean` — **0 errors**, 29 s.  `check_W3_identity.py` (5/5 IDENTICAL, imports = draft +
`SM.BigonDeletion`) and `check_W3_statements.py` (42/42 byte-identical, no missing names) both pass.
`grep -c sorry`: **10 → 6** (`W3_A1_Assembled.lean` 10, `W3B_H.lean` 6).  Companion: `W3B_H_brute.py` (brute-force check of
the two pure cores on all one-circle records with ≤ 10 occurrences; 0 failures).

## 0. Result — UNIT H CLOSED

| sub-leaf (frozen statement) | line | state | proof |
|---|---|---|---|
| `w3h_restrict_switch_deleted` | 8711 | **PROVED** | identity `RecordIso`; `switch_isOver_of_ne`/`switch_sgn_of_ne` (retained `w` has `crossingOf w ∈ S`, so `w ≠ v, pair v`) |
| `w3h_smooth_record_occ` | 8693 | **PROVED** | `unfold smoothDiagram`, `dite_eq_left/right`; `selfRecordIso`/`mixedRecordIso` have `Φ = visitEquiv`, i.e. `origVisit` on the nose, so `(ι.Φ v).1.1 = origCrossing v.1` (rfl) + `crossingPoint_origCrossing` |
| `w3h_record_core` | 8591 | **PROVED** | assembly (§2) on `w3bh_core_firstReturn` and `w3bh_core_comp`, both proved from the Φ-free cores `w3bh_core_pure₀`, `w3bh_core_comp_pure` |
| `w3h_hrec` | 8827 | **PROVED** | `w3bh_reduced_to_smooth` on both sides + `w3h_record_core` with `Φ := Ψ`; `hsucc` from `hcyc` via `nextVisit_comm_of_visitBetween_iff` on `Φ' := σ.trans Ψ` (`σ ∘ σ = id`) |

`#print axioms` (scratch copy `W3B_H_Axioms.lean`): `w3h_restrict_switch_deleted`, `w3h_smooth_record_occ`,
`w3h_record_core`, `w3h_hrec`, `w3bh_core_pure₀`, `w3bh_core_comp_pure` each depend on
`[propext, Classical.choice, Quot.sound]` only — **no `sorryAx`, no literature axiom**.  (`G11_core_sw`, for reference:
`[propext, Classical.choice, Quot.sound, lit_homfly, lp_lm, lp_lm_uniqueness]`, unchanged.)

## 1. Sorry inventory of `W3B_H.lean` (6; line = the `  sorry` line): 4094, 7552, 7570, 7603, 7699, 7726

| line | declaration | unit |
|---|---|---|
| 4094 | `w3b_reparam_switch` (optional) | b |
| 7552 | `w3e_xs_point` | E |
| 7570 | `w3e_liftVisit_σD_sw` | E |
| 7603 | `w3e_recordIsoData_sw` | E |
| 7699 | `w3g_bigonData_smooth_arcST` | G |
| 7726 | `w3g_bigonData_smooth_arcTS` | G |

No Unit-H declaration carries or depends on `sorry`.  Black boxes consumed from other units: **none** (`w3h_hrec` takes the two
`BigonData` as hypotheses exactly as frozen; the realiser's D4/D5 data are outside this unit).

## 2. New `w3bh_` material (≈ 1.1k lines, all in `section Row177_6`, all PROVED)

Generic helpers (before `w3h_record_core`):
`w3bh_crossingOf_mem_setOf` (7729; `crossingOf v ∈ {c | ∀ w ∈ c.1, P w} ↔ P v ∧ P (pair v)`),
`w3bh_record_crossingOf_eq_iff` (7736; `D.record.crossingOf v = crossingOf w ↔ v.1 = w.1`),
`w3bh_invol_mul` (7742), `w3bh_swap_disjoint` (7750), `w3bh_swap3_sq` (7761),
`w3bh_swap3_apply_apply` (7774; `σ (σ v) = v` from the 12 disequalities), `w3bh_compOf_eq_of_one`
(7785), `w3bh_ne_ne_twin_iff` (7795), `w3bh_fst_eq_iff_of_twin` (7807;
`(Ψ u).1 = (Ψ v).1 ↔ u.1 = v.1` for twin-compatible `Ψ`), `w3bh_restrictCrossings_iso_of_recordIso` (7824;
**a 15-line copy of `SM.CB.restrictCrossings_iso_of_recordIso`, SM/CBProducts.lean:1358 — that module is NOT in the file's
import closure**, §4), `w3bh_pair_ne_iff` (7840), `w3bh_crossKeep_iff` (7848; the `{y,z}`-deletion
predicate on `ρ.smooth a₁` read on `.1`), `w3bh_map_swap` (7863; `Φ (swap a b u) = swap (Φ a) (Φ b) (Φ u)`).

The core (the eight-orientation-pattern content of `w3h_record_core`, organised as a chase, not as eight cases):
* `w3bh_fr_chain` (7873): a `k`-step chain (intermediate points outside `p`, end point in `p`) determines
  `firstReturn` (`returnTime_eq_iff`); `w3bh_pow2/3/4` (7880–7884).
* `w3bh_no_two_cycle` (7888), `w3bh_no_fixed` (7905): on a one-circle record no `(x y)` two-cycle /
  fixed point of `s` coexists with a third occurrence (`sameCycle_of_one_circle` + `exists_nat_pow_eq`); `w3bh_succ_ne`
  (7916, predecessor uniqueness); `w3bh_sameCycle_closed` (8255, an `f`-closed set contains the `f`-cycle).
* **`w3bh_core_pure₀`** (7928): for one-circle `ρ`, four distinct occurrences `a₁ ~ a₂`, `b₁ ~ b₂` adjacent, and
  retained `v`: `firstReturn (s ∘ (a₁ b₁)) v = firstReturn (s ∘ (a₂ b₂)) v` on the complement of `{a₁,b₁,a₂,b₂}`.  Proof: if
  `s v` is retained both return `s v`; else `s v` is an entry of the block and the two chains (2–4 steps) end at the same
  exit, retained by `w3bh_succ_ne`/`w3bh_no_two_cycle`/`w3bh_no_fixed`: pattern `s a₁ = a₂, s b₁ = b₂`: entry `a₁`:
  `a₁ ↦ b₂ ↦ s b₂` vs `a₁ ↦ a₂ ↦ s b₂`, entry `b₁`: `b₁ ↦ a₂ ↦ s a₂` vs `b₁ ↦ b₂ ↦ s a₂`; pattern `s a₁ = a₂, s b₂ = b₁`:
  entry `a₁`: `a₁ ↦ s b₁` vs `a₁ ↦ a₂ ↦ b₁ ↦ s b₁`, entry `b₂`: `b₂ ↦ b₁ ↦ a₂ ↦ s a₂` vs `b₂ ↦ s a₂`; the two mirror
  patterns likewise (16 chains).  The other two entries of each pattern are impossible (their predecessor is local).
* **`w3bh_core_pure`** (8120): the six-point version (with `c₁, c₂`), from `w3bh_core_pure₀` by
  `firstReturn_congr_pred` + `firstReturn_firstReturn` (peeling `{c₁, c₂}` off: the `g`-strand orientation is irrelevant).
* **`w3bh_core_firstReturn`** (8163): the `Φ`-form — `Φ` intertwines `σ (s ∘ (a₂ b₂)) σ` with
  `s' ∘ (Φ a₁, Φ b₁)` (`hsucc` + `mul_swap_eq_swap_mul`, `σ a₁ = a₂`, `σ b₁ = b₂`); `firstReturn_map_val` for `Φ` and for `σ`
  (which fixes the non-local set pointwise); then `w3bh_core_pure`.
* **`w3bh_core_comp_pure`** (8273): the component bijection `Quotient (s ∘ (a₁ b₁)) ≃ Quotient (s ∘ (a₂ b₂))`
  fixing every retained class: the induced permutations agree (`w3bh_core_pure₀`), so retained classes transfer
  (`firstReturn_sameCycle_iff`); the class of `a₁` (of `a₂`) is followed to its exit (`sameCycle_apply_right`), and a
  non-retained exit closes a local cycle with no retained point (`w3bh_sameCycle_closed`); the two-class structure by
  `mul_swap_sameCycle_or`/`not_mul_swap_sameCycle_of_sameCycle`.
* **`w3bh_core_comp`** (8482): the `Φ`-form — `Equiv.sumCongr (e₀ ≫ Quotient.congr σ ≫ Quotient.congr Φ)
  (equivOfIsEmpty)` (`sameCycle_conj`, `sameCycle_map_iff`; `FreeComp` empty on a one-circle record with an occurrence).
* **`w3h_record_core`** (8591): nested-subtype `Φ̂ := subtypeEquiv (subtypeEquiv Φ hSK) hRK`; pair/bit/sgn
  from `hpair/hbit/hsgn`; `comp_eq` from `w3bh_core_comp`; `succ_eq` after reducing the doubly-restricted successor to
  `firstReturn (reconnect a₁)` on the six-point complement (`hred`: `firstReturn_congr_pred`, `firstReturn_firstReturn`,
  `w3bh_crossKeep_iff`) and `w3bh_core_firstReturn`.

The bridge (after `w3h_restrict_switch_deleted`): **`w3bh_reduced_to_smooth`** (8733): for a bigon `B` on
`(smoothDiagram D x ε hε).switch y₀` with `B.y = y₀`, `B.z = z₀` at the double points of `y, z`,
`B.reducedRecord ≅ (D.record.smooth a₁).restrictCrossings {c | ∀ v ∈ c.1, v.1 ≠ a₂ ∧ v.1 ≠ twin a₂ ∧ v.1 ≠ b₂ ∧ v.1 ≠ twin b₂}`
for EITHER occurrence `a₁` of `x`: `switchRecordIso` → `w3bh_restrictCrossings_iso_of_recordIso` (`keep` ↔ the
occurrence-defined set by `w3bh_record_crossingOf_eq_iff`) → `w3h_restrict_switch_deleted` → `w3h_smooth_record_occ` (+
`generic.crossingPoint_injective` on both diagrams: `u.1 = y₀ ↔ (ι.Φ u).1.1 = y`) → `smoothPairIso.symm` when
`a₁ = twin (overVisit x)`.

## 3. Correctness evidence beyond the compiler

`W3B_H_brute.py` enumerates every one-circle record with `n ≤ 10` occurrences and every labelling of six distinct local
occurrences satisfying the three adjacency disjunctions (96 / 336 / 768 / 1440 / 2400 configurations for `n = 6 … 10`, all 8
orientation patterns, all block adjacencies): the first returns of `s ∘ (a₁ b₁)` and `s ∘ (a₂ b₂)` on the non-local set
agree, both reconnections have exactly two cycles, and their partitions of the non-local set coincide — 0 failures.  This was
run before proving `w3bh_core_pure₀`/`w3bh_core_comp_pure` (rule 3: check a new statement before proving it).

## 4. Pitfalls met (for the port and for Units E/G)

* `SM.CB.restrictCrossings_iso_of_recordIso` (CBProducts:1358) is NOT importable here (`SM.CBProducts` is imported only by
  `SM/CornerChainStatements.lean`); `w3bh_restrictCrossings_iso_of_recordIso` is a copy using `firstReturn_map_val`
  (LinkRecordExtras:394).  At port time either add `import SM.CBProducts` and delete the copy, or keep it (no name clash).
* `set E := smoothDiagram D x ε hε with hE` REVERTED `y₀ z₀ hy₀ … B` and re-introduced them, so `hy₀` referred to a shadowed
  `y₀✝` and every later `exact` failed with a spurious type mismatch; spell the term out instead.  Likewise
  `rw [Equiv.Perm.mul_apply]` on a goal containing a `set`-bound permutation `σ` unfolded `σ`; use `show`.
* `have ι₁ := E.switchRecordIso …` hides the body, so `ι₁.Φ u` does not reduce to `u`; pass the iso term inline.
* `D.componentCount = 1` is not defeq to `D.record.componentCount = 1` (use `D.record_componentCount.trans hH`), but IS defeq to
  `D.Γ.c = 1`.
* `rintro u (rfl | rfl)` with `u = a₁` SUBSTITUTES AWAY the theorem's variable `a₁` (both sides are local variables), breaking
  every later reference; use `rintro u (hu | hu)` + `rw [hu]`.
* `rw [Ne]` unfolds only the first `≠`-instance; use `simp only [Ne, …]` + `tauto`, or `not_congr`.
* `sameCycle_map_iff` is stated `f'.SameCycle (Φ v) (Φ w) ↔ f.SameCycle v w` (target first).  `push_neg` is deprecated for
  `push Not`.  `Finset.forall_mem_singleton` does not exist (`simp only [Finset.mem_singleton, forall_eq]`).
* The `firstReturn_congr_pred`/`firstReturn_firstReturn`/`firstReturn_map_val` chain raised no instance mismatches as long as
  every predicate is the same literal lambda; do not `set`/`let` them.
* Cosmetic lints left in place: unused binders `hy hz` (`w3bh_core_pure`, `w3bh_core_comp_pure`) and `hadj_g`
  (`w3bh_core_comp_pure`) — kept so the two pure cores share the exact hypothesis list of `w3h_record_core`; the frozen
  file's 14 `if_pos/if_neg` deprecation warnings are untouched; two `if_pos/if_neg` uses of mine in `w3bh_core_comp_pure`.

## 5. Time log (UTC / ET)

22:01 / 18:01 start; 22:14 the two easy sub-leaves; 22:22–22:28 `w3bh_reduced_to_smooth` + `w3h_hrec` (3 iterations);
22:28 first integration (7 sorries); 22:29 `w3h_record_core` assembly on two `w3bh_core_*` sorries; 22:31 (a) reduced to the
Φ-free `w3bh_core_pure`; 22:39 (b) reduced to `w3bh_core_comp_pure`; 22:41 brute-force check of both; 22:45 `c₁,c₂` peeled
off (`w3bh_core_pure₀`); 22:49 `w3bh_core_pure₀` PROVED (16-chain chase, 2 iterations); 22:58 `w3bh_core_comp_pure` PROVED
(4 iterations); 22:59 final integration: 0 errors, 6 sorries, checks pass, `#print axioms` clean.  Well inside the
00:30 UTC hard stop.
