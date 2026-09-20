# U_CUSPGEN_REPORT — unit U-CM-CUSPGEN, leaf `cusp_deletion_generic` (sm-6:335-359)

Prover subagent, 2026-09-15 ~17:45 UTC / 1:45pm ET.  File: `work/drafts/comparison/U_CUSPGEN.lean`
(byte-identical copy of `Statements_FINAL.lean` with the leaf's `sorry` replaced and helpers inserted
immediately before the leaf's docstring; `diff Statements_FINAL.lean U_CUSPGEN.lean` shows exactly two
hunks: `769a770,905` (the helpers) and `780c916,934` (the one `sorry` line → the proof body).  No
definition, structure, theorem statement, name or docstring was changed; the three §5 row theorems keep
their placeholder `sorry`.)

## Result

**PROVED**: `SM.cusp_deletion_generic {n} [NeZero n] (w : WallGerm (n+1)) (j) (hf : w.CuspAt j)
(hQ1 : G1 (deleteVertex w.center j)) : Generic (deleteVertex w.center j)` — the frozen statement, as
stated, no extra hypothesis (the domain is NOT narrowed: threaded cusps included).

- Compile (the only allowed command): `cd work/lean && lake env lean ../drafts/comparison/U_CUSPGEN.lean`
  → **0 errors**, 16.6 s warm; warnings = the 3 expected `declaration uses sorry` at §5 (lines 1002, 1007,
  1014: `prop_anchor_values`, `thm_comparison`, `cor_C_inherits`) + the 3 pre-existing unused-variable
  `hn` linter warnings in the frozen §0 prefix (lines 177, 195, 198 — not touched).
- `grep -c sorry`: **6 before → 5 after** (line 22 docstring, line 997 docstring, the three §5 bodies).
- `#print axioms` (scratchpad probe copy `cuspgen/U_CUSPGEN_axprobe.lean`, same content + prints):
  - `SM.cusp_deletion_generic` : [propext, Classical.choice, Quot.sound]
  - `SM.cu_cuspLawC_of` : [propext, Classical.choice, Quot.sound, SM.lit_homfly]
  - `SM.cor_C_inherits_of` : [propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm,
    SM.lp_lm_uniqueness] — **`sorryAx` is gone**; rows 127/128 are now conditional on rows 110/112 ONLY.

## Proof (PLAN_FINAL.md §3.4, steps 1-5 — followed literally; 136 lines of helpers + 19 lines of body)

Notation: `P = w.center`, `Q = deleteVertex P j`, `A = P (j-1)`, `M = P j`, `B = P (j+1)`.

1. **Case split** — `(w.cusp_cases hf).1 : CuspCase P j true ∨ CuspCase P j false`
   (SM/CuspDefinition.lean; internally `collinear_exterior_cases`).  `CuspCase … true` is definitionally
   `StrictBetween A B M`, `… false` is `StrictBetween M A B` — passed to the helpers by defeq, no unfolding
   needed.  From the case we get `k ∈ {j-1, j}` and the fused-edge containment below.
2. **Fused-edge containment** (`cu_fused_interior_true` / `cu_fused_interior_false`, ≈ 12 lines each):
   `x ∈ edgeInterior Q (-1)` unfolds (`edgePoint`, `deleteVertex_last`, `edge_deleteVertex_last`) to
   `x = A + q • (B - A)`, `0<q<1`.  Case true: `B = A + t • (M - A)` ⇒ `x = edgePoint P (j-1) (q*t)`,
   `0 < q*t < 1` (`mul_pos`, `nlinarith`).  Case false: `A = M + t • (B - M)` ⇒
   `x = edgePoint P j (t + q*(1-t))`, bounds by `nlinarith`.  Both closed by `ext <;> dsimp <;> ring`.
   No `x = M` case arises (M is outside `[A,B]`) — the cusp analogue of `fused_interior_lift` is simpler.
3. **The lift** — `def cu_lift j k i := if i = -1 then k else deletionIndex j i` (a function, as the plan
   suggests, instead of the relation `DeletionEdgeLift`).  `cu_lift_interior`: retained edges via
   `edgeInterior_deleteVertex P j hi`, the fused edge via the containment of step 2 (passed as the
   hypothesis `hfused`, so the lemma is case-independent).
4. **Remoteness transfer** (the "bulk"; ≈ 90 lines instead of the budgeted 150):
   - `cu_deletionIndex_adjacent` (`a, b ≠ -1`): `adjacent (dI a) (dI b) → adjacent a b` — three cases of
     `adjacent`, each by `deletionIndex_next` + `deletionIndex_injective` + `linear_combination`;
     `cu_deletionIndex_remote` is its contrapositive.
   - `cu_deletionIndex_two_prev [Nontrivial (ZMod n)]`: `deletionIndex j (-2) = j - 2`
     (`deletionIndex_next` at `-2 ≠ -1`, `deletionIndex_last`).
   - `cu_remote_prev` (`a ≠ -1`, `remote a (-1)`): `remote (dI a) (j-1)` — neighbours `j` and `j-1` are
     excluded by `deletionIndex_ne_deleted` / `deletionIndex_ne_prev`, `j-2 = dI (-2)` by injectivity +
     `remote a (-1)` (`-2` is adjacent to `-1` in `Q`).
   - `cu_remote_deleted` (`a ≠ -1`, `remote a (-1)`): `remote (dI a) j` — symmetric with `j+1 = dI 0`
     (`deletionIndex_zero`).
   - `cu_lift_remote (hk : k = j-1 ∨ k = j)`: `remote a b → remote (cu_lift a) (cu_lift b)` by the
     `a = -1` / `b = -1` case split (both `-1` is excluded by `remote_endpoints`; `remote_symm` for the
     mirrored case).  Remoteness implies distinctness, so no separate injectivity lemma is needed.
5. **Assembly** (the leaf body): `refine ⟨hQ1, ?_⟩`; `3 ≤ n` from `hf.1 : 4 ≤ n+1`; `Fact (1 < n)` for
   `Nontrivial (ZMod n)`; `rintro ⟨a, b, c, x, hab, hbc, hac, ha, hb, hc⟩`; the three `remote` facts in
   `Q` by `g1_common_interiors_remote hn hQ1` (SM/GenericTopology.lean); then
   `(mem_concurrenceTriples P {cu_lift a, cu_lift b, cu_lift c}).mpr ((concurrenceTriple_iff …).mpr ⟨x, …⟩)`
   contradicts `hf.2.2.1 : w.concurrences = ∅` (unfolded by `simpa only [WallGerm.concurrences]`) —
   exactly `flat_center_g2`'s last three lines.

## Helpers added (all `cu_`, lowercase, placed at lines 770-905, immediately before the leaf)

`cu_fused_interior_true`, `cu_fused_interior_false`, `cu_deletionIndex_adjacent`, `cu_deletionIndex_remote`,
`cu_deletionIndex_two_prev`, `cu_remote_prev`, `cu_remote_deleted`, `cu_lift` (def), `cu_lift_remote`,
`cu_lift_interior`.  All have explicit `{n : ℕ} [NeZero n]` binders (no `variable` block is open at that
point of the file); `[Nontrivial (ZMod n)]` where `-2 ≠ -1` is needed.  Clash scan: no other `cu_*` names in
the file besides the pre-existing `cu_cuspLawC_of`; none in work/lean/SM (`cu_` prefix unused there).

## Truth / fidelity notes

- The printed argument (sm-6:335-359) is complete and the accepted vocabulary covered every step; no
  new definition beyond the bookkeeping function `cu_lift` was needed, and no counterexample search was
  required (the statement is true as frozen).
- Nothing outside the leaf changed; `cu_cuspLawC_of` and `cor_C_inherits_of` typecheck unchanged against
  the proved leaf.
- Port note (U-CM-ROWS): the helpers are pure deletion-index / affine-parameter lemmas; at port,
  `cu_fused_interior_*` and `cu_deletionIndex_*` / `cu_remote_*` belong next to `fused_interior_lift` and
  `DeletionEdgeLift` (SM/DeletionInteriors.lean) or in a new SM/CuspDeletionGeneric.lean with the leaf.
- Elapsed: ≈ 15 min of prover time (well under the 6-10 h budget); two compile iterations of the scratch
  file (sign errors in two `linear_combination`s, a `rcases … rfl` that substituted `j` instead of `k`).
