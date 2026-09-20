# PORT_REPORT — row 57 lem:gauss-two-discs, `work/drafts/twodiscs/port/SM/GaussTwoDiscs*.lean`

Prepared 2026-09-19 (14:55 UTC / 10:55am ET) by the U12 (wave-2) assembler from `W2_Assembled.lean` (20 912 lines, sha256
`6ffc9a339f4bddb4b…`; all 92 leaves closed, `#print axioms SM.lem_gauss_two_discs = [propext, Classical.choice, Quot.sound]`,
W2_ASSEMBLY_REPORT.md).  Generator: scratch `asm2/port.py` (deterministic: within-line edits by line number, each asserted to match
exactly once, then a split at section boundaries).  Nothing was written under `work/lean`; no `lake build`.  **The files are
prepared for the pod executor**: copy `port/SM/*.lean` to `work/lean/SM/`, replace the literal `<HH:MM>` in each header line by the
port time, register the row, run `python3 tools/check_lean.py work/lean`.

## 1. Modules (import chain, in this order)

| module (`SM/…lean`) | content (W2_Assembled lines) | lines | decls | leaves | compile (`-o` olean) | warnings left |
|---|---|---|---|---|---|---|
| `GaussTwoDiscsDefs` | the 14 imports; header prose (reworded); provenance note; **frozen DEFS block** = `namespace SM … §1-§4` (77-276) | 274 | 32 | 0 | 19 s | 0 |
| `GaussTwoDiscsPL` | §L header, U1 (283-853), U2 (854-2543), U3 (2544-5231) | 4 972 | 352 | 46 | 35 s | 2 |
| `GaussTwoDiscsEars` | U4 (5232-10676) | 5 462 | 290 | 9 | 31 s | 0 |
| `GaussTwoDiscsAmbient` | U5 (10677-12600), U6 (12601-13006; `AmbientParam`), U7 (13007-13221), U8 (13222-16628), U9 (16629-18043; `InteriorOnLeft`, `CyclicPos`) | 7 385 | 600 | 30 | 35 s | 11 |
| `GaussTwoDiscsExtension` | U10 (18044-20290; `IsFinitePLOnFrontier`, `PreservesCyclicPos`), U11 (20291-20837) | 2 811 | 188 | 7 | 23 s | 2 |
| `GaussTwoDiscs` | **frozen BUNDLE block** (§5, `GaussTwoDiscsData`), the row `theorem lem_gauss_two_discs` (**frozen THM header**, body = the assembly from the leaves), §6 bridges `two_regions_plane`, `isPLDisc_of_isPLDiscSphere`, `isPLDisc_closure_interior` (20838-20912) | 92 | 5 | 0 | 20 s | 0 |

Total 20 996 lines, 1 467 declarations (unchanged from `W2_Assembled.lean`: no declaration was added, removed or renamed).  Each
module starts with the header line
`-- Ported <HH:MM>Z 2026-09-19 from work/drafts/twodiscs/W2_Assembled.lean by the pod executor (files prepared by the U12 assembler)`
(literal placeholder `<HH:MM>`), then its imports (`GaussTwoDiscsDefs`: the 14 imports of the assembled file — `SM.EmbeddedRotation`,
`SM.LinkMoves`, `SM.DeletedTuple` and 11 Mathlib modules; every other module: `import SM.<previous module>` only — imports are
transitive), a module docstring, `namespace SM`, `open Set OnePoint`, `variable {n : ℕ}`, the body, `end SM`.  The skeleton
vocabulary stays in the module of the unit section that introduced it (the split is at the section headers of the assembled
file, so every declaration keeps its relative order and no dependency crosses a module boundary backwards).  Every `section`,
`namespace u4h_SplitCtx`, `namespace u8h_AnnCtx/AnnData` and `variable … include` is closed inside its module; `open Filter`
(U5) and `open Classical … in` are section- or declaration-scoped.  Sizes are within the existing work/lean range (largest
registered module: `SM/CS7Units.lean`, 27 000 lines, 1 421 declarations).

## 2. Compile (module semantics, scratch object tree — nothing under work/lean)

Object tree `asm2/porttree/O/SM/` = symlinks to every `work/lean/.lake/build/lib/lean/SM/*` (olean/ilean) + the six new oleans.
From `work/lean`, in import order (`asm2/compile_port.sh`, log `asm2/compile_port.log`, per-module logs `asm2/port_<m>.log`):
```
lake env sh -c "LEAN_PATH=\"$O:\$LEAN_PATH\" lean --root=$ROOT -o $O/SM/<m>.olean ../drafts/twodiscs/port/SM/<m>.lean"
```
(`ROOT = work/drafts/twodiscs/port`, so the module name is `SM.<m>`).  Results: **all six exit 0, 0 errors**; wall 19 + 35 + 31 +
35 + 23 + 20 s = 2 min 43 s for the chain (14:46:40Z → 14:49:23Z), 15 warnings in all (§4).  Then `asm2/axioms_port.lean`
(`import SM.GaussTwoDiscs` + `#print axioms SM.<name>` for the 92 leaves, the row and the 3 bridges) against the tree: exit 0,
24 s, **96 × `[propext, Classical.choice, Quot.sound]`**, in particular
```
'SM.lem_gauss_two_discs' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.two_regions_plane' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.isPLDisc_of_isPLDiscSphere' depends on axioms: [propext, Classical.choice, Quot.sound]
'SM.isPLDisc_closure_interior' depends on axioms: [propext, Classical.choice, Quot.sound]
```
Forbidden strings: `grep -c "sorry\|#print\|#eval"` = 0 in every module (code and prose).  Frozen blocks:
`python3 port/check_57_identity_port.py` → `OK DEFS SM/GaussTwoDiscsDefs.lean`, `OK BUNDLE SM/GaussTwoDiscs.lean`,
`OK THM SM/GaussTwoDiscs.lean`, `IDENTITY OK` (the script reuses `blocks()` of `check_57_identity.py`; to re-point the original,
check DEFS against `SM/GaussTwoDiscsDefs.lean` and BUNDLE/THM against `SM/GaussTwoDiscs.lean`).

## 3. Renames and rewordings (the only differences from `W2_Assembled.lean` besides the split)

**Declaration names: none renamed** (leaf names `U<k>_…`, helper prefixes `u<k>h_`, the vocabulary and the row name
`SM.lem_gauss_two_discs` are as in the assembled file; the checker-relevant name is the row's).  Binder renames (unused
variables in helper signatures/lambdas, statements semantically unchanged): `u4h_exists_clean_invader` `hn → _hn`;
`u4h_tri_side_of_ends` `hk → _hk`; `u4h_lexmin_deleteVertex` `hP → _hP`; `u4h_ear_clean` `hn → _hn`; `u10h_marks_cover`
`hainc → _hainc`; in `u8h_AnnData.triangulation` the lambdas `fun T hT T' hT' … → fun _ hT _ hT' …` (×2); in
`u8h_AnnData.frontier_in_cover` `∃ h : A a b, → ∃ _ : A a b,`; in `u8h_A_cover` `fun y hy → fun _ hy`.

Prose rewordings (no `sorry` string, no wave markers): header `/-! # Row 57 … statement draft A (architect A, fidelity first)` →
`/-! # Row 57 lem:gauss-two-discs — definitions (frozen statement part §1-§4)`; "Not a module of work/lean; every leaf is
`sorry`." → "Ported to work/lean as the module chain `SM.GaussTwoDiscsDefs → …PL → …Ears → …Ambient → …Extension →
SM.GaussTwoDiscs`."; the draft check line → where the frozen blocks live; the three top-of-file notes (`W1 assembly note`,
`W2 assembly note`, `Skeleton note`) → one `## Provenance and assembly history` docstring in `GaussTwoDiscsDefs` (same facts:
inputs, merge method, the four rule-3 corrections, axioms, module chain); `/-! ## §L Leaves of the proof units (skeleton; every
leaf is `sorry`)` → `(all proved)`; the in-docstring markers `W1 ASSEMBLY (rule 3…)` (×3: `U3_isPositivePLFromPlane_inv`,
`U4_polygonImage_ear`, `U5_exists_ear_homeo`) and `W2 ASSEMBLY (rule 3, reported by U5)` (`U5_pushforward_edges`) →
`Assembly correction (wave 1/2, rule 3…)`, text otherwise unchanged.  Every other docstring and every proof is verbatim except
the warning clean-ups of §4.

## 4. Warnings: 80 in `W2_Assembled.lean` → 15 in the port

Cleaned (65 warnings, 56 within-line edits, all recompiled in the chain):
* 25 deprecations → the pin's replacement names, all exact aliases (same statement, checked with `#check` before editing):
  `Set.mem_setOf_eq → Set.mem_ofPred_eq` (×10), `Set.setOf_true → Set.ofPred_true`, `dif_pos → dite_eq_left` (×7),
  `if_pos → ite_eq_left` (×2), `if_neg → ite_eq_right` (×2), `continuousOn_iff_continuous_restrict → …_domRestrict` (×2),
  `ContinuousOn.restrict → ContinuousOn.domRestrict`.
* 5 `haveI → have` (goal is a Prop; U3 helpers).
* 18 unused `simp` arguments removed: `u4h_mkTri_v0/1/2` in two `simp only … at h0 h1` (U4, 6 warnings); `u8h_f_det_zero_right/
  left`, `u8h_f_det_self` (U8's fan-toolkit copy, 6); `u10h_det_zero_right/left`, `u10h_det_self` (U10, 6).
* 3 never-executed tactics removed (6 warnings): the alternative `| exact hne12 h1.symm` of one `first` (U4, second block);
  `<;> ring` after `field_simp` in `u8h_capInvFun_eq_ρ`-area lemma (Ambient 15082) and in the `u8h_f_ray … = u8h_ρ L c` lemma (15449).
* 11 unused variables in helpers (the binder renames of §3).

Remaining (15), all listed, none blocking:
* 10 unused variables in **leaf headers kept as printed** (the leaf statements are fixed by their consumers / the plan):
  `GaussTwoDiscsPL.lean:1660` `hx` (`U2_local_structure`); `GaussTwoDiscsAmbient.lean:1643` `hn`, `hP` and `:1649` `hedge`
  (`U5_exists_ear_homeo`), `:2260` and `:2266` `hn`, `hP` (`U6_exteriorRegion_eq`, `U6_interiorRegion_eq`);
  `GaussTwoDiscsExtension.lean:1900` and `:2760` `hD'` (`U10_boundary_map_of_lift`, `U11_boundary_homeo_of_lift`).
* 5 style notes "Used `tac1 <;> tac2` where `(tac1; tac2)` would suffice" on `… <;> field_simp <;> ring_nf <;> linarith`
  (`GaussTwoDiscsPL.lean:802`; `GaussTwoDiscsAmbient.lean:4246, 4253, 4262, 4269`): left as written — the `<;>` expresses
  "close whatever goals remain", and rewriting it as a sequence would encode the accidental goal count.

## 5. Notes for the executor

* Registration: row `lem:gauss-two-discs` → `SM.lem_gauss_two_discs` in module `SM.GaussTwoDiscs` (`lean-declarations.json`);
  the bridges for consumers are in the same module.  The wave-1 blocker (`SM.polygonImage` vs `SM.Rounding`) is gone: the
  namespace-aware clash scan of the assembled file against all of `work/lean` reports 0 clashes (W2_ASSEMBLY_REPORT.md §5).
* Build cost: the chain adds about 2 min 45 s of `lean` time to a full build (measured here on the 8-vCPU pod); the largest
  olean is `GaussTwoDiscsAmbient` (17.9 MB).
* Optional later clean-up (not done, no effect on correctness): U8's `u8h_f_` copy of U10's fan toolkit (73 declarations,
  byte-identical modulo prefix, W2_U8_REPORT.md §4) and U9's re-proof `u9h_cyclicPos_total` of `u10h_cyclicPos_total` could be
  deduplicated by moving U10's toolkit into `GaussTwoDiscsAmbient` before U8; the 10 leaf-header unused variables could be
  silenced only by changing leaf statements (not done: statements as printed).
