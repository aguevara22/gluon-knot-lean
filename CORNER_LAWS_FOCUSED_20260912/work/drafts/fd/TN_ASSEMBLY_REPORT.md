# TN_ASSEMBLY_REPORT.md — assembly of row 84 fd:transverse-neighborhood

Date: 2026-09-14.  Output: `work/drafts/fd/TN_Assembled.lean` (3150 lines, md5
`971744272f3dd9f9311767cf3f6b0351`).  Inputs: `TN_Skeleton.lean` (959 lines) and `TN_U_{A,B,C,D,E,F}.lean`
with their `TN_U_*_REPORT.md`.  Scripts: `TN_assemble.py` (assembly + repair, every step asserted),
`TN_clash_scan.py` (namespace-aware name-clash scan).  Nothing under `work/lean` was written or built;
the only compile command used was `cd work/lean && lake env lean ../drafts/fd/TN_Assembled.lean`
(and the same command on `/tmp` copies for `#print axioms` and the pass-1 control).

## Result in one line

**0 `sorry` (`grep -c sorry` = 0, also case-insensitive), 0 errors, 0 unproved leaves, 0 name clashes.**
`#print axioms SM.fd_transverse_neighborhood` = `[propext, Classical.choice, Quot.sound]` — no `sorryAx`.
The statement block (§1–§6) is byte-identical to `TransverseNeighborhood.lean` lines 67-238.
One deliberate deviation from the skeleton: its leaf C2 was **false as stated** and was replaced by the
repair unit C had prepared (§3 below); statements of every other declaration are unchanged.

## 1. Statement-freeze verification (task item 1)

`diff TN_Skeleton.lean TN_U_<u>.lean` (normal format) was parsed hunk by hunk.  Rule: a `c` hunk must
replace exactly one `  sorry` line; an `a` hunk is a pure insertion; a `d` hunk is accepted only if every
removed non-blank non-`sorry` line reappears verbatim and contiguously inside an `a` hunk of the same
unit (a relocation).  Hunks of different units may not touch the same skeleton line.

| unit | hunks | `sorry` lines replaced | removed non-`sorry` lines | helpers added | verdict |
|---|---|---|---|---|---|
| A | 8 (`258a`, `261c`, `268c`, `277c`, `285c`, `291c`, `298c`, `735c`) | 7 (A1–A7) | none | 16 (`ta_*`) | clean |
| B | 10 (`393a`, `396c`, `403a`, `408c`, `419a`, `425c`, `432c`, `466a`, `470c`, `477c`) | 6 (B1–B6) | none | 23 (`tb_*`) | clean |
| C | 11 (`521a`, `525c`, `557a`, `562c`, `569c`, `576c`, `584a`, `590c`, `610c`, `616c`, `626c`) | 8 (C1, C3–C9) | none | 22 (`tc1_*`, `tc2_*`, `tc3_*`, `tc6_*`, `tc9_*`) | clean; C2 left `sorry` (false, §3) |
| D | 9 (`682a`, `694c`, `704c`, `712c`, `723,729d`, `736a`, `743c`, `750c`, `757c`) | 7 (D1–D7) | 5 lines of `723,729d` = the D4 docstring + statement, re-inserted verbatim in `736a` | 14 (`td_*`) | clean (relocation) |
| E | 8 (`789c`, `793c`, `798c`, `804c`, `810c`, `816a`, `823c`, `832c`) | 7 (E1–E7) | none | 23 (`te_*`) | clean |
| F | 6 (`873a`, `879c`, `886c`, `891c`, `920a`, `927c`) | 4 (F1–F4) | none | 19 (`tf_*`) | clean |

No violation; nothing was rejected.  The relocation in D: the skeleton declares LEAF A7 `pullback_chart`
*after* LEAF D4 `Hmap_pullback`, which uses it; unit D moved the D4 block (docstring + statement, byte-
identical, plus its proof) to just after A7 (with the D4 helpers).  The assembler reproduces exactly that:
in the assembled file `pullback_chart` is at line 2213 (with unit A's proof) and `Hmap_pullback` at 2251.

## 2. Assembly (task item 2)

`TN_assemble.py`, pass 1: all 49 hunks applied in one pass over the skeleton (replacements at `c`,
insertions after `a`, the D deletion), then checked:
* every inserted block occurs in the result **exactly once, contiguously** (49/49);
* **117 distinct helper names**, none duplicated across units (each unit uses its own prefix), so no
  de-duplication or renaming was needed; the only skeleton name re-declared inside an insertion is the
  relocated `Hmap_pullback` (asserted);
* pass-1 result (`/tmp/tn_assembly/TN_Assembled_pass1.lean`, 3142 lines) compiles: 0 errors, exactly
  one `declaration uses sorry` (leaf C2) — the faithful control.

## 3. Unproved leaves (task item 3) — none; the false leaf C2 and its repair

After pass 1 the single remaining `sorry` was LEAF C2

```
theorem hasCompactSupport_Yfield {ρ : ℝ} (hρ : GoodRadius T ρ) : HasCompactSupport (Yfield T ρ)
```

which is **false**: `Yfield T ρ q = (chiTau q.1, (chiTau q.1 * cutoff ρ q.2) • Vf T q.1 q.2)` has first
component `χ_τ(τ)`, independent of `p` and equal to `1` for `|τ| ≤ 2`, so `Yfield T ρ (0, p) ≠ 0` for every
`p`.  Unit C kernel-checked this as `tc2_not_hasCompactSupport_Yfield : ¬ HasCompactSupport (Yfield T ρ)`
(assembled line 1113, axiom-clean) and supplied the repair (`TN_U_C_REPORT.md` §2).  A `sorry` on a false
statement cannot be proved and would leave `sorryAx` in the row theorem, so pass 2 applies the repair
(each edit an exact-match replacement asserting a unique occurrence; delta vs pass 1: 89 lines removed,
98 added, all inside Unit C plus the module docstring):

1. the C2 block (docstring, statement, `sorry`) is removed and replaced by a `/-! … -/` note (line 1194);
2. `isGlobalFlow_Theta` (statement unchanged, line 1273) is proved by
   `Classical.epsilon_spec (tc2_exists_isGlobalFlow hT hρ)` — existence of the global flow from
   boundedness + global Lipschitz continuity (row 86's `ContactMotions.exists_isGlobalFlow`) instead of
   compact support;
3. `contDiff_Theta` (statement unchanged, line 1279) is proved by
   `obtain ⟨L, hL⟩ := tc2_exists_bound hT hρ; exact tc9_contDiff_uncurry_of_bounded (contDiff_Yfield hT hρ) hL (isGlobalFlow_Theta hT hρ)`
   — joint smoothness of the flow of a bounded smooth field, unit C's localisation of row 86's
   `ContactMotions.contDiff_uncurry` (axiom-clean, general finite-dimensional `E`);
4. `section tc9_localization … end tc9_localization` (68 lines; depends only on `SM.ContactMotions`) is
   moved from after C8 to just before `isGlobalFlow_Theta` (line 1203) so that (3) can see it.

Nothing else referenced `hasCompactSupport_Yfield` (checked by grep over all six unit files: only the
skeleton's two consumers above).  Not done, deliberately: cutting off the first component of `Yfield`
as well — that would make C3 (`τ = t` for every `p`) and C5 (`Φ₁` a global diffeomorphism) false.

Unproved leaves remaining: **none**.  Own proving time spent: 0 (the repair used unit C's helpers only).

## 4. Compile, `sorry` count, axioms (task item 4)

`cd work/lean && lake env lean ../drafts/fd/TN_Assembled.lean`: **exit 0, 0 errors**, 4 warnings, all
`Variable name … is not explicitly referenced` on frozen leaf statements whose proofs did not need the
hypothesis: `hN` in E5 `embedded_L` (line 2580), `hκ` in E7 `transverselyIsotopic_pushoff` (2762), `hN`
in F2 `contDiff_pushfwd` (3020) and F3 `hasCompactSupport_pushfwd` (3032).  Left as-is (statements
frozen; harmless).  ≈ 26 s with three compiles in parallel.

`grep -c sorry TN_Assembled.lean` = **0** (`grep -ci` = 0 as well; the module docstring was rewritten and
no docstring or comment contains the word).  No `#print`, `#eval`, `#check`, `set_option`, `#exit` or
`axiom` line is present.

`#print axioms` on the `/tmp` copy `/tmp/tn_assembly/TN_Assembled_axioms.lean` (the file plus seven
`#print axioms` lines after `end SM`):

| declaration | axioms |
|---|---|
| `SM.fd_transverse_neighborhood` | `[propext, Classical.choice, Quot.sound]` |
| `SM.TransverseNeighborhood.model` (D1–D7 assembled) | same |
| `SM.TransverseNeighborhood.exists_legendrian` (E1–E7) | same |
| `SM.TransverseNeighborhood.ambientIsotopy` (F1–F3) | same |
| `SM.TransverseNeighborhood.isGlobalFlow_Theta` (repaired) | same |
| `SM.TransverseNeighborhood.contDiff_Theta` (repaired) | same |
| `SM.TransverseNeighborhood.tc2_not_hasCompactSupport_Yfield` (the counterexample to C2) | same |

No `sorryAx` anywhere.

## 5. Byte identity of the statement (task item 5)

Assembled lines 31–202 (from `namespace SM` through the last line of `TransverseNeighborhoodData`, 172
lines) were compared with `TransverseNeighborhood.lean` lines 67–238 by `cmp`: **byte-identical**.
(The skeleton's lines 27–198 are the same block; the four-line shift comes from the longer module
docstring.)  Row theorem: `SM.fd_transverse_neighborhood : TransverseNeighborhoodData` (line 3133), the
skeleton's name; `axiom-policy.json` fixes no declaration name for this row.

## 6. Name-clash scan (task item 6)

`TN_clash_scan.py` indexes every non-private top-level declaration of the 654 `.lean` files under
`work/lean` (13,703 declarations), tracking `namespace`/`section`/`end` (block comments skipped), and
compares with the 254 fully-qualified names of `TN_Assembled.lean` (250 in `SM.TransverseNeighborhood`;
`SM.TransverseNeighborhoodHyp`, `SM.TransverseNeighborhoodConclusion`, `SM.TransverseNeighborhoodData`,
`SM.fd_transverse_neighborhood` directly in `SM`):
* exact fully-qualified clashes: **0**;
* short-name shadows in an enclosing namespace (`SM.<x>` or root `<x>` for an `SM.TransverseNeighborhood.<x>`): **0**;
* pre-existing `SM.TransverseNeighborhood*` declarations in `work/lean`: **0** (namespace new);
* duplicate names inside the assembled file: **0**;
* informational (unrelated namespaces, no ambiguity): `alpha` ~ `SM.ContactMotions.alpha` (the file opens
  `ContactMotions` only for `IsGlobalFlow`, so `alpha` resolves to the local one — the clean compile
  confirms), `chart` ~ `SM.RPC.chart`, `SM.SpatialLink.GermData.chart`, `chart_core` ~
  `SM.SpatialLink.Choices.chart_core`, `GoodRadius`/`exists_goodRadius` ~ `RProof.G1.*`.
* sanity: the `SM.ContactMotions` names the file relies on (`IsGlobalFlow`, `contDiff_uncurry`,
  `exists_isGlobalFlow`, `globalFlow`, `ODE_unique_global`) are found in the index.

## 7. Module docstring / directives (task item 7)

Since the `sorry` count is 0 the header docstring was rewritten (assembly provenance, layout, the C2
deviation, the axioms line); the word does not occur anywhere in the file.  There were no `#print`/`#eval`
lines to remove (the units had none).

## 8. Notes for the integrator

* To move into `work/lean`: the file is self-contained over `SM.ContactMotions` and the four Mathlib
  imports; `TransverseNeighborhood.lean` (statement-only) is not in `work/lean`, so the assembled file can
  become `SM/TransverseNeighborhood.lean` directly (statement block untouched, as required by the freeze).
* The frozen leaf statements carry three unused hypotheses (`hN` in E5, F2, F3; `hκ` in E7); if the
  linter warnings are unwanted in `work/lean`, renaming to `_hN`/`_hκ` changes no statement.
* Pass-1 (faithful, one `sorry`) and the `#print axioms` copy are kept under `/tmp/tn_assembly/` for
  inspection; they are not part of the deliverable.
