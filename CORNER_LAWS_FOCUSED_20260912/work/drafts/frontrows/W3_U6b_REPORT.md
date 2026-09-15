# W3_U6b report — frontrows lane, unit U6b (leaf `typeII_move`)

File: `work/drafts/frontrows/W3_U6b.lean` (copy of `W3_U6.lean` as of 2026-09-14 16:52 UTC — the U6 block
L11103-22210 with `typeI_move`, `crossedCusp_move` proved and `typeII_move` left `sorry` — plus ONE new block).
Compile: `cd work/lean && lake env lean ../drafts/frontrows/W3_U6b.lean` → **0 errors** (log `/tmp/u6b/full.log`,
1m45s wall on the pod; the only `declaration uses sorry` warnings are L11100 `typeIII_site` and L28902 `represent`). `grep -c sorry`: **3 → 2** (`typeIII_site` L11101 — unit U5 — and `represent` L28904 — unit U8R —
untouched).

## Result

| leaf | statement row | status | body |
|---|---|---|---|
| `typeII_move` (L25440) | P_typeII → row 78 ng:front-II, row 83 | **proved** | `U6b.typeII_move_proof h` |

No statement, name or docstring was changed; the only edit outside the new block is the `sorry` body of
`typeII_move` (now L25442). Axioms (`#print axioms` on the copy `/tmp/u6b/W3_U6b_axioms.lean`, log
`/tmp/u6b/axioms.log`): `SM.FrontRows.typeII_move` depends on `[propext, Classical.choice, Quot.sound]` (likewise `typeI_move`, `crossedCusp_move`, `U6b.typeII_b`, `U6b.typeII_move_proof`). `SM.lp_lm` is not involved.

## IMPORTANT: duplication with `W3_U6.lean`

While this unit was running, the U6 unit kept working on its own copy and completed the same leaf there:
`W3_U6.lean` (29 216 lines, 2 sorries, `end U6` at L25426, `typeII_move := U6.typeII_move_proof h` at L25434;
its `W3_U6_REPORT.md` was rewritten at 17:15 UTC). Both copies share the identical prefix L1-22207. The merger
therefore has two complete files for the same leaf:

* `W3_U6.lean`: everything inside `namespace U6` (its own (b) sections H3-H5 and (d) sections I1-I5, dispatch J).
* `W3_U6b.lean` (this file): the same prefix, then the new block `namespace U6b` (below) containing MY proof of
  variant (b) (written independently before the duplication was noticed; same design, same vertex tables as
  the U6 report prescribed) and, for variant (d), the U6 sections I1-I5 + J **taken verbatim from
  `W3_U6.lean` L23475-25424** (per the folder rule "kernel-checked drafts are reused, not redone"), with two
  one-token edits (see below).

Either file closes the leaf with the standard axioms. Taking `W3_U6.lean` wholesale is the simpler merge (one
block, one namespace); this file is the fallback / cross-check. Do NOT merge both blocks into one file: the (b)
material would then exist twice (`U6.pvA3` and `U6b.pvA3`, …) — harmless but pointless.

## Where the new material is (for the merger: hunks relative to `W3_U6.lean`-as-of-16:52 = this file's prefix)

ONE block, `/-! ### U6b infrastructure -/` L22212 … `namespace U6b` L22218 … `end U6b` L25432 (3 221 lines),
placed immediately after `end U6` (L22210) and before the docstring of `typeII_move` (L25434). Header:
```lean
namespace U6b
open SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4 U6
noncomputable section
```
All declarations are `SM.FrontRows.U6b.*`; the block depends only on L1-22210 (developed against a prefix olean
of exactly those lines, `/tmp/u6b/olean/U6bPrefix.olean`; scratch pieces `/tmp/u6b/B1.lean B2.lean B3.lean
D_all.lean`, assembled by `/tmp/u6b/mk.sh`).

| lines | section | content |
|---|---|---|
| 22224-22431 | B1: `MvIIb`, `IIbVertices` | `pvA3` (T fixed: `(k,h),(k+1,h),(k+2,h−1),(k+3,h−2)`), `pvB3`/`mvB3` (cusp arc, realized / lifted: indices 1-4 ↦ `(k+2,h−3/8),(k+1,h+1/8),(k+1/2,h+3/8),(k+1,h+5/8)`), `IsMovedB`, `mvIIb` + `mvIIb_of_not_moved/v1-v4/of_ext/xcoord/injective` (`nonGrid_eighth (n+1) o`, `o ∈ {−3,1,3,5}`, `NonGrid.ne_pt`/`ne_pt_half`), membership `pvA3_int/mem`, `pvB3_int/mem`, `mvB3_int/mem` (disc `tIIL k h`, `h = −m`), macro `bII_pair`, `bII_NM_T0C2 … bII_NM_C0C5`, `bII_OJ234` |
| 22435-22865 | B2: `TypeIIbSpec` | `bMv`, `b_pt_T/C`, `b_mv_T/C`, `tvT3_inj`, `tvC3_inj`, `tvT3_ne_tvC3`, `bT_mv_slot/pt_slot`, `bC_mv_slot/pt_slot`, `bT/bC_next_slot`, `b_segIn_key`, `bT/bC_chain_in`, `bT/bC_vert`, `b_moved`, `bT/bC_chain_of`, `b_spec`, `b_hmv`, **`b_rest`** (the classification; spectator table as in the U6 report: cut `k` `p<m` above / `p=m` T0 / `p≥m+1` `tIIL_out_slant`; cuts `k+1`,`k+2` `p∈{m,m+1,m+2}` chain slots, `p≥m+3` below; leftward cut `k+1` `q≥m+3` `tIIL_out_slant'`) |
| 22869-23474 | B3: `TypeIIbSpec2` | `bT/bC_slot_ne`, `b_disj`, `b_prevOut₁/₂`, `b_stopOut₁/₂`, `b_vertex_of_mem` (bounds `2p ≤ 2m+5`, `4m ≤ 4p+3`, `4p+8k ≤ 4m+3+8j`), `b_touch`, `b_exits` (`exists_ext_of_no_r`), `b_σcol`, `b_σA_chain` (T is the over strand at both block crossings), `b_hK` (←: the under slot is `(k+1,m+1)` / `(k+2,m)→(k+1,m+1)` via `b_A16`, or `(k+2,m+2)` / `(k+3,m+1)→(k+2,m+2)` via `b_A20`), `b_hKout`, `b_cross` (first disjunct), `b_pairs_TT/TC/CC`, `b_pairs`, `b_genericData`, `b_riiSpec`, `b_riiData`, `b_recordIso` (`vertexMovedRecordIso' X Pb Y Pb' … (b_passage …) (b_hexit …) (a'_hexit X Y m d hW')`), **`typeII_b`** (L23463) |
| 23476-23480 | provenance note for the (d) part | |
| 23481-23912 | I1: `TypeIIdWord` (from `W3_U6.lean`) | `tvT4/tvC4/tvTd4/tvCd4`, `d_letters … d_bits`, `d_A1..d_A22`, `d_hexit`, `dT`, `dC`, `dT/dC_slot_val`, `dT/dC_col`, `dT_col3`, `dC_col6` |
| 23916-24149 | I2: `TypeIIdPassage` (from `W3_U6.lean`) | `d_passage` (target word `X ++ [r m] ++ Y`: the `c'_L1..L6`, `c'_extCol` of the (c) files) |
| 24151-24366 | I3: `MvIId`, `IIdVertices` (from `W3_U6.lean`) | `pvA4`, `pvB4`, `mvB4`, `IsMovedD`, `mvIId`, memberships in `tIIR k h`, `dII_pair`, `dII_NM_*`, `dII_OJ234` |
| 24370-24804 | I4: `TypeIIdSpec` (from `W3_U6.lean`) | `dMv`, …, `d_rest` |
| 24808-25416 | I5: `TypeIIdSpec2` (from `W3_U6.lean`) | …, `d_cross`, `d_pairs_*`, `d_genericData`, `d_riiSpec`, `d_riiData`, `d_recordIso`, **`typeII_d`** (L25405) |
| 25418-25430 | J (from `W3_U6.lean`) | **`typeII_move_proof`**: `obtain ⟨X, Y, m, ⟨d, hm, hWeq, hW'eq⟩ | ⟨d, hm, hWeq, hW'eq⟩ | ⟨hm, hWeq, hW'eq⟩ | ⟨hm, hWeq, hW'eq⟩⟩ := h` then `typeII_a / typeII_b / typeII_c / typeII_d` |

Edits made to the copied (d) text: `σSlotA_val`/`σSlotB_val` → `U6.σSlotA_val`/`U6.σSlotB_val` (4 occurrences;
inside `U6b` both `U3.σSlotA_val` and `U6.σSlotA_val` are visible, so the bare name is ambiguous — the same
edit was needed in my (b) sections). Nothing else.

## Variant (b) geometry as proved (mine)

`W = X ++ [l (m+1) d, σ m, σ (m+1)] ++ Y`, `W' = X ++ [l m d] ++ Y`, `1 ≤ m`, `k = |X|`, `h = −m`, disc
`tIIL k h`. Through-strand `T = tvT3` `(k,m),(k+1,m),(k+2,m+1),(k+3,m+2)` **unmoved**, over at both block
crossings (columns `k+1`: `σ_m`, `k+2`: `σ_{m+1}`; `σSlotA` values `(k+1,m)/(k+2,m+1)` and `(k+2,m+1)/(k+3,m+2)`
by `t`). Cusp arc `C = tvC3` `(k+3,m+1),(k+2,m+2),(k+1,m+2),(k,0),(k+1,m+1),(k+2,m),(k+3,m)`: indices 1-4 lifted
to `(k+2,h−3/8),(k+1,h+1/8),(k+1/2,h+3/8),(k+1,h+5/8)`, so the moved arc runs above `T` everywhere; same-column
pairs `(T0,C2),(T0,C3),(T1,C1),(T1,C4),(T2,C0),(T2,C5)`, `(C0,C5)`, `(C1,C4)` are `NoMeet`, `(C2,C3)` meets only at
the cusp joint (`OnlyAtJoint`) — each by `linarith` on the segment parameters (`bII_pair`). Injectivity of the
move: the four heights `h + o/8`, `o ∈ {−3,1,3,5}` odd, are non-grid (`nonGrid_eighth (m+1) o`, since
`h = −(m+1) + 1`), the cusp image sits on the half-integer vertical `k + 1/2` (`ne_pt_half`). Record iso
exactly as in `a_recordIso` with the (b) passage/hexit of the block and `a'_hexit` for `X ++ [l m d] ++ Y`.

## Pitfalls met (in addition to the U6 report's list)

* Inside `namespace U6b` with `open U3 … U6`, `σSlotA_val`/`σSlotB_val` are ambiguous (both `U3` and `U6` define
  them with the same statement): qualify.
* A `local notation "hB" => (-(m : ℝ))` shadows the pattern variable name `hB` in `rintro ⟨-, hB⟩` and in
  `fun … hB => …` ("unexpected token 'hB'; expected rcasesPat" / a type mismatch with `-m`): use other names.
* A generic `SegIn`-from-tables helper (`b_segIn_key`, parameter `n`) needs `2 ≤ n` explicitly for the
  `omega` side goals; and under `include hW ht` such a helper silently acquires `Y d t hW ht` as arguments
  through `hW` — `omit hm hW ht in` keeps its signature `X m n …`.
* `m + 1 + 1` vs `m + 2` after `σSlotB_val` at the `σ_{m+1}` column: `rw [show m + 1 + 1 = m + 2 from rfl, D6]`.
* Scratch iteration against the 22 210-line prefix olean takes 10-20 s per piece; the full file takes ≈ 1.5 min.

## Notes for the merger

* The block introduces no axioms, no `sorry`, no `unsafe`; nothing outside `namespace SM.FrontRows.U6b` changed
  except the one leaf body.
* If `W3_U6.lean` is taken instead, this file is superseded entirely (its prefix is a strict prefix of that file).
