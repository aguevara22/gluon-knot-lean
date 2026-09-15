# W3 / U6 report — frontrows lane, unit U6 (`typeII_move`, `typeI_move`, `crossedCusp_move`)

File: `work/drafts/frontrows/W3_U6.lean` (copy of `Skeleton_W2.lean` with the U6 block installed and the
three U6 leaf bodies filled).

## Result

| leaf | row(s) | status | body |
|---|---|---|---|
| `crossedCusp_move` | 80/83 (`P_crossedCusp`) | **proved** | `U6.crossedCusp_move_proof h` |
| `typeI_move` | 77 (`P_typeI`) | **proved** | `U6.typeI_move_proof h` |
| `typeII_move` | 78 (`P_typeII`) | **proved** | `U6.typeII_move_proof h` |

No leaf was found false; no statement, name or docstring was changed.

* Full compile (`cd work/lean && lake env lean ../drafts/frontrows/W3_U6.lean`): **0 errors**, 1m34s wall.
  Remaining `declaration uses sorry` warnings: exactly two, `typeIII_site` (U5, L11100) and `represent`
  (U8R, L28896) — not mine.
* `grep -c sorry`: 5 at the start of the unit (`typeIII_site`, `typeII_move`, `typeI_move`,
  `crossedCusp_move`, `represent`) → **2** now (`typeIII_site`, `represent`).
* Axioms of the three leaves (checked with `#print axioms` on a copy of the file and, per variant, on the
  scratch builds): `propext`, `Classical.choice`, `Quot.sound` only.

## Where the helpers are (merger notes)

* ONE block, `/-! ### U6 infrastructure -/` at L11103, `namespace U6` (L11110) … `end U6` (L25426), placed
  immediately before the docstring of `typeII_move` (L25434) — i.e. after `typeIII_site` and before my
  first leaf. Full name space `SM.FrontRows.U6`; the block opens
  `SM.FrontRealize SM.FrontWord.Letter Equiv U2 U4` and uses `U3.*` lemmas by qualified name / `open U3`
  inside its sections. Everything in the block is `noncomputable section`.
* Nothing outside the block was touched except the three `sorry` bodies of my leaves (L25434 ff.).
* The block is ~14 300 lines. All names carry U6-local prefixes: `cl_`/`cr_`/`cc_`/`ccr_` (crossed cusp),
  `tl_`/`tu_`/`tI_`/`tL`/`tv`/`tw` (type I), `a_`/`aT`/`aC`/`aII_` (type II (a)), `c_`/`cT`/`cC`/`cII_`
  ((c)), `b_`/`bT`/`bC`/`bII_` ((b)), `d_`/`dT`/`dC`/`dII_` ((d)), `tIIL_`/`tIIR_` (type-II discs),
  generic assembly `RISpec`/`riData_of`, `RIISpec`/`riiData_of`, `genericData_of`/`genericData_of'`,
  `mvDiagram`/`rlDiagram`, `OnChain`, `NoMeet`/`OnlyAtJoint`, `ExtSl`, `ptv`, `isExtSlot_cut_left/right`.
  If a merger wants to move the block into its own file it needs `U2`, `U3`, `U4` (all of the skeleton up
  to L11084) and nothing after it.

## What the proofs do (design)

Common route (all three leaves). `realize W = realizeAt .std W.closed hne`; the moved diagram is
`D := mvDiagram .std hW hne mv K d = U2.mkDiagram … (vertsOf mv) (generic_of …) (ovMv …)` where `mv` moves
finitely many block vertices of the grid realization, `K := ExtCol X P` (the crossings kept are exactly the
exterior ones). The record isomorphism with `realize W'` is `U2.vertexMovedRecordIso'` fed with a
`SlotDiagramData` (from `U4.slotDiagramData_of` + the `hK` field), the block `Passage`, and the two `hexit`
facts (every component meets the exterior: `exists_ext_of_no_l/_no_r`, `exists_cusps_of_no_ext`).
The Reidemeister data is built once and for all at the slot level:

* `RISpec L pl hW mv K c` (one chain `c`, a kink) → `riData_of : Nonempty (RIData (polygon L) D (rlDiagram …))`.
* `RIISpec L pl hW mv K c₁ c₂` (two disjoint chains, two block crossings, the same over strand on one chain)
  → `riiData_of : Nonempty (RIIData (polygon L) D (rlDiagram …))`; the over/under visits are identified with
  `pt_ext'` (`overVisit_eq`/`underVisit_eq`, `overOn_of_chain`/`underOn_of_chain`).
* Each pattern only supplies finite checks: the classification `rest` (every slot is on a chain or is an
  unchanged spectator piece outside the disc), chain membership/interiority, same-column pair non-meeting
  (`NoMeet`/`OnlyAtJoint` by `linarith` on segment parameters), `touch` (a grid point in the disc is a chain
  vertex), `exits`, `hK`/`hKout`, and `kink`/`cross`.

Discs are convex polygons `polygon [xge, xle, yle, yge, above …]` hugging the block, with one or two slanted
sides cutting off the spectator strands that pass a cusp column diagonally (`tIIL`/`tIIR`, `tL`, `ccL`).

* **Crossed cusp** (`l_i d σ_i ↦ l_i (!d)` and `σ_i r_i ↦ r_i`): the two arm ends at the block cut are
  exchanged to heights `−i−3/4`, `−i−1/4` (`mv2`), one 4-piece chain, `RI` with disc `ccL`/`ccLr`.
* **Type I** (`l_m d σ_{m−1} r_m ↦ ∅`, `l_m d σ_{m+1} r_m ↦ ∅`): six moved vertices forming a shallow Z at
  heights `h ± 1/8, 3/8, 5/8` (`mvT`/`mvU`), one 9-piece chain, disc `tL k h` with two slants, `RI`.
* **Type II**, four variants of `IsTypeII` (`X ++ P ++ Y ↦ X ++ P' ++ Y`):
  * (a) `l_{m−1} d σ_m σ_{m−1} ↦ l_m d` (2 ≤ m): the through-strand `T` (3 pieces, entry `(|X|, m−1)`) is
    under at both crossings; its two interior vertices are lifted to height `h + 5/8` (`h = −(m−1)`), the
    cusp arc `C` (6 pieces) is unchanged; disc `tIIL`.
  * (c) `σ_{m−1} σ_m r_{m−1} ↦ r_m` (2 ≤ m): the mirror image; `T` is over at both crossings and its two
    interior vertices are lifted; disc `tIIR`.
  * (b) `l_{m+1} d σ_m σ_{m+1} ↦ l_m d` (1 ≤ m): `T` (over at both) is unchanged, the cusp arc is lifted:
    `(|X|+2, m+2) ↦ h − 3/8`, `(|X|+1, m+2) ↦ h + 1/8`, cusp `(|X|, 0) ↦ (|X|+1/2, h + 3/8)`,
    `(|X|+1, m+1) ↦ h + 5/8` (`h = −m`); disc `tIIL`.
  * (d) `σ_{m+1} σ_m r_{m+1} ↦ r_m` (1 ≤ m): mirror of (b); the cusp arc (over at both) is lifted; disc `tIIR`.
  The direction of `T` is `t := bit W |X| (idx)`, the direction of the cusp arc is the letter's bit `d` (left
  cusps) or `e := bit W (|X|+2) (idx)` (right cusps); chains are `tvTd/tvCd`-style vertex lists read forwards
  or backwards. `typeII_move_proof` dispatches on the four disjuncts of `IsTypeII`.

Order deviation: the task suggested typeI → typeII → crossedCusp along the `Curl.lean` template. That template
is the smooth-curve setting and does not apply to the grid realization, so I did crossedCusp → typeI → typeII
(simplest pattern first, then the generic RI assembly, then the RII assembly on top of it).

## API used

`U2`: `mkDiagram`, `SlotDiagramData`, `vertexMovedRecordIso'`, `Passage`, `entry_iff`, `isSlot_ext`, `extPair`,
`shiftIdx`, `ExtCol/ExtCut/IsExtSlot`, `SameEffect`, `sameEffect_of_replace`, `run_typeII_*`, `run_typeI_*`,
`run_crossedCusp_*`, `realize_eq_realizeAt`, `letterAt_block`, `slot_other`, `visit_ext`.
`U3`: `cutSlot_facts`, `vertex_not_crossing`, `next_right_lt/ge`, `next_left_lt/ge`, `next_σ_right_idx/succ`,
`next_σ_left_idx/succ`, `l_bits`, `r_bits`, `σ_facts`, `next_cusp_l/r`, `next_arm_l/r`, `bit_succ_of_lt/ge`,
`block_col_true/false/vertex`, `passage_step/end`, `slot_col_lt`, `bool_eq_of_not_ne`, `bool_eq_not_of_ne`,
`isSlot_cut`, `decomp`/`StepDecomp.length_add`, `exists_ext_of_no_l/_no_r`, `exists_cusps_of_no_ext`,
`sameCycle_of_iterate`, `exists_iterate_of_sameCycle`.
`U4`: `polygon`, `HalfPlane.*`, `mem_polygon_iff`, `mem_interior_polygon_iff`, `isDisc_polygon`, `SegIn/SegOut`,
`segIn_of_interior_left/right`, `segOut_of_lt`, `PieceIn/PieceOut`, `Unch`, `unch_pt`, `pieceOut_of_extCol`,
`MeetSpec` (+ `.symm`), `GenericData`, `generic_of`, `ovMv`, `slotDiagramData_of`, `realizeAt_data'`,
`realizeAt_diagram_eq`, `Chain`/`IsChain`/`toArc`/`arcCover_of`, `σSlotA/B`, `σSlotA_spec/B_spec`, `σpair`,
`crossingOf`, `crossingPoint_notMem_interior_iff`, `pt_ext'`, `std_pt_cut`/`std_pt_cusp` (block-local),
`pt_inj`, `nextPerm`, `next_prev`, `Chain.slot_succ/slot_zero`.

## Pitfalls met (for the merger / successors)

* `subst`/`rfl`-patterns eliminate the **right-hand** variable first: with `h : m' = m` the section variable
  `m` disappears (subsequent tactic text mentioning `m` fails with "unknown identifier"). State such
  equalities as `m = m'` (or `m - 1 = m'`).
* `cases d` on a Bool that occurs inside a `local notation` for the word is fine as long as the notation is
  not re-elaborated afterwards (`show … Va …` after `cases d` → "unknown free variable"); use
  `rcases Bool.eq_false_or_eq_true d with hd | hd` + `ite_eq_left/right` where the notation is needed.
* `include`/`omit`: an `include`d hypothesis is only pulled in when mentioned; unused-but-included variables
  give linter warnings and change signatures — `omit … in` per theorem. Many `omega` failures with
  "No usable constraints" were simply a missing `1 ≤ m`/`2 ≤ m`.
* `omega` treats `cut W (X.length + 1 + 1)` and `cut W (X.length + 2)` as different atoms; normalise with
  `rw [show X.length + 1 + 1 = X.length + 2 from rfl] at h`.
* `IsExtSlot` side goals via `simp only [IsExtSlot, …]; split_ifs <;> omega` are fragile (simprocs turn
  `X.length + 1 ≤ X.length` into `False` and `omega` then sees nothing); use `isExtSlot_cut_left/right`.
* `rw [h] at hb` where `h` also occurs in the word: `rw [hpe] at hbit` with `hpe : m - 1 = p` rewrites the
  `m - 1` inside the word too; `subst` instead.
* `first | exact L1 | … ` with dozens of alternatives times out; enumerate the same-column pairs explicitly
  (the pair blocks are generated; `interval_cases j <;> interval_cases j'` + `norm_num [colT, colC] at hc`
  dispatches the column mismatches).
* `Int.cast_injective`/`Nat.cast_injective` need both sides cast from the same type; non-grid heights are
  `-(n:ℝ) + 1 + o/8` with `o` odd (`nonGrid_eighth`), and half-integer x is handled by `NonGrid.ne_pt_half`.
* Mathlib names at this pin: `Set.mem_setOf_eq` deprecated, `push_neg` → `push Not`, `if_pos/if_neg` →
  `ite_eq_left/right`, `le_or_lt` unavailable (`lt_or_ge`).
