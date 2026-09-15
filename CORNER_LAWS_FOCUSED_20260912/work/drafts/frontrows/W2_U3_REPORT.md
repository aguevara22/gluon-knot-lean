# W2_U3 — unit U3 (record rows L-rec) report

File: `work/drafts/frontrows/W2_U3.lean` (= `Skeleton_W1.lean` + the U3 infrastructure section + the five
U3 leaf bodies).  Compile: `cd work/lean && lake env lean ../drafts/frontrows/W2_U3.lean` → 0 errors; the
only warnings are the 8 `declaration uses sorry` of the other units.

`grep -c sorry`: Skeleton_W1.lean 13 → W2_U3.lean 8.  The five remaining-vs-removed: the 8 left are
`typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move` (U6) and `deform_downCount`,
`deform_writhe`, `deform_P`, `represent` (U7).  `diff Skeleton_W1.lean W2_U3.lean` shows exactly 7 removed
lines (the five `sorry` bodies) and one inserted block (the section below); no statement, name, docstring or
definition was touched.

`#print axioms` (checked on a temporary copy, then regenerated): `comm_recordIso`, `zigzag_recordIso`,
`circle_recordIso_addFree`, `skein_site` use `[propext, Classical.choice, Quot.sound]`; `skein_unique`
uses `[propext, Quot.sound]`.

## Leaves

| leaf | status | proof route |
|---|---|---|
| `comm_recordIso` | proved | `U3.cm_recordIso_above` (above case) + the below case read as the above case of the pair `(b.reindex (b.idx + a.arity - a.coarity), a)` and `RecordIso.symm` (mirrors `IsComm.closed`); `IsComm`'s second disjunct by `symm`. |
| `zigzag_recordIso` | proved | `U3.zb_recordIso` / `U3.za_recordIso` (pure exterior passages, `U2.realize_recordIso_of_ext`). |
| `circle_recordIso_addFree` | proved | `U3.ci_recordIso` (exterior passage + the circle as the one free component, `U2.realize_recordIso_addFree_of_ext`). |
| `skein_site` | proved | site `x₀ = U3.siteX` (the interior `σ` slot of `A`); switch half `U3.sk_switchIso` (`recordIsoOfConjSwitch` on the active superset `ActE`, `IntPassage`); smoothing half `U3.sk_smoothIso` (`Record.smooth` as a first return of the reconnected permutation `gPerm`, `smoothCompsEquiv`, `PassageF`); sign `U3.siteX_sgn` + `U3.sk_writhe_factor` + `realize_writhe`, `run_skein_*`. |
| `skein_unique` | proved | `U3.two_appends_eq`, `U3.skeinStep_unique`, `U3.skeinStep_not_both` (word combinatorics: the block position is forced by the letter shapes). |

## Infrastructure (namespace `SM.FrontRows.U3`, section `/-! ### U3 infrastructure -/`, ~5.7k lines)

A. word combinatorics for `skein_unique`.
B. generic: `glueEquiv`, `conj_of_paths(_next)`, `recordIsoOfConj` — a record isomorphism of the full
   `σ`-slot records from conjugate first returns to *active supersets* `E ⊇ IsσSlot` (the U2
   `extRecordIso` is the case `E = ExtPiece`), and the switch variant `recordIsoOfConjSwitch`.
C. letter-local successor computations on a block (`next_σ_*`, `next_cusp_*`, `next_arm_*`, `pass_*`,
   `*_window`, `exit_vertex/right/left`, `block_col_*`, `letterAt_block`).
D–F. block passages; zigzag (below/above, 12-row tables `zb_T*`, `za_T*`); circle (`InCirc`, `circV`).
G. `IntSlot`, `ActE`, `φA` (glued exterior/interior correspondence), `IntPassage`, `conj_of_intPassage`.
H. cusp-skein: sites, `skφI`, `sk_intPassage`, `sk_switchIso`, `siteX_sgn`.
I–J. smoothing: `gPerm`, `reconnect_eq`, `smooth_succ_val_eq`, `smoothCompsEquiv`, `smoothRecordIso`,
   `PassageF`, `skG`, `skc_passageF`, `sk_ghexit`, `sk_smoothIso`, `sk_writhe_factor`.
K. commutation: `cm_*` block facts, `cmφI` (interior `σ` slots of the two letters, `cmφI_to/inv` with
   specs), `cm_left`/`cm_right` (entries), `cm_interior`, `cm_intPassage`, `hexit_of_comm`
   (`CExit`/`CDone`, `cexit_A..F`), `cm_slotIso`, `cm_recordIso_above`.

## Deviations from PLAN_FINAL §4 / U_U2_REPORT (recorded here, no statement changed)

1. The U2 report's suggestion for `comm_recordIso` ("a bijection of ALL slots of `W` and `W'`") is not
   realizable: the two words have different numbers of slots in general (e.g. `a = l`, `b = r`: the middle
   cut of `X a b Y` has two more strands than that of `X b a' Y`).  The proof instead conjugates the first
   returns to the active superset `ActE = ExtPiece ∨ IntSlot` (exterior pieces plus the interior `σ`
   slots), with `cmφI` matching the interior `σ` slots of `a`/`b` to those of `a'`/`b` and the passage
   split into entries (`cm_left`, `cm_right`) and interior departures (`cm_interior`).  The same
   machinery (`IntPassage`, `recordIsoOfConjSwitch`) is what `skein_site` needs, since the skein block has
   an interior crossing.
2. `skein_site`'s smoothing half uses the library form of `Record.smooth` (`succ = firstReturn (reconnect
   x) (SmoothKeep x)`, `comps = Quotient (SameCycle (reconnect x)) ⊕ FreeComp`) transported along the
   realization isomorphism (`smoothCongr`), and identifies the reconnected traversal of `A` with the
   traversal of `C` through the generic `smoothRecordIso` (conjugate first returns of `gPerm` and
   `nextPerm hC` on `E = ExtPiece`).
3. Lean lessons for later units: `rw` fails under implicit transparency on goals with anonymous
   constructors of def-wrapped Props (`IntSlot`, `ActE`) — use `exact` with explicit `Eq.trans`/`congrArg`
   or lemmas with explicit hypotheses; never `cases`/`subst` a section letter variable used in local
   notations (derive equalities like `hℓa2 := hℓa.trans hai` instead); `le_or_lt` is not available in this
   Mathlib pin (use `lt_or_ge` and swap branches).
