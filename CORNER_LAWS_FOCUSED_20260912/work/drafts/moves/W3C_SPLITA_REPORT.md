# W3C_SPLITA_REPORT — unit SPLITA (prefix `w3ca_`): `esc_FullSplitData` fields `touching_iff`, `distinct`, `central_no_piece`, `central_rot`

Prover subagent, 2026-09-15, 23:19–00:00 UTC / 7:19–8:00pm ET (bounded window A-177-2, hard stop 01:45 UTC).
File: `work/drafts/moves/W3C_SPLITA.lean` (12867 lines = `W3B_Assembled.lean` 11851 + ONE pure insertion of 1016 lines,
`diff W3B_Assembled.lean W3C_SPLITA.lean` = `10671a10672,11687`, placed inside `section W3BI_REAL` immediately before the
docstring of the leaf `w3bi_esc_outer_data`).  No frozen statement, name or docstring touched; no other unit's `sorry`
touched; the leaf `w3bi_esc_outer_data` itself is untouched (its Prop `w3bi_esc_outer` also demands `writhe`, `mixed`,
`outer_alternative`, `uniform`, `knot_after_two`, `three_components` — SPLITB/SPLITC/KNOT).

## Compile / checks (mandated)

* `cd work/lean && lake env lean ../drafts/moves/W3C_SPLITA.lean` → exit 0, **0 errors**, 35 s warm; exactly the base's
  **7** `declaration uses sorry` warnings (`w3g_bigonData_smooth_arcST/TS`, `w3bi_esc_outer_data`, `w3bi_site_data_data`,
  the two `_switch_z` forms, one G11 placeholder) — the inserted block is sorry-free.  Other warnings: the base's
  deprecation notes (`if_pos`/`if_neg`) plus the `unusedSectionVars` lint on `w3ca_geoIndependent_mono` (harmless).
* `grep -c sorry`: **8 before → 8 after** (no leaf closed: `w3bi_esc_outer_data` needs the other units' fields; the
  inserted block contains no `sorry`).
* `check_W3_identity.py Port_GenericTransportSw_draft.lean W3C_SPLITA.lean`: `structure G11_ConfigSw`, `namespace
  G11_ConfigSw block`, `def G11_core_sw_statement`, `theorem G11_core_sw (statement)`, `theorem esc_switch_riii_of_chain`
  all **IDENTICAL**; `imports = draft's + SM.BigonDeletion: False` is the known artifact (the file imports
  `RProof.RALedgers`, W3B_ASSEMBLY_REPORT §8), `G11_core_sw body starts with sorry: False` as in the base.
* `check_W3_statements.py W3C_SPLITA.lean`: 42 skeleton statements, **42 byte-identical**, `w3a_` count 20, no missing
  declaration names.
* `#print axioms` (scratch copy `W3C_SPLITA_Axioms.lean` in the prover's scratchpad, 0 errors): `w3ca_split_at_outer`,
  `w3ca_central_rot_at_outer`, `w3ca_marks_partition_config`, `w3ca_core`, `w3ca_pattern`, `w3ca_six_on_contact` each depend on **`[propext, Classical.choice, Quot.sound]`
  only** (no `sorryAx`, not even the HOMFLY axioms).  `w3bi_extreme_selected` unchanged (still `sorryAx` through the
  open leaves).
* Name-clash scan: `w3ca_` occurs nowhere in the base or under `work/lean`; no `#print`/`#eval` in the deliverable.

## CLOSED (all four fields of this unit, at the configuration of `w3bi_esc_outer`)

For the empty side `t'`, `Q' = transportSupport hs Q`, `T' = triangleCrossings (E.curve t') e f g`, `S' = Q' ∪ T'`,
`hP' = geomAt E t' ht'.1`, `hef' = (hs _).mp hef` etc., with the four carriers

    A := w3ca_A hP' S' hef' heg' hfg'    B := w3ca_B hP' S' hef' heg' hfg'
    C := w3ca_C hP' S' hef' heg' hfg'    Z := w3ca_Z hP' S' hef' heg' hfg'      (all : GeoComponent hP' S')

* **`w3ca_split_at_outer`** (line 11508; binders = those of `w3bi_esc_outer` that the fields see: `E e f g δ hL t t' ht ht'
  hop hs hef heg hfg Q hQ hfull hS'`): `touching_iff` (`∀ q, ¬ TriangleDisjoint hP' S' e f g q ↔ (q = A ∨ q = B ∨ q = C ∨
  q = Z)`) ∧ `distinct` (`A ≠ B ∧ A ≠ C ∧ A ≠ Z ∧ B ≠ C ∧ B ≠ Z ∧ C ≠ Z`) ∧ `central_no_piece` (`CV.piecesOn hP' S' Z = ∅`),
  verbatim the three field types of `esc_FullSplitData hn (genericAt E t' ht'.1) e f g hQi' hS' q₀' A B C Z Λ`.
* **`w3ca_central_rot_at_outer`** (line 11637; same binders + `hn`): `CV.carrierR hn (genericAt E t' ht'.1) hS' Z = 1`
  = the field `central_rot`.

Neither needs `q₀'`, `hQi`, `hQi'`, `GenericTableData`, `AV_EventRadius` or `CompleteLocal`; the assembler instantiates
them at the leaf's binders and pairs them with SPLITB (`writhe`, `mixed`), SPLITC (`outer_alternative`, `uniform`) and KNOT
(`knot_after_two`, `three_components`) on the SAME `A B C Z`.

## OPEN in this unit

Nothing.  (The leaf `w3bi_esc_outer_data : w3bi_esc_outer` stays `sorry`: its remaining conjuncts belong to SPLITB, SPLITC,
KNOT.)

## Black boxes / interface Props stated

None — no `w3ca_` Prop with `sorry` was needed; nothing from another unit was assumed.

## The four carriers, for SPLITB / SPLITC / KNOT (the outputs to refer to by name)

Visits (all on the polygon `P = E.curve t'`, `a = xPair hef' = x_ef`, `b = xPair heg' = x_eg`, `c = xPair hfg' = x_fg`):

    a₁ = visitOn a e (mem_pair_left e f)    a₂ = visitOn a f (mem_pair_right e f)
    b₁ = visitOn b e (mem_pair_left e g)    b₂ = visitOn b g (mem_pair_right e g)
    c₁ = visitOn c g (mem_pair_right f g)   c₂ = visitOn c f (mem_pair_left f g)

Edge adjacencies (R-LOC-2 (2b), `GT_adjacent_of_shared` + `GT_succ_of_adjacent`, with `σ = geoMarkSuccessor hP'`):
`σ a₁ = b₁ ∨ σ b₁ = a₁` (edge `e`), `σ b₂ = c₁ ∨ σ c₁ = b₂` (edge `g`), `σ c₂ = a₂ ∨ σ a₂ = c₂` (edge `f`).

**`w3ca_pattern`** (line 10735): from the independence of `S'` alone, the three adjacencies are coherently oriented —
either **P1** `σ a₁ = b₁ ∧ σ b₂ = c₁ ∧ σ c₂ = a₂` (the traversal word `a_e b_e | b_g c_g | c_f a_f`) or its mirror **P2**
`σ b₁ = a₁ ∧ σ c₁ = b₂ ∧ σ a₂ = c₂`.  Since `succ_{S'} v = σ (visitTwin v)` at a selected visit, in P1 the smoothing
successor of `S'` has the 3-cycle `a₂ → b₁ → c₁ → a₂`, in P2 the 3-cycle `b₂ → a₁ → c₂ → b₂`.

Definitions (lines 10925–10948 abstract, 11404–11431 concrete; `Zc/Ac/Bc/Cc` take the visits, `Z/A/B/C` take
`hef heg hfg` and plug the six visits above):

    w3ca_Z hP S hef heg hfg = if σ a₁ = b₁ then geoOwner hP S (inr a₂) else geoOwner hP S (inr a₁)
    w3ca_A hP S hef heg hfg = if σ a₁ = b₁ then geoOwner hP S (inr a₁) else geoOwner hP S (inr a₂)
    w3ca_B hP S hef heg hfg = if σ a₁ = b₁ then geoOwner hP S (inr b₂) else geoOwner hP S (inr b₁)
    w3ca_C hP S hef heg hfg = if σ a₁ = b₁ then geoOwner hP S (inr c₂) else geoOwner hP S (inr c₁)

So `A` is the outer carrier through the outer visit of `x_ef`, `B` through the outer visit of `x_eg`, `C` through the outer
visit of `x_fg`, `Z` the central triangle (the inner visits).  In P1: `Z ∋ a₂, b₁, c₁`; `A ∋ a₁`; `B ∋ b₂`; `C ∋ c₂`.  In P2:
`Z ∋ a₁, b₂, c₂`; `A ∋ a₂`; `B ∋ b₁`; `C ∋ c₁`.

**What SPLITB/SPLITC can consume directly** (all at a generic punctured parameter `t`, so also at `t'`):
* `w3ca_split_config hL ht hef heg hfg hQ hfull hS` (line 11436): `w3ca_CoreData hP S a₁ … c₂ A B C Z ∧ touching_iff ∧
  distinct ∧ central_no_piece` — `w3ca_CoreData` (line 10904) has fields `six` (every one of the six visits is owned by
  `A`, `B`, `C` or `Z`), `hitA/hitB/hitC/hitZ` (each of the four owns one of the six), `distinct`, and `central`:
  `∃ zA zB zC, zA.1 = a ∧ zB.1 = b ∧ zC.1 = c ∧ ∀ m, geoOwner hP S m = Z ↔ (m = inr zA ∨ m = inr zB ∨ m = inr zC)` — the
  marks of `Z` are EXACTLY three selected visits, one per triangle crossing (this is what gives `piecesOn Z = ∅` and
  `geoCornerCount Z = 3`).
* `w3ca_sixData_config hL ht hef heg hfg hQ hfull : w3ca_SixData …` (line 11355): twins, `a b c ∉ Q`, the adjacencies.
* `w3ca_pattern hP D hS` for the orientation case split (`hS : GeoIndependent hP (insert c (insert b (insert a Q)))`,
  classical `insert`, see pitfall 1).
* `w3ca_cornerCount_three` (line 11570, generic), `w3ca_carrierR_of_three` (line 11599: three corners ⇒ `carrierR = 1`),
  `w3ca_rotAbs_three` (line 11562: `c = 3 → rotAbs L hL = 1`, from `CV.rot_triangle`).
* **`w3ca_marks_partition_config hL ht hef heg hfg hQ hfull hS q₀ hq₀ m`** (line 11656; `q₀` any triangle-touching
  carrier of `Q`): `(owner_S m = A ∨ owner_S m = B ∨ owner_S m = C ∨ owner_S m = Z) ↔ owner_Q m = q₀` — the marks of
  `A ∪ B ∪ C ∪ Z` are exactly the marks of the contact carrier (for the piece/writhe ledgers of SPLITB and the component
  identification of KNOT).  Abstract form `w3ca_marks_partition` (line 11196; three insertions,
  `geoComponentForgetSwitch_fiber_affected` on the affected block, `geoOwner_insert_iff_of_unaffected` on the rest);
  `w3ca_six_on_contact` (line 11145): all six visits lie on `owner_Q a₁` from independence + adjacency alone (so
  `esc_contact_owns` is not needed).
* Intermediate ownership facts the writhe/selector units may want are INSIDE the proof of `w3ca_core` (line 10950): on
  `Q₁ = insert a Q'`: `owner₁ a₁ ≠ owner₁ a₂`, `owner₁ b₁ = owner₁ b₂`, `owner₁ c₁ = owner₁ c₂`, and in P1 `owner₁ b₁ = owner₁
  a₂ = owner₁ c₂` (b, c on the `a₂` daughter); on `Q₂ = insert b Q₁`: `owner₂ b₁ ≠ owner₂ b₂`, `owner₂ c₁ = owner₂ c₂`, in P1
  `owner₂ b₁ = owner₂ a₂ = owner₂ c₂`.  They are `have`s, not exported theorems; export on request (each is one line from
  `w3ca_owner_of_succ` + `geoIndependent_remaining_pair_owners` / `geoIndependent_selected_pair_owners_ne`).

## Route actually used (vs the U_R177_REPORT "What remains" item 4 estimate ≈ 3–5k for all fields)

1016 lines for four fields plus the marks partition, no geometry beyond the library.  The two ideas that made it short:

1. **The orientation pattern needs no traversal positions and no non-interlacing argument.**  With `T ⊆ S'` and `S'`
   independent, `geoIndependent_remaining_pair_owners` puts both visits of every not-yet-selected triangle crossing on ONE
   carrier of `T`, and `geoIndependent_selected_pair_owners_ne` separates the two visits of every selected one.  Under an
   incoherent orientation (e.g. `σ a₁ = b₁` and `σ a₂ = c₂`, "a first on both its edges"), the two `a`-visits of
   `Q' ∪ {a}` get joined through `b`/`c` by two applications of `geoOwner_successor` — contradiction; the remaining bad
   orientation of edge `g` is killed the same way on `Q' ∪ {a, b}`.  Six `have`s and `Eq.trans` chains.
2. **The central carrier is read off the permutation.**  `geoSmoothingSuccessor_visit_of_mem` gives `succ v = σ (twin v)`,
   so P1 yields the literal 3-cycle; `w3ca_three_cycle_marks` (induction on `(f ^ i) x` via
   `Equiv.Perm.SameCycle.exists_pow_eq'`) turns it into `owner m = Z ↔ m ∈ {a₂, b₁, c₁}`.  Distinctness of `A, B, C` is
   pushed down to `Q₁`/`Q₂` by `geoOwner_eq_of_subset` (refinement) where the daughters are already separated;
   `A/B/C ≠ Z` is `geoIndependent_selected_pair_owners_ne` at `S'`.  `central_no_piece`: a piece on `Z` has an
   unselected label whose visit would be a mark of `Z`, but `Z`'s marks are selected.  `central_rot`: `geoCornerCount Z = 3`
   by `List.perm_ext_iff_of_nodup` against `[inr zA, inr zB, inr zC]`, then `CV.rot_triangle`.

Not used: `esc_contact_owns` / `GT_empty_tri_subset` (that all six visits lie on `q₀'`) — the independence layer implies
what was needed; hence the fields are proved without the hypotheses on `q₀'`, exactly as the field types allow.

## Pitfalls (for the assembler)

1. **`DecidableEq (Crossing P)` instances (U_SPLIT_REPORT pitfall 1 again).**  The frozen `Q' ∪ T'` is elaborated with
   `RProof.instDecidableEqCrossing`; the library's `insert v.1 T` lemmas (`SM/GeoCarrierCount.lean`) with
   `Classical.propDecidable`.  Solution used: the abstract section `W3CA_Core` (lines 10691–11306) is wrapped in
   `attribute [local instance high] Classical.propDecidable`, its main theorem `w3ca_core` takes an ARBITRARY `S` with the
   instance-free hypothesis `hSeq : ∀ x, x ∈ S ↔ x ∈ Q ∨ x = a ∨ x = b ∨ x = c` and `subst`s
   `S = insert c (insert b (insert a Q))` (proved by `ext; simp only [Finset.mem_insert]; tauto`) inside; the section
   `W3CA_Config` (normal instances) then instantiates `S := Q ∪ triangleCrossings …` so the frozen `∪` is matched
   syntactically.  No `decide`/`omega` inside the classical region (pitfall 2 there).
2. `rw [if_pos h]` rewrites only the first `if` (the other three have different branches): use
   `simp only [h1, ↓reduceIte]` / `simp only [hn1, ↓reduceIte]` after `unfold w3ca_Ac w3ca_Bc w3ca_Cc w3ca_Zc`.
   `if_pos`/`if_neg` are deprecated in this toolchain (warnings only).
3. A `_` for the support inside a theorem STATEMENT (`w3ca_A hP _ hef heg hfg ≠ …`) cannot be inferred in `≠` clauses;
   the support must be written out.
4. `geomAt E t ht.1` and `(genericAt E t ht.1).crossingGeometry` are defeq: `CV.carrierR hn (genericAt E t ht.1) hS Z` with
   `Z : GeoComponent (geomAt E t ht.1) _` elaborates (as in `esc_interface`).
5. After `obtain ⟨x, i, hi⟩ := v` for `v : Visit P`, coerce `hv` / `hi` with an explicit `have … := hv` before feeding them to
   `P1.mem_triangleSupports` / `Finset.mem_insert` (the Sigma projections are only defeq).
6. `SEL_visitTwin_visitOn (hxu : u ∈ x.val) (hxv : v ∈ x.val) (huv : u ≠ v) : visitTwin (visitOn x v hxv) = visitOn x u hxu`
   — the twin is named by the FIRST membership argument.

## Times (UTC / ET)

23:19 / 7:19pm start (reading); 23:32 route fixed on the independence layer; 23:36 core (`w3ca_pattern`,
`w3ca_three_cycle_marks`) compiled first try; 23:40 `w3ca_core` + configuration section 0 errors; 23:44 first full
compile 0 errors + checks; 23:48 `central_rot` closed; 23:50 second full compile, axioms, checks; 23:52 first report; 23:56 extra `w3ca_marks_partition` compiled first try; 23:58 third full compile (0 errors, 35 s), axioms, checks; 00:00 this report.
