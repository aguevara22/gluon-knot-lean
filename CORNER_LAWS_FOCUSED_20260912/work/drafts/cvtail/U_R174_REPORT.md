# U-174 report — `RProof.generic_selected` (R:generic_selected, row 174), prefix `gsc_`

Prover, 2026-09-15. File: `work/drafts/cvtail/U_R174.lean` (= `Statements_FINAL.lean` + two `import` lines +
one inserted section; `diff Statements_FINAL.lean U_R174.lean | grep '^<'` prints nothing — no statement,
definition, name or docstring changed). Check: `cd work/lean && lake env lean ../drafts/cvtail/U_R174.lean`
→ exit 0, 0 errors, exactly the 10 `sorry` warnings of the FINAL (4 sibling-lane placeholders, the leaves
`carrier_slot_floor_of_C`, `cvt_singleton_split`, `cvt_pair_row_zero_of_singleton`, `extreme_transport`,
`extreme_selected`, and THIS unit's leaf `generic_selected`). `grep -c sorry`: 11 before, 11 after (the
11th hit is the header prose "Every `sorry` is"). Compile time ≈ 20–25 s on the pod as loaded today.

## 1. Result in one paragraph

The leaf `generic_selected` is **left** (`sorry`), as D-F11 anticipates for the three RA rows: its content
is a Reidemeister-II deletion plus record identifications on the grouped contact diagrams (G10 scale).
Following the prescribed pattern, the moves and identifications the RA argument needs are stated as explicit
interface Props (`gsc_fulltwist_triple`, `gsc_smoothing_split`, the data bundle `gsc_Ledger`, the event-level
`gsc_moves`), and the RA ledger of GSC §4–§5 is **PROVED** from them and from `CV.CarrierSlotFloor`:

* `gsc_ledger : gsc_moves → CV.CarrierSlotFloor → RowShape @GenericSelectedData` — the row in the shape
  `cv_R_of_rows` consumes;
* `gsc_generic_selected_of_moves : gsc_moves → CV.CarrierSlotFloor → <exact signature of generic_selected>`.

`#print axioms gsc_ledger` = `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness`
(the three literature axioms enter through `CV.fulltwist_skein` and `CV.two_component_row_rows`); no `sorryAx`.
Part of the interface is already **realised** from the accepted library: the wall part of the ledger
(`gsc_WallData`: the carrier correspondence `τ` of the centre row across the wall with selector and rotation
transport — `gsc_wallData_of_endpoint`, axioms standard only) and the canonical sign (`gsc_sigma_of_endpoint`).
When `gsc_moves` is realised, the leaf is
`gsc_generic_selected_of_moves <realisation> (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) hn E e f g h3 h4e h4f h4g hE`.

## 2. Interface Props stated (never mapped)

| name | kind | content (GSC section) |
|---|---|---|
| `gsc_fulltwist_triple D_L D_H D₀ q : Prop` | the G10 move | §3: `q` (the retained crossing `a` of `D_H`) is positive, `D₀` is an oriented smoothing of `D_H` at `q` (T1), and `D_H.switch q` is carried by RII moves to a diagram `D_L'` with `homfly D_L' = homfly D_L` (T2 read through ax:gausscode, see §5 below) |
| `gsc_smoothing_split D₀ i j QA QB ℓ : Prop` | diagram identification | §3: `D₀` has two components `i ≠ j`, `homfly (D₀.knotRestrict i) = QA`, `homfly (D₀.knotRestrict j) = QB` (the pair-row grouped polynomials `Q_A, Q_B`), `CV.IsLinkingNumber D₀ i j ℓ` |
| `gsc_WallData hn hG hG' hs Q m hSm hSm'` | data (REALISED) | §1 (2) `E-b : C ∣ AB` and §2 (6)–(7): `τ : carriers(Q ∪ {m}) ≃ carriers(transport (Q ∪ {m}))`, `weight_wall`, `carrierR_wall` |
| `gsc_Ledger hn hG hG' hs Q m x w hSm hSxw hSm' W` | data bundle over the realised `W` | `σ = ±1` (1); the carriers `qC, qAB` of `P-b`, `qC', qA, qB` of `P-ac` (2); `omega_wall` (spectators and `C` keep their read across the wall), `writhe_wall` ((9) `w_H = w_L + 2`); `ρ : carriers(P-b) ≃ {carriers(P-ac) ∖ B}` with `ρ_AB`, `ρ_C`, `spectator_weight/omega`; `omega_C`, `weight_C` ((5) `wt(C_ac) = −σ wt(C_b)`), `weight_AB` ((5) `wt(A)wt(B) = σ wt(AB)`), `carrierR_add` ((8), under `wt(AB) ≠ 0`); `D₀`, `qx`, `fulltwist : gsc_fulltwist_triple (carrierDiagram qAB) (carrierDiagram (τ qAB)) D₀ qx`; `i j ℓ`, `smoothing : gsc_smoothing_split …`; `writhe_count` ((10) `w_L = w_A + w_B + 2ℓ − 1`) |
| `gsc_moves : Prop` | event-level interface | for every `GT_Endpoint` configuration (the accepted row-173 configuration: `x, w` the selected pair, `m` the centre, `ℓ₁` shared by `x, m`, `ℓ₂` by `x, w`, `ℓ₃` by `w, m`, `Q` outside at full availability, R-LOC (2)–(4), lem:guardconst, masks) in the canonical sign branch (`crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₁ ℓ₃`, with `GT_Endpoint.sgn` giving the third equality), `Nonempty (gsc_Ledger … (gsc_wallData_of_endpoint …))` |

Reading of the fixed labels: canonical branch `x = a = x_ef`, `w = c = x_fg`, `m = b = x_eg`, `(ℓ₁,ℓ₂,ℓ₃) = (e,f,g)`;
branch `ab` (centre `c`): `x = a, w = b, m = c`, `(f,e,g)`; branch `bc` (centre `a`): `x = b, w = c, m = a`, `(e,g,f)` —
the same assignments as the accepted `GT_row_*_of_*` of row 173, so the two-edge side of every branch is a
`GT_Endpoint` configuration with the sign condition derived from `SelectedAB/BC` + nonalternating
(`GT_signs_of_selectedAB/BC`, `crossingSign_swap`).

## 3. Helpers added (all PROVED; `gsc_` prefix; in `namespace RProof`, sections `GSC`, `GSCEvent`)

Algebra (GSC §4 (12)–(13)): `gsc_coeff_mul_floor`, `gsc_coeff_mul_eq_zero_of_lt` (floors multiply / vanish below the
sum), `gsc_coeff_shift` (the factor `(a − a⁻¹) a^{−2ℓ}`), `gsc_omega_jump_alg` (the whole extraction on `R`, `zRow`).
def:X1 ↔ lem:fulltwist bindings: `gsc_carrierDiagram_componentCount`, `gsc_carrierDiagram_writhe`,
`gsc_carrierDiagram_absRot` (`rfl`), `gsc_d_carrierDiagram` (`d(D(W)) = slot`), `gsc_Omega_carrierDiagram` (`Ω(D(W)) = Ω₁`) —
"the two bindings agree wherever both apply".
Floor: `gsc_alt_of_uniform` (a def:wind-uniform carrier satisfies `UniformOrOneDissentCV` of its corner polygon, via
`turn_det`, `principalAngle_pos_iff/neg_iff`, `principalTurn_reversal`), `gsc_floor_of_weight_ne_zero`
(`CarrierSlotFloor.coeff_zero` at a carrier of nonzero weight).
Realised interface parts: `gsc_wall_of_endpoint : GT_Endpoint … → GT_Wall … (Q ∪ {m})`, `gsc_wallData_of_endpoint`
(`τ := GT_carrierEquiv`, `GT_weight_eq`, `GT_carrierR_eq`), `gsc_sigma_of_generic`, `gsc_sigma_of_endpoint`.
Ledger: `gsc_rowTerm_eq_prod`, `gsc_prod_split`, `gsc_omega_jump` ((13): `Ω_H − Ω_L = −ω_A ω_B` under a nonzero
selector), `gsc_couple_of_ledger` (GSC §5 on the abstract configuration, the zero-selector and mixed cases included).
Event level: `gsc_Ind_centre`, `gsc_Ind_pair`, `gsc_Ind_centre'` (presence of the three rows), `gsc_couple_event`,
`gsc_couple_canonical`, `gsc_couple_relabelled` (the two bundle fields), `gsc_genericSelectedData`, `gsc_ledger`,
`gsc_generic_selected_of_moves`.

## 4. What the realisation still needs (the content of `gsc_moves`), field by field, with estimates

Realised: `τ`, `weight_wall`, `carrierR_wall` (`gsc_WallData`), `σ`/`hσ`. Remaining, on a `GT_Endpoint` configuration
`D` with `crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₁ ℓ₃`:

1. **The carrier structure (2)** — `qC, qAB` (the two visits of `x` on `P-b` lie on different carriers: `qAB` owns the
   `ℓ₂`-visits of `x, w`, `qC` the `ℓ₁`-visit of `x` and the `ℓ₃`-visit of `w`), `qC', qA, qB` on `P-ac` (`qA` owns the
   `ℓ₁`-visit of `m`, `qB` its `ℓ₃`-visit), the distinctness facts, and the bijection `ρ` with `ρ_AB`, `ρ_C`. Tools:
   `GT_owner_arc`, `AV_nextCorner`/`GT_carrierMap` machinery of RProof/X1Rows3, `CV.owner_eq_of_mem_U`, the adjacency
   fields `adj1..3` of `GT_Endpoint`. The bijection compares carriers of two supports `Q ∪ {m}` vs `Q ∪ {x, w}` on ONE
   polygon: this is the geo-layer insert/remove step (the U-SPLIT layer `CarrierInheritedInsert`/`CarrierSmoothing`
   named in PLAN_FINAL §4), applied twice. ~1500–2500 lines.
2. **Pieces and reads across the wall** — `omega_wall` (every carrier but `AB` keeps `groupedPoly`, `groupedWrithe`:
   for a spectator by `GT_geoCarrierCrossings_eq_of_good`-type retention + `EXT_homfly_wall` (record isomorphism); for `C`
   the same after showing `C` owns only good marks besides the `m`-corner), `writhe_wall`
   (`retained(AB') = transport(retained(AB)) ∪ {x', w'}`: `GT_owner_transport` on good marks plus the ownership of the
   four `x', w'` visits by `AB'` — the arc `[m(ℓ₁) → m(ℓ₃)]` on `P'`, `GT_owner_arc`). ~800–1200 lines.
3. **The selector ledger (4)–(5) and rotation (7)–(8)** — `weight_C`, `weight_AB`, `omega_C`, `carrierR_add`: the turn
   signs at the three smoothing corners (`σ` at the `m`-corner of `C`, `−σ` at the `x`-/`w`-corners of `A`, `B`,
   `σ, σ` on `C_ac`) from `turn_eq_sign_of_traced`/(G5) and the corner-list structure; `carrierR_add` from
   CV:lem:turnlift (ii) (`CV.turnlift_full.polygon_two_pi_rot`: `2π rot = Σ principal turns`, the two new corners'
   turns cancelling against the removed one) and lem:uniformrot (i) (`uniformrot.pos_ge_one/neg_le_neg_one`) for the
   common sign of the three rotations. ~600–1000 lines.
4. **The G10 move `fulltwist`** — the RII deletion of the switched empty pair on the `E`-side positive lift
   `carrierDiagram (τ qAB)`: an actual `SM.Link.RIIData U (D_H.switch qx) D_L'` at a disc `U` containing the bigon bounded by
   the `ℓ₂`-segment `[w(ℓ₂), x(ℓ₂)]` (adjacent visits, R-LOC (2)) and the corner path `[w(ℓ₃) → m-corner → x(ℓ₁)]`, with
   `LocalFrame`, `MoveMatch`, `ArcCover`, `Separates`, `OverOn` — exactly the shape of G11's Units B–E (11k lines for one
   RIII site); plus (T1) the oriented smoothing `D₀` at `qx` (`OrientedSmoothingData`), and the record identification
   `homfly D_L' = homfly D_L` (`GT_homfly_wall_gen`-style record isomorphism between `D_L'` and the `P-b` lift, then
   `CV.gausscode_polynomial`). Dominant cost: **~8000–12000 lines** on the G11 precedent; nothing of it is in the library
   (no `RIIData` is constructed anywhere in work/lean).
5. **The smoothing identification `smoothing`** — `D₀.componentCount = 2`, the two knot restrictions record-isomorphic to
   the `P-ac` lifts of `A`, `B` (masks (9a): a mask-zero survivor is a residual crossing of the corresponding `P-ac` carrier,
   a mask-`xw` survivor is a mixed crossing), the linking number. Record-level, as lem:triplebridge (ii)'s argument
   "derived from the RIII words and masks". ~1500–2500 lines.
6. **The writhe count (10)** `writhe_count` — retained crossings of `AB` = self-crossings of `A` ∪ self-crossings of `B`
   ∪ mixed crossings minus `w`; all positive so `mixedSignSum = 2ℓ`. ~400–600 lines once 5 is in place.

Total remaining ≈ 13–19k lines; the unit's PLAN estimate (3–5k) covered the ledger-first deliverable, which is done.

## 5. Fidelity decisions and readings (for AUTHOR_NOTES)

* **(T2) read through ax:gausscode.** lem:fulltwist (T2) says the switched diagram is "carried to `D_L` by oriented
  Reidemeister-II moves". In this application `D_L` is the grouped diagram of the `P-b` carrier and `D_H` that of the
  `E-b` carrier — two positive lifts of polygons on OPPOSITE sides of the wall. An RII chain (`Relation.ReflTransGen RII`)
  cannot move a diagram between two different polygons (no planar isotopy in `RII`), so the literal
  `ReflTransGen RII (D_H.switch q) D_L` is FALSE as a target and the RA's `D_L` must be read as a diagram with the RECORD
  of the `P-b` lift ("By lem:carrierword, def:record, ax:gausscode, and cor:groupedknot", GSC §3). `gsc_fulltwist_triple`
  therefore asks for `∃ D_L', ReflTransGen RII (D_H.switch q) D_L' ∧ homfly D_L' = homfly D_L`, and the ledger uses
  lem:fulltwist's FIRST display (`CV.fulltwist_skein` at `D_L'`) and re-derives the second display's coefficient step
  (d6:2039–2044) on def:X1's `slot`/`Ω₁` — the accepted `fulltwist_coefficient` is not applied because its `D_L` is literal;
  the sanity lemmas `gsc_d_carrierDiagram`/`gsc_Omega_carrierDiagram` show the two bindings agree.
* **Zero selector and mixed cases.** The ledger never divides: (13) is used only under `wt(AB) ≠ 0` (`gsc_omega_jump`),
  and `gsc_couple_of_ledger` carries `wt(AB)` as a factor (`hkey`), with (5) stated as equalities "including the mixed
  cases" exactly as the RA text prescribes.
* **`R:exterior` (row 168) is not consumed.** The RA's spectator factor `V` is handled by the explicit bijection `ρ`
  (all carriers of `P-b` other than `AB` against all carriers of `P-ac` other than `A, B`) rather than by
  `exteriorFactor`; the triangle-touching carrier `C` is part of that bijection (`ρ_C`, `omega_C`, `weight_C`). This
  replaces one accepted input by an interface field; the realiser may prove `ρ`'s spectator clauses from
  `ExteriorData` if convenient.
* **Sign condition.** `gsc_moves` takes `crossingSign ℓ₁ ℓ₂ = crossingSign ℓ₁ ℓ₃` beside `GT_Endpoint.sgn`
  (`crossingSign ℓ₂ ℓ₃ = crossingSign ℓ₁ ℓ₃`): together "sgn det(u1,u2) = sgn det(u1,u3) = sgn det(u2,u3) = σ" (GSC (1)).
  In the relabelled branches this is derived from `SelectedAB/BC` and nonalternation exactly as row 173 does.
* **Floors.** Only `CV.CarrierSlotFloor` (via `.coeff_zero`) is consumed, through `gsc_floor_of_weight_ne_zero`; the
  alternative is discharged by `gsc_alt_of_uniform` (all-left → all positive turns; all-right → the reversal is all
  positive, `principalTurn_reversal`). Piece-free carriers need no special case (`groupedPoly = 1`, floor `0`).

## 6. Mathlib / library pitfalls met

* The FINAL does not import `CV.FullTwist` / `CV.HomflyRows`; both were added to the header (`import CV.FullTwist`,
  `import CV.HomflyRows`) — the only change outside the inserted section. The assembler must keep them.
* `AddMonoidAlgebra` is now a structure with `.coeff`; the product coefficient lemma is `AddMonoidAlgebra.coeff_mul`,
  the monomial ones `coeff_single_mul_apply` (additive form: `(single g r * x).coeff h = r * x.coeff (-g + h)`);
  `coeff_sub` gives a `Finsupp` difference, needing `Finsupp.sub_apply`. `if_pos/if_neg` are deprecated for
  `ite_eq_left/ite_eq_right`.
* `Finset.prod_subtype` with an equiv onto a subtype produced a `whnf` timeout (two different `Fintype (Subtype p)`
  instances to unify); use `Finset.prod_bij'` with the explicit inverse instead. A `congr n` one level short makes the
  next `Finset.prod_congr` unfold `Int.mul`/`Finset.prod`/`set`-bound lets → timeout; state the spectator product
  equality as a separate `have` and `rw`.
* `SignType`: `hk i : turn … = SignType.pos` does not match `sign_eq_one_iff` (`= 1`); restate the hypothesis with the
  literal `1`/`-1` through `turn_det`.
* Implicit `hG : CV.Generic P` cannot be inferred from a `GT_Endpoint hG.crossingGeometry …` argument
  (`crossingGeometry` is a Prop); pass it explicitly (`gsc_wall_of_endpoint hG hG' D …`).
* `principalAngle_pos_iff` is `CV.principalAngle_pos_iff` (CV/Rotation.lean) while `principalAngle_neg_iff` and
  `principalTurn_reversal` are in `SM`.

## 7. For the assembler / executor

* Port target: the `gsc_` section (lines 734–1474 of U_R174.lean) is library material for `RProof/` (suggested
  `RProof/GenericSelected.lean`, `import RProof.GenericTransport`, `import CV.FullTwist`, `import CV.HomflyRows`) — but it
  depends on `CV.CarrierSlotFloor` (U-SLOT / row 155 §1.3 of this lane), so it ports together with or after
  `CV/CarrierFloor.lean`. Nothing here may be mapped as a row: the row is closed only by a realisation of `gsc_moves`.
* The interface Props (`gsc_fulltwist_triple`, `gsc_smoothing_split`, `gsc_Ledger`, `gsc_moves`) must not be asserted;
  D-F11.
* Closing the row: `generic_selected := gsc_generic_selected_of_moves <proof of gsc_moves>
  (carrier_slot_floor_of_C SM.cf_thm_carrierfloor.clauseC) hn E e f g h3 h4e h4f h4g hE` (or the `RowShape` form via
  `gsc_ledger` for `cv_R_of_rows`). Its axiom footprint will be that of `gsc_ledger` plus row 99 (C)'s
  (`SM.lit_homfly_descent`, FR-R-178-2).
* The realisation order that minimises rework: items 4.1 → 4.3 → 4.2 (all on the accepted geo carrier layer, independent
  of the floor), then 4.5–4.6, then the G10 site 4.4 (the only piece with no library precedent besides G11).
