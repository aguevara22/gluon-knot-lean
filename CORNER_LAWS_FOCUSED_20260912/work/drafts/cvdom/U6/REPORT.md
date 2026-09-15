# CV-DOM unit U6 — REPORT (2026-09-14 07:13 UTC / 3:13am ET)

Prover: Claude Code subagent (claude-fable-5-1) of the pod executor. Spec: work/drafts/cvdom/DECISION_FINAL.md §5
row **U6** ("agreement on SM-generic P … `Bridge.B4Data.pointwise` … `sides` via `SM.prop_C_chamber` +
`CV.chamberinv_ii`; `theorem Bridge.B4 : B4Data`"), §3 ruling R7 (shape of `Bridge.B4`), §4 review note for
Bridge:B4, §7 risks 2 and 6; reference/BRIDGE/BRIDGE.md §2 B4 (lines 637–1441; displays (13)–(18)).
Nothing under work/lean was written. Paths are relative to the package root
/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912.

## 0. Deliverables and status

| file | intended home | lines | declarations | check | placeholders | axioms |
|---|---|---:|---:|---|---|---|
| `work/drafts/cvdom/U6/GeoCarrierAgreement.lean` | `work/lean/SM/GeoCarrierAgreement.lean` (library; imports `SM.CS3`, `SM.GeoCarriersLemma`, `SM.GeoPositiveLift`, `SM.CBBlocks`, `CV.X1`) | 291 | 22 | `cd work/lean && lake env lean ../drafts/cvdom/U6/GeoCarrierAgreement.lean` → **exit 0, no output** (no warnings) | **none** (`grep -c` of the placeholder keyword = 0) | standard (`propext, Classical.choice, Quot.sound`) on the 14 declarations that do not mention `homfly`; standard + `SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` on the 6 `_of_cb` declarations (through `homfly`, `SM.P`/`P_eq_homfly` and the cb:products bundle — exactly the axioms of def:C, cb:blocks and row 102) |
| `work/drafts/cvdom/U6/BridgeB4.lean` | `work/lean/Bridge/B4.lean` (row module; imports `Bridge.B3`, `SM.GeoCarrierAgreement`, `SM.CBProducts`, `SM.GermSides`, `CV.ChamberInvRow`) | 132 | 7 | overlay check (§6) → **exit 0, no output** | **none** | `Bridge.B4`: `propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` (the policy's standard + literature axioms, work/lean/axiom-policy.json; no `SM.hyp_R`, no new axiom) |

**`Bridge.B4 : B4Data` is PROVED and closed** (not left out): `SM.cb_products` was ported to
work/lean/SM/CBProducts.lean at 06:58Z (AUTHOR_NOTES "cb:products (102) proved and ported"), so the final
`theorem Bridge.B4 : B4Data := B4_of_cb fun _ _ hn _ hP _ hS => SM.cb_products hn hP hS` is in the file, and
`#print axioms Bridge.B4` shows only policy axioms. `B4_of_cb` keeps cb:products isolated as the one explicit
hypothesis (DECISION_FINAL §7 risk 6), as the brief asked.

Both files: 0 errors, 0 warnings, no `#print axioms` lines (those were run on /tmp copies, §6), no accepted
declaration modified, no `geo*` name of FlatCarriersDefs/FlatCarriers re-declared (ruling R3), every new
declaration name grepped against every declaration head under work/lean/{SM,CV,Bridge,RProof,Supplemental}:
**0 collisions**.

## 1. Route (BRIDGE.md B4 parts 1–5 → Lean)

Setting: `hn : 3 ≤ n`, `hP : SM.Generic P`; the CV-generic proof is `hG` (in the row: `CV.generic_of_sm hn hP`,
B1 (1)); `hc := hG.crossingGeometry` and `generic_crossingGeometry hn hP` are two proofs of the `Prop`
`CrossingGeometry P`, so every geo object at one is definitionally the object at the other (proof
irrelevance — the pattern of U4 §6 and CBBlocks' `SM.CB.cg`); `e := geoComponentEquivGeneric hn hP S :
GeoComponent hc S ≃ Component hn hP S` (accepted, `rfl` on owners).

| BRIDGE.md | statement | Lean (file, declaration) | proof ingredients |
|---|---|---|---|
| part 1, common supports | `Ind(G_P)` is the same finite set | `CV.Ind_eq_generic` (accepted, CV/Events.lean:204); `CV.isDecomposition_of_mem_Ind`, `CV.mem_Ind_of_isDecomposition` (A §2) | rewrite |
| part 2, common carriers | carrier `L` of CV = carrier `e L` of SM | the accepted `geoComponentEquivGeneric`; `CV.blocksOwnedBy_eq_piecesOn` (A §2): cb:blocks' `blocksOwnedBy (e q) = piecesOn hc S q` | `Equiv.symm_apply_apply` |
| part 3, (13) first equality | `P_{S,L} = ∏_{H on L} P_H = H⁺_L` | `CV.groupedPoly_eq_cornerHomfly_of_cb` (A §2), from `hcb : CbProductsData hn hP hS'` | `hcb.product (e q)`: `P_A = ∏_{H owned by A} P_H`; `P_eq_homfly` (lp:core); per block `CV.pieceHomfly_eq_blockPoly_of_cb`: `hcb.polynomial_independent H (pieceDiagram H) _` at the actual positive carrier diagram `pieceDiagram H` — `CV.isBlockCarrierDiagram_pieceDiagram` (A §2): `pieceDiagram H = positiveLift hn hP (S ∪ K_H) (e q_H) hT` by the accepted `geoPositiveLift_eq_generic` (U4 §6), self-crossings `= pieceLabels H` by `pieceCarrier_geoCarrierCrossings` (U7c) + `geoCarrierCrossings_eq_generic` (U4 §6) |
| part 3, (13) second equality | `w_{S,L} = Σ_{H on L} |H| = m_L` | `CV.groupedWrithe_eq_generic` (A §2) | U7c `groupedWrithe_eq_card_geoCarrierCrossings`; `SM.GeoCarrier.card_geoCarrierCrossings_eq_generic` (A §1) |
| part 4, (14) | `R^CV(L) = |r_L^SM|` | `CV.carrierR_eq_generic` (A §2): `(carrierR : ℤ) = |carrierRotationInt (e q)|` | `CV.carrierR_cast`, `CV.rot_eq_rotationNumber` (lem:turnlift (ii)), `SM.carrierRotationInt_cast` (lem:rot), `SM.carrierRotation_eq_geo` (CS3 §B, the recast) — the integers agree because their real casts do (`exact_mod_cast`) |
| part 4, (15) | slot `1 − w − R = d_L` | `CV.slot_eq_generic` (A §2) | the two above |
| part 4, (16) | `Ω₁(S,L) = c(L)` | `CV.Omega1_eq_cornerCoefficient_of_cb` (A §2) | `cornerCoefficient_eq_coeffAt`, both `coeffAt slot 0 poly` |
| part 4, selectors | `wt`, `wind` agree | `SM.GeoCarrier.geoCarrierSelector_eq_carrierWeight` (A §1; from CS3 §B), `CV.wind_eq_generic` (A §2; from U3 `geoWind_eq_generic`; `CV.wind` and `geoWind` are both `∏_q geoCarrierSelector`) | — |
| part 4, (17) | `C^SM(P) = X₁^CV(P)` | `CV.X1_eq_cornerStateSum_of_cb` (A §3), `CV.X1_generic_of_sm_eq_cornerStateSum_of_cb` | `SM.C_X1.selector_form` (accepted lem:C-X1: `C = Σ_{S ∈ Ind} wind(S) ∏ c(Q)` — no uniformity filter is compared, non-uniform supports have `wind = 0` on both sides), `SM.sum_attach_congr` (A §0: attached sums along `Ind hc = independentSupports`), per summand `CV.X1_summand_eq_of_cb` = `wind_eq_generic` + `Fintype.prod_equiv e` + (16) |
| part 5, (18) | `C^SM(P_±^SM) = X₁^CV(P_±^CV)` | `Bridge.B4_sides_of_pointwise` (B) | exactly BRIDGE.md 1429–1441: `Bridge.cornerStateSum_sideTuple_eq_base` (SM chamber constancy `SM.prop_C_chamber.constant` along the connected punctured side, `WallGerm.sidePolygon_mem_side`), then (17) at the base parameter, then `CV.chamberinv_ii` on the containing CV side chamber (`Bridge.sideChamber_eventOfTriple`: `(eventOfTriple hn g h).sideChamber b = CV.chamber (g.sideTuple b g.sideBase).val`, `rfl`) |

## 2. Declarations

### A. `GeoCarrierAgreement.lean` (namespaces `SM`, `SM.GeoCarrier`, `CV`)

§0 helpers (hypothesis-free): `SM.leftTurns_recastTuple` (companion of `rotationNumber_recastTuple`),
`SM.sum_attach_congr` (transport of `∑ x ∈ s.attach, f x` along `s = t`).

§1 SM side, at `generic_crossingGeometry hn hP`, `q : GeoComponent hc S`:
`geoCarrierRotation_eq_generic q : geoCarrierRotation hc S q = carrierRotation hn hP S (e q)`;
`geoCarrierRotationInt_eq_generic`; `geoCarrierLeftTurns_eq_generic` (via `geoCornerPolygon_eq_generic` + recast);
`geoCarrierSelector_eq_carrierWeight q : geoCarrierSelector hc S q = carrierWeight hn hP S (e q)`;
`card_geoCarrierCrossings_eq_generic q : (geoCarrierCrossings hc S q).card = carrierCrossingCount hn hP S (e q)`.
(The §5 list's `geoIndependent_iff_mem_independentSupports`, `geoCornerCount_eq_generic`,
`geoCornerPolygon_eq_generic`, `geoCarrierCrossings_eq_generic`, `geoWind_eq_generic`,
`geoPositiveLift_eq_generic` already exist — U3 §6, CS3 §B, U4 §6 — and are consumed, not redone, per
AUTHOR_NOTES 2026-09-14 ~03:58Z.)

§2 CV side, `hG : CV.Generic P`, `hS : S ∈ Ind hG.crossingGeometry`, `hS' : IsDecomposition hn hP S`
(both taken explicitly; the second is `isDecomposition_of_mem_Ind hn hP _ hS`):
`CV.isDecomposition_of_mem_Ind`, `CV.mem_Ind_of_isDecomposition`;
`CV.wind_eq_generic hG hS' : wind hG.crossingGeometry S = SM.wind hn hP S`;
`CV.groupedWrithe_eq_generic hG hS q : groupedWrithe hG q = (carrierCrossingCount hn hP S (e q) : ℤ)`;
`CV.carrierR_eq_generic hG hS hS' q : (carrierR hn hG hS q : ℤ) = |carrierRotationInt hn hP S (e q)|`;
`CV.slot_eq_generic hG hS hS' q : slot hn hG hS q = cornerSlot hn hP S (e q)`;
`CV.isBlockCarrierDiagram_pieceDiagram hG hS hS' H : SM.CB.IsBlockCarrierDiagram hn hP hS' H (pieceDiagram hn (hG.diagrammatic hn) hS H)`;
`CV.blocksOwnedBy_eq_piecesOn hG q : SM.CB.blocksOwnedBy hn hP S (e q) = piecesOn hG.crossingGeometry S q`;
`CV.pieceHomfly_eq_blockPoly_of_cb hG hS hS' (hcb : CbProductsData hn hP hS') H : pieceHomfly … H = SM.CB.blockPoly hn hP hS' H`;
`CV.groupedPoly_eq_cornerHomfly_of_cb hG hS hS' hcb q : groupedPoly hn hG hS q = cornerHomfly hn hP S (e q) hS'`;
`CV.Omega1_eq_cornerCoefficient_of_cb hG hS hS' hcb q : Omega1 hn hG hS q = cornerCoefficient hn hP S (e q) hS'`;
`CV.X1_summand_eq_of_cb hG hS hS' hcb : wind … S * ∏ q, Omega1 hn hG hS q = SM.wind hn hP S * cornerProduct hn hP S hS'`.

§3 state sums: `CV.X1_eq_cornerStateSum_of_cb hn hP hG (hcb : ∀ S hS, CbProductsData hn hP hS) : X1 hn P hG = cornerStateSum hn hP`;
`CV.X1_generic_of_sm_eq_cornerStateSum_of_cb hn hP hcb : X1 hn P (generic_of_sm hn hP) = cornerStateSum hn hP`.

### B. `BridgeB4.lean` (namespace `Bridge`)

```
structure B4Data : Prop where
  pointwise : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : SM.Generic P),
    CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP
  sides : ∀ (n : ℕ) [NeZero n] (hn : 3 ≤ n) (g : WallGerm n) (e f k : ZMod n) (h : g.TripleAt e f k)
    (t : g.SideParameter) (b : Bool) (Q : LabelledTuple n),
    Q ∈ (eventOfTriple hn g h).sideChamber b → ∀ hQ : CV.Generic Q,
    SM.cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q hQ
theorem B4_pointwise_of_cb (hcb : ∀ n [NeZero n] hn P hP S hS, CbProductsData hn hP hS) (hn) (P) (hP) : CV.X1 hn P (CV.generic_of_sm hn hP) = SM.cornerStateSum hn hP
theorem cornerStateSum_sideTuple_eq_base (hn) (g) (b) (t) : cornerStateSum hn (g.sideTuple b t).2 = cornerStateSum hn (g.sideTuple b g.sideBase).2   -- SM.prop_C_chamber
theorem sideChamber_eventOfTriple (hn) (g) (h) (b) : (eventOfTriple hn g h).sideChamber b = CV.chamber (g.sideTuple b g.sideBase).val   -- rfl
theorem B4_sides_of_pointwise (hpw : <the pointwise statement>) (hn) (g) (h) (b) (t) (Q) (hQ) (hQG) : cornerStateSum hn (g.sideTuple b t).2 = CV.X1 hn Q hQG
theorem B4_of_cb (hcb : ∀ n [NeZero n] hn P hP S hS, CbProductsData hn hP hS) : B4Data
theorem B4 : B4Data := B4_of_cb fun _ _ hn _ hP _ hS => SM.cb_products hn hP hS
```

`pointwise` is character for character the hypothesis `hB4` of the R lane's consistency check
`smR_shape_of_hyp_R` (work/drafts/rlane2/Statements_FINAL.lean:1157–1160), i.e. the shape `Bridge.sm_R`
consumes. `sides` follows ruling R7's binder list (`hn`, `g`, `e f k`, `h`, `t`, `b`) with "for every `Q` in
the CV side chamber" rendered as `Q ∈ (eventOfTriple hn g h).sideChamber b → ∀ hQ : CV.Generic Q, …`
(the genericity proof is quantified separately rather than extracted from `sideChamber_subset_generic`, so
the field reads as printed; proof irrelevance makes the two forms interchangeable).

## 3. What remains for Bridge:B4

Nothing mathematical: `Bridge.B4` is proved. Remaining are executor steps —
1. port `GeoCarrierAgreement.lean` → work/lean/SM/GeoCarrierAgreement.lean and `BridgeB4.lean` → work/lean/Bridge/B4.lean
   (headers only; then the plain `lake env lean` check applies to both), `lake build` through the checker,
   map `Bridge:B4` → `Bridge.B4` (lean-declarations.json has the row `pending` with empty module);
2. review with the §4 note (§4 below); the row depends on the accepted rows def:C, lem:C-X1, prop:C-chamber,
   def:flat-carriers/cor:flat-carriers, CV:def:X1, CV:prop:chamberinv, Bridge:B1 and on **cb:products (row
   102), ported but still under review** (AUTHOR_NOTES 06:58Z / 07:00Z) — if row 102 is sent back, `B4_of_cb`
   stands and only the one-line `B4` waits;
3. `Bridge.sm_R` (Bridge:theorem) consumes `Bridge.B4.pointwise` with `RProof.cv_R` as in `smR_shape_of_hyp_R`.

Not needed for B4 but noted: the agreement library imports the accepted **row module** `SM.CS3` for
`geoCornerPolygon_eq_generic`, `carrierRotation_eq_geo`, `carrierWeight_eq_geoCarrierSelector` (allowed for
U6 by AUTHOR_NOTES ~03:58Z; alternatively the assembler copies those three short proofs into the library —
they are 6, 3 and 3 lines — and drops the import; nothing else of CS3 is used).

## 4. Readings recorded for the reviewer (Bridge:B4 review note, DECISION_FINAL §4, filled in)

"Field `pointwise` is (17) on SM-generic labelled representatives, as printed; field `sides` is (18). `CV.X1`
at an SM-generic `P` is evaluated through `CV.generic_of_sm hn hP` (B1 (1)); the identification with
`cornerStateSum` goes through the agreement lemmas of SM/GeoCarrierAgreement.lean, lem:C-X1 (`SM.C_X1`) and
cb:products (`SM.cb_products`)."

1. **(17) as printed** (BRIDGE.md:1360–1366, "for every `P ∈ 𝓤_n^SM`"): `pointwise` quantifies every `n`,
   `hn : 3 ≤ n`, labelled `P`, `hP : SM.Generic P`. The `hn` binder is the one def:C and CV:def:X1 both carry
   (reading (iii), DECISION_FINAL §2). `X₁` is read at the CV-generic proof `CV.generic_of_sm hn hP` — the
   inclusion `𝓤_n^SM ⊆ 𝓤_n^CV` of B1 (1) — as BRIDGE.md part 1 prescribes; the value does not depend on which
   `CV.Generic P` proof is used (`CV.X1_eq_cornerStateSum_of_cb` is stated for an arbitrary `hG`).
2. **(18) as printed** (BRIDGE.md:1429–1441): "equalities of values on corresponding sides". The SM side value
   `C(P_±^SM)` is rendered as `cornerStateSum hn (g.sideTuple b t).2` at an arbitrary side parameter `t`, the
   CV side value `X₁(P_±^CV)` as `X1 hn Q hQ` at an arbitrary `Q` of the CV side chamber
   `(eventOfTriple hn g h).sideChamber b` (def:event's "chambers containing `P((0,ε))`/`P((−ε,0))`", the CV
   event of B1). Two instances of the field at `t, t'` with one `Q` give the SM side value's independence of
   `t`; two instances at `Q, Q'` with one `t` give the CV side value's independence of `Q`. The proof is the
   printed one, in the printed order: SM chamber constancy (`SM.prop_C_chamber`, prop:C-chamber, on the
   quotient chamber `g.side b` containing the connected punctured image, GermSides), then (17), then CV
   chamber constancy (`CV.chamberinv_ii`, prop:chamberinv (ii), accepted 07:00Z). "They do not assert equality
   of a quotient SM chamber with a labelled CV chamber, or equality of their underlying generic loci" — the
   Lean statement mentions only values.
3. **Part 2, carriers** (BRIDGE.md:810–948): CV's carrier `L` of `S` is `q : GeoComponent hc S`
   (def:flat-carriers' local objects read through `hG.crossingGeometry`), SM's is `e q : Component hn hP S`
   (def:smoothing), identified by the accepted `geoComponentEquivGeneric` (same marks, same `ρ_S` cycles,
   `geoSmoothingSuccessor_eq_generic`). The ownership of the two visits of a selected crossing is SM
   conv:selected-visits on both sides (the same `selectedMarkPerm`), the disambiguation CV leaves implicit.
4. **Part 3, products** (BRIDGE.md:949–1190, (13) first equality): `P_{S,L} = ∏_{H carried by L} P_H` with
   CV's `P_H = homfly (pieceDiagram H)` (rows 142/143) equals `H⁺_L = homfly (positiveLift (e q))` through
   cb:products' `P_A = ∏_{H owned by A} P_H` (row 102, `CbProductsData.product`) and `P_H = blockPoly H`
   (`polynomial_independent`, applied to `pieceDiagram H`, which is an actual positive carrier diagram of `H` in
   the sense of cb:products' `IsBlockCarrierDiagram` — reading R-4 of SM/CBBlocks.lean; the witness refinement
   is `S ∪ K_H` and the witness carrier `e q_H`, by the accepted `geoPositiveLift_eq_generic`). "The CV grouping
   by carriers is the SM grouping by owners": `blocksOwnedBy (e q) = piecesOn hc S q` literally
   (`blocksOwnedBy_eq_piecesOn`). This is the *separate factorization-based identification* BRIDGE.md
   requires (line 1368: "not a reinterpretation of the restricted selector lemma").
5. **Part 4, rotations** (BRIDGE.md:1191–1340, (14)): CV's `R(L) = |rot(L)|` uses CV:def:rot's integer `rot`
   (ray formula), SM's `r_L` is the real `rotationNumber` of `ccpCornerPolygon`; they agree by CV:lem:turnlift
   (ii) (`rot_eq_rotationNumber`, "`2π rot(L) = Σ τ_i`, exactly SM's definition") on the recast corner polygon
   (`carrierRotation_eq_geo`), and SM's `d_L` uses `carrierRotationInt = round r_L` with `r_L` an integer by
   lem:rot (`carrierRotationInt_cast`). `carrierR_eq_generic` is the integer identity `R(L) = |carrierRotationInt|`.
6. **Part 4, slots and coefficients** ((15), (16)): both slots are `1 − m_L − |r_L|` in `ℤ`
   (`slot_eq_generic`), both coefficients `coeffAt slot 0 poly` = `f.coeff (slot, 0)` (Finsupp evaluation, zero
   off the support): "This argument includes absent monomials, whose coefficients are zero. It imposes no sign
   gate or nonzero gate" — no gate appears in either definition or in the proof.
7. **Part 4, selectors and the sum** ((17)): CV:def:wind's `wt(L)` is the accepted `cornerSelector` of the
   corner polygon (`CV.weight = geoCarrierSelector`), SM's `wt` is lem:C-X1's `carrierWeight`; they agree
   (`carrierWeight_eq_geoCarrierSelector`, CS3 §B) and so do the products (`wind_eq_generic`). The sum over
   the common `Ind(G_P)` uses lem:C-X1's *selector form* of `C` (`C_X1.selector_form`, accepted) — "for each
   independent support the summands in the two formulas agree, including a mixed support with zero selector"
   is exactly `X1_summand_eq_of_cb` at every `S ∈ Ind`, with no uniformity filter on either side.

## 5. Fidelity risks (for the reviewer)

1. **The `hn` binder of `sides`.** R7's shape puts `hn : 3 ≤ n` first; `eventOfTriple hn g h` needs it (B1).
   No new `hn` was added anywhere (ruling R5): `pointwise` has def:C's and CV:def:X1's `hn`.
2. **`sides` quantifies `Q` with its own genericity proof `hQ`** rather than deriving it from
   `sideChamber_subset_generic`. Same content (proof irrelevance); chosen so the field reads "for every
   generic `Q` of the CV side chamber". If the reviewer prefers the derived form, it is a one-line change.
3. **The SM side value at an arbitrary `t`.** BRIDGE.md speaks of "its corresponding SM side value" (a value
   on the quotient side chamber `g.side b`). The field states the equality at every side parameter `t`, which is
   equivalent given prop:C-chamber (companion `cornerStateSum_sideTuple_eq_base`); no quotient object appears in
   the statement, as BRIDGE.md 1441 insists.
4. **Import of a row module.** The library module imports `SM.CS3` (accepted thm:C-S3) for three §B helpers.
   Permitted for U6 (AUTHOR_NOTES ~03:58Z); the alternative (copy the three proofs) is noted in §3.
5. **Dependence on row 102 under review.** `Bridge.B4`'s statement hash does not reach `SM.cb_products` (a
   theorem; only its type enters `semantic_dependencies`, and `B4Data`'s type mentions neither), but its proof
   does; if cb:products is revised, `B4_of_cb` is unaffected and `B4` follows any re-proof of row 102 unchanged.
6. **Defeq through proof irrelevance** is used throughout (objects at `hG.crossingGeometry` vs
   `generic_crossingGeometry hn hP`; `Piece hG.crossingGeometry S` vs `CV.Piece (SM.CB.cg hn hP) S`;
   `(eventOfTriple hn g h).sideBase` vs `g.sideBase`). This is the established pattern (U4 §6, CBBlocks
   header, Bridge/B1.lean shape decisions); the kernel checks it, so it is not a reading, but a reviewer
   should know why no transport lemma appears at these points.
7. **Nothing is assumed about the CV and SM chamber sets**, generic loci, or the letter R; `sides` uses only
   B1's event and the two accepted constancy theorems, and `pointwise` only accepted rows plus row 102.

## 6. How the files were checked (commands)

```
source /workspace/envs/lean/env.sh
cd work/lean
lake env lean ../drafts/cvdom/U6/GeoCarrierAgreement.lean                     # exit 0, no output
LP="$(lake env printenv LEAN_PATH)"; LEANBIN="$(lake env which lean)"
mkdir -p /tmp/u6_root/SM /tmp/u6_olean/SM
for f in "$PWD"/.lake/build/lib/lean/SM/*.olean; do ln -sf "$f" /tmp/u6_olean/SM/; done   # overlay of the SM package
cp ../drafts/cvdom/U6/GeoCarrierAgreement.lean /tmp/u6_root/SM/
LEAN_PATH="/tmp/u6_olean:$LP" "$LEANBIN" --root=/tmp/u6_root \
  -o /tmp/u6_olean/SM/GeoCarrierAgreement.olean /tmp/u6_root/SM/GeoCarrierAgreement.lean
LEAN_PATH="/tmp/u6_olean:$LP" "$LEANBIN" ../drafts/cvdom/U6/BridgeB4.lean       # exit 0, no output
```
Axioms: `#print axioms` appended to /tmp copies (/tmp/u6_ax/A.lean, B.lean) for all 22 + 7 declarations;
results as in §0 (standard on the `homfly`-free declarations; standard + `SM.lit_homfly`, `SM.lp_lm`,
`SM.lp_lm_uniqueness` on the rest, `Bridge.B4` included). Compile times ≈ 7 s and ≈ 8 s.

## 7. Open items

- Executor: port both files (headers only), build, map `Bridge:B4`, launch the review with §4; decide whether
  to keep `import SM.CS3` in the library module or copy the three CS3 §B helpers (§3).
- `Bridge.sm_R` (Bridge:theorem) can now be assembled from `Bridge.B4.pointwise` + `RProof.cv_R` (when the R
  lane lands) exactly as `smR_shape_of_hyp_R` shows; `Bridge.B4.sides` is available for the alternative
  chamber-value route of BRIDGE.md §3 (18)→(20)→(21).
- Row 102 (cb:products) is under review; `Bridge.B4` inherits its status.
