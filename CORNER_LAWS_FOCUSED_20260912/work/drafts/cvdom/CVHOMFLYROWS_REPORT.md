# Row 157 — CV:lem:homflyrows — report

File: `work/drafts/cvdom/CVHomflyRows.lean` (325 lines). Main declaration `CV.homflyrows : CV.CVHomflyRowsData`.
Compiled 2026-09-14 with `cd work/lean && lake env lean ../drafts/cvdom/CVHomflyRows.lean`: exit 0, no errors, no
warnings, no incomplete proofs, no new axioms. `#print axioms CV.homflyrows` (on a /tmp copy):
`propext, Classical.choice, Quot.sound, SM.lit_homfly, SM.lp_lm, SM.lp_lm_uniqueness` — exactly the expected set.
Imports: `SM.MarkedProducts` (which itself imports `CV.Axioms`) and `CV.RecordHomfly`.

Source: reference/R/CV/d6_vertexedge.tex, `lem:homflyrows`, statement 117–141, proof 142–261. SM counterpart:
`SM.homflyrows : SM.HomflyRowsData` (work/lean/SM/MarkedProducts.lean:363 bundle, :4954 theorem; fixed statement
work/drafts/MarkedProducts_statement.lean:434–461), sm-4-knotlaws.tex:230–266.

## 1. Clause → field map

| tex lines | printed clause | field of `CV.CVHomflyRowsData` | proof |
|---|---|---|---|
| 119–120 | "Put R = ℤ[a^{±1}, z^{±1}] and δ = (a − a⁻¹)/z ∈ R" | not a clause; `R`, `R.delta` (SM/LinkLaurentRing.lean:76, :193); sanity `CV.delta_eq` (`R.delta = (a − a⁻¹) · z⁻¹`, rfl) and `CV.delta_mul_z` (`δ · z = a − a⁻¹`, `R.delta_mul_z` :195) | — |
| 122–124 | (i) "For oriented knots K, J, P_{K#J} = P_K P_J" | `connected_sum` — for one-component `K J`, marked representatives `K' J' : MarkedDiagram` with `LinkEquiv K K'.D`, `LinkEquiv J J'.D`, and any `D` with `IsCleanMarkedJoin K' J' D`: `homfly D = homfly K * homfly J` | `SM.homflyrows.connected_sum` verbatim (MarkedProducts.lean:4955–4957: mp:join `join_value_of_iso` :2402, `P_eq_homfly` PolynomialBlock.lean:667, `homfly_descent` LinkInterfaces.lean:395) |
| 126–128 | (i) "for an oriented knot K and an oriented link J, P_{K⊔J} = δ P_K P_J" | `knot_split_link` — one-component `K`, ANY `J`, representatives `LinkEquiv K K'`, `LinkEquiv J J'`, `IsSplitUnion K' J' D`: `homfly D = R.delta * (homfly K * homfly J)` | `CV.homfly_splitUnion` (file :154) = `SM.Link.P_splitUnion` (MarkedProducts.lean:4899, stated for ANY two diagrams; mp:stack `SM.stack.split_union` Stack.lean:1346 + `presentations` PolynomialBlock.lean:1177) + `P_eq_homfly` + `homfly_descent` |
| 130–135 | (ii) "D … with ordered components D₁, D₂ and linking number λ: [z^{−1}]P_D = (a − a⁻¹) a^{−2λ} [z^0](P_{D₁}P_{D₂})" | `two_component_row` — `D.componentCount = 2`, ordered tags `i ≠ j`, `ℓ : ℤ` with `CV.IsLinkingNumber D i j ℓ` (`2 * ℓ = mixedSignSum D i j`): `zRow (-1) (homfly D) = (aPow 1 - aPow (-1)) * aPow (-(2 * ℓ)) * zRow 0 (homfly (D.knotRestrict i) * homfly (D.knotRestrict j))` | `SM.homflyrows.two_component_row` (MarkedProducts.lean:4961–4966: mp:lowest `two_component_row_of_lowest` :2500, `P_eq_homfly`, `CV.zRow_zero_mul_of_inSupportM_one` Axioms.lean) with `twoLinking D i j = 2 * ℓ` (`CV.IsLinkingNumber.twoLinking_eq`, `twoLinking := mixedSignSum` MarkedProducts.lean:144) |
| 136–139 | (iii) "for oriented knots K₁,…,Kₙ (n ≥ 1), P_{K₁⊔⋯⊔Kₙ} = δ^{n−1} P_{K₁}⋯P_{Kₙ}" | `split_union_family` — `1 ≤ n`, one-component `K : Fin n → Diagram`, representatives `K'` with `∀ i, LinkEquiv (K i) (K' i)`, `CV.IsSplitUnionFamily K' D`: `homfly D = R.delta ^ (n - 1) * ∏ i, homfly (K i)` | `CV.homfly_splitUnionFamily` (file :219) ← `CV.P_splitUnionFamily` (:207) = `SM.stack_formula` (Stack.lean:1317, mp:stack-value with `q = n`; `BlockOrdered` vacuous since no crossing joins two blocks) + `presentations` per block, then `P_eq_homfly`, `homfly_descent` |

Supplementary (not fields): `CV.two_component_row_rows` (:288) — (ii) with `[z^0]` of the product split into the product of
`[z^0]` rows via `CV.ax_homfly.knot_parity`/`knot_product_z0` (the form the R lane reads, plan §157 (2));
`CV.IsSplitChain` (:303) / `CV.homfly_splitChain` (:311) — the printed proof's parenthesization "K₁ ⊔ (K₂ ⊔ ⋯ ⊔ Kₙ)"
(tex 220–224) with (iii) proved by the printed induction from (i)'s split identity; `CV.exists_linkingNumber` (:131, mp:zero-link
`SM.zero_link.half_sum_integer` ZeroLink.lean:44), `CV.IsLinkingNumber.unique` (:137);
`CV.isSplitUnionFamily_of_isSplitUnion` (:171): `IsSplitUnion K J D → IsSplitUnionFamily ![K, J] D` (the `n = 2` case of the
n-ary predicate is (i)'s split union).

## 2. Readings (design question (a))

All readings are SM lem:homflyrows' readings (MarkedProducts_statement.lean notation map, lines 85–99), reused verbatim:
- "oriented knot K": one-component `Diagram` standing for its `LinkEquiv` class (SM/LinkMoves.lean:760; D2 — isotopy of links
  is read through Reidemeister's theorem, which is outside the formal scope, exactly as in the accepted CV:ax:homfly row).
  "oriented link J": any `Diagram`. "P": `SM.homfly` (CV:ax:homfly / CV:def:homfly identification; no other one introduced).
- "K # J": any clean marked join of marked representatives, `IsCleanMarkedJoin K' J' D` (MarkedProducts.lean:95, record-level
  join `Record.joinRecord`, D9). CV's own proof builds exactly this (tex 149–152: a ball at `p`, two short arcs cut, cross-paired).
  Well-definedness of `#` on classes is not claimed (D9) — the row asserts the identity for every clean marked join of every pair
  of marked representatives, which is what CV's proof proves.
- "K ⊔ J" / "put K in a ball disjoint from J" (207): `IsSplitUnion K' J' D` (MarkedProducts.lean:276): two component blocks, no
  crossing between them, block restrictions with the records of `K'`, `J'`.
- "linking number λ": `CV.IsLinkingNumber D i j ℓ := 2 * ℓ = mixedSignSum D i j` (ZeroLink.lean:31, sum of decorated signs over
  ALL mixed crossings between `i` and `j`). The factor 2 is explicit: SM writes `aPow (-(twoLinking D i j))` with
  `twoLinking = mixedSignSum = 2·lk`; CV's field writes `aPow (-(2 * ℓ))`, literally "a^{−2λ}". The printed proof's convention
  "λ₊ = λ₋ + 1 at a positive versus negative mixed crossing" (235–236) is this one. Existence of `ℓ` is mp:zero-link.
- "ordered components D₁, D₂": ordered pair of tags `i ≠ j` with `D₁ = D.knotRestrict i`, `D₂ = D.knotRestrict j`
  (MarkedProducts.lean:126). The order is immaterial to the identity (`mixedSignSum_comm` :1857; the product commutes) but the
  field takes an ordered pair as printed.
- "K₁ ⊔ ⋯ ⊔ Kₙ": `CV.IsSplitUnionFamily K' D` — one diagram partitioned into `n` component blocks (surjection `blk : Fin D.Γ.c → Fin n`),
  no crossing between distinct blocks, block `i` has the record of `K' i` (`blockRestrict`, Stack.lean:58). This is the
  `n`-block form of `IsSplitUnion` (the two agree at `n = 2`, `isSplitUnionFamily_of_isSplitUnion`). "(n ≥ 1)" kept as `1 ≤ n`
  (implied by the surjection since `D` has a component; kept for fidelity, unused).
- Where CV differs from SM: (1) the split identity is for a knot and a LINK (SM: two knots) — the field `knot_split_link` has no
  hypothesis on `J`; (2) λ vs lk (bookkeeping above); (3) clause (iii) is CV-only.

## 3. Knot ⊔ link clause (design question (b))

`SM.Link.P_splitUnion (K' J' D : Diagram) (h : IsSplitUnion K' J' D) : P D = R.delta * (P K' * P J')` (MarkedProducts.lean:4899)
is stated for arbitrary diagrams — no component-count hypothesis — so the knot ⊔ link clause follows with no new geometric lemma:
`CV.homfly_splitUnion` is `P_splitUnion` + `P_eq_homfly` + `homfly_descent` (4 lines). CV's based relative-uniqueness argument
(tex 154–219) is not formalised; the library's mp:stack route replaces it, as SM's proof already does. `SM.homflyrows.split_union`
itself could not be used (it demands `J.componentCount = 1`), which is why the general lemma is consumed directly.

## 4. CV (ii) vs SM two_component_row (design question (c))

Literally the same identity after substituting `twoLinking D i j = 2 * ℓ`:
- coefficient `(a − a⁻¹) a^{−2λ}` in the same order: SM `(aPow 1 - aPow (-1)) * aPow (-(twoLinking D i j))`, CV
  `(aPow 1 - aPow (-1)) * aPow (-(2 * ℓ))`;
- the `[z^0]` is of the PRODUCT `homfly D₁ * homfly D₂` in both (CV prints `[z^0](P_{D₁}P_{D₂})`; SM's statement prints the
  same, its proof converting mp:lowest's product of rows through `CV.zRow_zero_mul_of_inSupportM_one`);
- the two-component hypothesis `D.componentCount = 2` and `i ≠ j` in both. The product-of-rows form is re-exported as
  `CV.two_component_row_rows` for the R lane.

## 5. Fidelity risks (design question (d))

1. Isotopy = `LinkEquiv` (planar isotopy + RI/RII/RIII on polygonal diagrams); Reidemeister's theorem is outside scope (D2).
   Inherited from CV:ax:homfly; nothing new here.
2. `K # J` is read on marked representatives; the class-level operation's well-definedness is NOT asserted (D9). The printed
   statement writes `P_{K#J}` for knot classes, presupposing it; the Lean row is the identity for every clean marked join.
3. `K ⊔ J` is the polygonal "disjoint page images" reading (no crossing between two component blocks), not "K in a ball disjoint
   from J in S³"; equivalent modulo the same out-of-scope theorem.
4. Printed one-component hypotheses (knots) and `1 ≤ n` are kept in the fields but unused by the proofs: the identities hold for
   all links. Rows are on the printed domain, neither stronger nor weaker (accepted CV-lane policy, Axioms.lean).
5. (iii) rendered as an `n`-block split diagram; the printed proof's binary parenthesization is proved separately
   (`homfly_splitChain`) but is not the field. The two renderings are not proved equivalent (only `n = 2` ↔ `IsSplitUnion`).
6. δ is `R.delta = (a − a⁻¹) · z⁻¹` (multiplication by the unit `z⁻¹`, not a ring division), consistent with the accepted
   CV:def:homfly row; `delta_mul_z` records "δ z = a − a⁻¹".
7. `mixedSignSum` sums decorated signs of def:positive-lift over strand pairs; that this is twice the topological linking number
   is the accepted mp:zero-link reading (SM/ZeroLink.lean), not re-derived here.
8. Proof route differs from the printed one everywhere (library rows mp:join, mp:stack, mp:lowest, lp:core instead of based
   relative uniqueness and mixed-switch invariance); the statements are the printed ones.

## 6. Library declarations consumed (file:line)

`SM.homflyrows.connected_sum`, `.two_component_row` — SM/MarkedProducts.lean:4954–4966; `SM.Link.P_splitUnion` :4899;
`SM.Link.IsSplitUnion` :276; `SM.Link.IsCleanMarkedJoin` :95; `SM.Link.MarkedDiagram` :75; `SM.Link.twoLinking` :144;
`SM.Link.aPow` :51; `SM.Link.Diagram.knotRestrict` :126, `knotRestrict_componentCount` :131; `SM.stack_formula` — SM/Stack.lean:1317;
`SM.blockRestrict` :58; `SM.BlockOrdered` :65; `SM.presentations` — SM/PolynomialBlock.lean:1177; `SM.P_eq_homfly` :667;
`SM.homfly_descent` — SM/LinkInterfaces.lean:395; `SM.Link.LinkEquiv.refl` — SM/LinkMoves.lean:766; `SM.mixedSignSum` — SM/ZeroLink.lean:31;
`SM.zero_link.half_sum_integer` :44; `SM.Link.R.delta` — SM/LinkLaurentRing.lean:193, `R.delta_mul_z` :195; `zRow` :335;
`SM.Link.Diagram.restrict_congr` — SM/MarkedProducts.lean:1774; `CV.ax_homfly.knot_parity`, `.knot_product_z0` — CV/Axioms.lean.
