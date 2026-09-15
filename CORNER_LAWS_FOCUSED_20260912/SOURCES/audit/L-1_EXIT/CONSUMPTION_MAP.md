# L-1 EXIT — CONSUMPTION MAP on frame SM6

Every statement frame SM6 consumes from literature input L-1, with the SM
locator (file:line, frame SM6, manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`) and the
source locator (printed page). Depth column: the depth **this seat reached at
the source bytes this pass**; `[carried]` marks a row inherited by citation
from a named earlier lane rather than re-established here.

Files quoted: `sm-3-statesum.tex` `8785877b…`, `sm-4-knotlaws.tex` `3309fa3d…`,
`sm-11-registry.tex` `751fd3e0…`, `sm-refs.bib` `17277432…`, `DAG.md` `f4f4ecdd…`.

---

## A. The four L-1 environments as SM6 prints them

| # | environment | SM6 locator | what it asserts | source locator | depth |
|---|---|---|---|---|---|
| A1 | `lit:homfly` | `sm-3:916–923` (statement `917–921`, status line `922`) | a map `D ↦ H_D(a,z) ∈ Z[a^±1,z^±1]` on oriented link diagrams: (a) existence, (b) invariance under the three Reidemeister moves and planar isotopy, (c) value 1 on the crossing-free circle, (d) skein `aH_+ − a^{-1}H_- = zH_0`, (e) descent: "Its value depends only on the oriented link presented by `D`" | cited on `sm-3:922`: LM Theorem pp. 112–113, proof pp. 113–120, isotopy-class descent p. 120; the descent through Reidemeister's theorem `\cite{Reidemeister,Reidemeister1927}` | see A1 breakdown below |
| A2 | `lp:lm` (= `src:lm`) | `sm-3:935–960` | the literal LM construction `F_D(l,m)` and ten clauses: the ring; independence of component order, basepoints and switch order; plane-isotopy well-definedness; the source skein and `μ`; the UNDER-first initialization `μ^{c-1}`; per-move invariance via source Prop. 4 at a level given by the maximum crossing count of the supplied sequence; and the explicit **exclusion** of LM's final p. 120 inference | LM §1, pp. 111–120 | **T2**, with two named residues (§2.1 of the SM2 lane) `[carried in part]` |
| A3 | `lp:lm-uniqueness` | `sm-3:962–979` | `F_D` is the **only** map from oriented link diagrams (mod plane isotopy) into `T = Z[l^±1,m^±1]` that depends only on the isotopy class, is 1 on the unknot and satisfies the source skein; the competitor is unrestricted in support and coefficients; plus a bridging sentence converting "invariant under planar isotopy and the three Reidemeister moves" into "depends only on the isotopy class", **by Reidemeister's theorem** | LM Theorem pp. 112–113 with the uniqueness argument p. 120; "the same statement is Theorem 15.2 of Lickorish" | **T2 over the source ring on links** (LM p. 120 + GTM Thm 15.2, complete printed proof pp. 168–172); the **diagram-level** form is below T2 because the bridging sentence consumes Reidemeister's theorem (E-25-6) |
| A4 | `lp:coefficient-transport` | `sm-3:981–992` statement, `993–1039` proof | any two maps `D ↦ Q_D ∈ R = Z[a^±1,z^±1]` on oriented link diagrams that are planar-isotopy- and Reidemeister-invariant, are 1 on the circle and satisfy the campaign skein, coincide | **campaign step**, tagged `new` on `sm-3:991`, flagged for source cross-check under rule 8; reduces to A3 at `sm-3:1009` | re-derived independently this pass; **inherits A3's Reidemeister dependency** |

### A1 breakdown — `lit:homfly` clause by clause against its own cited locators

| clause | SM6 bytes | cited locator | at that locator? | depth |
|---|---|---|---|---|
| (a) existence of a map into **`Z[a^±1,z^±1]`** | `sm-3:917–918` | LM Theorem pp. 112–113, proof pp. 113–120 | **the ring is not.** LM's Theorem (p. 112, bottom) constructs `P(K) ∈ Z[l^±1,m^±1]`. The passage to `Z[a^±1,z^±1]` is the substitution `l = ia, m = −iz` plus integrality of the image | **below T2 at the cited locators**; **T2 at LM if LM Prop. 22 is added** (see D3) |
| (b) invariance under the three Reidemeister moves and planar isotopy | `sm-3:918–919` | LM proof pp. 113–120 | yes — LM **Prop. 4(n)**, p. 115, "𝒫(K) is invariant under Reidemeister moves which do not increase the number of crossings beyond n"; plane isotopy is LM p. 112 item (4) | **T2** (proof pp. 115–117; figure-driven, see `T2_DELTA.md` §1) |
| (c) value 1 on the crossing-free circle | `sm-3:919–920` | LM Theorem p. 113 | yes — LM formula **(II)**, p. 113: `𝒰(l,m) = 1` | **T2** |
| (d) skein `aH_+ − a^{-1}H_- = zH_0` | `sm-3:920–921` | LM Theorem p. 113 | LM prints formula **(I)** `lK_+ + l^{-1}K_- + mK_0 = 0`; the two are the same relation under `l = ia, m = −iz` after multiplying by the unit `−i` (verified exactly, `work/checks.py` C3, with the negative control C3b) | **T2** modulo the same substitution as (a) |
| (e) descent, "depends only on the oriented link presented by `D`" | `sm-3:921` | LM p. 120; Reidemeister's theorem | yes at LM p. 120 — the closing sentence of the theorem's proof, which asserts that two projections of isotopic links are joined by a finite move sequence *"that do not increase the number of crossings beyond n"* | **BELOW T2** — no printed proof of Reidemeister's theorem is on file (E-25-6). LM's own sentence is additionally the **bounded-crossing** form, stronger than the classical statement; SM6's use needs only the unbounded form |

---

## B. Proof-body consumption sites in SM6 (not status lines, not registry prose)

| site | SM6 locator | which L-1 statement it consumes | how |
|---|---|---|---|
| B1 | `lp:core` statement, `sm-3:1049` | A1 (existence) | "It equals `H_D` of Literature input~`lit:homfly`" |
| B2 | `lp:core` proof, **identification paragraph**, `sm-3:1164–1177` | A1(a)(b)(c)(d) + A4 (hence A3) | `P` and `H` are two maps into `R` with the transport lemma's four properties; `Lemma~lp:coefficient-transport` identifies them, so `P_D = H_D`. The paragraph says outright that `lit:homfly`'s (former) uniqueness clause "is not used" (`sm-3:1174–1175`) |
| B3 | `lp:core` proof, everywhere else | A2 | the Gaussian substitution `\eqref{lp:gaussian}`, the `(N,b)` induction, the `M_c` support argument, the `Q(a)` nonvanishing specialization — all from `lp:lm` (`sm-3:1060`, `1168`) |
| B4 | `cf:thm-carrierfloor` clause **(R)** proof, `sm-3:4338–4360` | A4 (hence A3), A1 | `D ↦ P_{-D}` and `D ↦ P_D` are two such maps; `lp:coefficient-transport` gives `P_{-D} = P_D`; then "Since `P_D` is the polynomial `H_D` of the oriented link presented by `D` (Thm `lp:core`), an oriented knot and its reverse have the same polynomial" |
| B5 | `cf:thm-carrierfloor` **mirror paragraph**, `sm-3:4528–4553` (`ι` at `sm-3:4537`, the transport applied at `sm-3:4543–4544`) | A4 (hence A3) | `ι = (a,z) ↦ (a^{-1},−z)`; `ι∘Q` satisfies the campaign skein, so two such maps agree by `lp:coefficient-transport`; gives `P_{D̄}(a,z) = P_D(a^{-1},−z)` |
| B6 | `prop:C-reversal` proof, `sm-4:1096–1107` (the L-1 consumption at `sm-4:1102–1103`) | B4 → A4 → A3 | reversal invariance of `H^+_Q` taken from `cf:thm-carrierfloor(R)` and `lp:core` |
| B7 | `lem:homflyrows` proof, `sm-4:237–265` | A1(e) explicitly | "Passing from these chosen representatives to the knot-class notation uses the **full global source premise** explicitly retained in Literature input~`lit:homfly`; it is not a conclusion of the local construction alone" (`sm-4:246–249`). Clause (ii) additionally consumes the **knot clause** (`z`-parity), registry L-1 |
| B8 | `rp:record-polynomial` and the record lemmas, `sm-3:1211`, `1867`, `3189`, `4264` | A2 | the source function `F_D` and its `μ`; equality of `F_D` from a named decorated record |
| B9 | `cp:finite-contact-path` / `fd:contact`, `sm-3:3274–3277`, `3492–3494`, `3509` | A1(e) explicitly | "Literature input~`lit:homfly` retains the original full global HOMFLY interface"; "The polynomial equality explicitly uses the original global HOMFLY source premise" |
| B10 | `prop:R-partial` proof, `sm-4:1307–1309` | A2 (narrowed in round 4) | Reidemeister-III invariance of the local polynomial now taken from `lp:core`, "whose Reidemeister invariance is proved from Literature input~`lp:lm`" — the seat L-1/L-5 C4 narrowing, verified landed |
| B11 | `lem:corner-values`(i), `sm-3:4810–4812` | A2 via `lp:core` | the crossing-free positive diagram has polynomial 1 by `lp:core` |
| B12 | `sm-4:29–34` (remark on `rem:crossing-record`) | A1(e) | fixes that "the oriented link presented by `D`" is the source's notion, "which Reidemeister's theorem (registry L-1) carries from the diagram" |
| B13 | `sm-7:375`, `398–402`, `1623`, `1705` | A2, A1 (normalization only) | the anchors section runs on `lp:lm`'s skein and initialization; Ng's and Jones's normalizations are compared with `lit:homfly`'s |

`DAG.md` (frame instrument, `f4f4ecdd…`) agrees on the edge set: line 292–312
lists `lp:coefficient-transport → lp:lm-uniqueness`, `lp:core → lit:homfly`,
`lp:core → lp:lm-uniqueness`, `cp:finite-contact-path → lit:homfly`,
`fd:contact → lit:homfly`, `lem:homflyrows → lit:homfly`,
`lit:torus → lit:homfly`; and `DAG.md:5` records the declared-input set of
`thm:comparison`'s 116-statement closure as
`{hyp:R, lit:homfly, lp:lm, lp:lm-uniqueness, ng:finite-word, src:contact}`.
I did not re-run the instrument; I checked its edge list against my own `\ref`
sweep of the frame and found no L-1 edge in one and not the other.

**Blast radius.** `lp:core` carries 67 `\ref`s in SM6 and `lit:homfly` 33.
Everything downstream of the identification `P = H` — which is the whole main
chain through `thm:floor` and `thm:comparison` — rides on A1(a)–(d), on A4, and
therefore on A3 and on Reidemeister's theorem.

---

## C. The registry entry L-1 (`sm-11-registry.tex:28–129`)

Every locator in the entry, checked at the source bytes this pass:

| registry claim | SM6 line | verified at | verdict |
|---|---|---|---|
| `lp:lm` = LM "Section 1, pp. 111–120 (Section 1 begins on p. 111; pp. 107–110 are their Section 0)" | `sm-11:31–34` | LM p. 111 **page render** `work/lm-05.png`: the header "**§1. THE EXISTENCE OF INVARIANT POLYNOMIALS**" is printed on p. 111, followed by the definitions (1) *ordered*, (2) *based*, (3) *oriented*, (4) *generic* | **correct**, with one precision: p. 111 carries **both** the tail of §0's property list (items (2)–(10)) **and** the §1 header, so "pp. 107–110 are their Section 0" is a page short of the truth. Immaterial to any consumer; recorded, not filed |
| `lp:lm-uniqueness` = LM "their Theorem, pp. 112–113, argument p. 120" | `sm-11:35–37` | LM p. 112 (theorem statement, foot of page), p. 113 (continuation), p. 120 (uniqueness paragraph) | **correct** |
| "the same statement is Theorem 15.2 of Lickorish" | `sm-11:37` | GTM 175 **p. 168**, Theorem 15.2 | **correct as to the polynomial, imprecise as to the domain**: GTM 15.2 quantifies over functions on `{Oriented links in S³}`; LM p. 120 and `lp:lm-uniqueness` quantify over functions on **diagrams/projections**. Recorded in `T1_STATEMENT.md` §3 |
| Reidemeister registered: `Reidemeister1927` pp. 24–32; the book `Reidemeister`, LM's [17]; "neither on file in this campaign" | `sm-11:41–44` | `sm-refs.bib:55,58`; LM's reference list | **the bibliographic records are correct**; "neither on file in this campaign" is **stale** — an English translation of the 1932 book is on disk (see `ACCESS_AUDIT.md`) |
| statement on file = Lickorish GTM "Chapter 1, p. 3 … through triangle moves with a sketch and no numbered theorem" | `sm-11:44–47` | GTM p. 3, the paragraph after Figure 1.2: prefaced *"With a little careful thought"*, it states that two diagrams of equivalent links are related by Reidemeister moves and an orientation-preserving plane homeomorphism | **correct, and weaker than the registry says**: GTM **p. 2** declares its own input assumed — the triangle-move characterisation of equivalence is introduced with *"This result will be assumed"*, its proof pointed to reference [17]. GTM's [17] resolves in the GTM references list to **Burde–Zieschang, *Knots*, de Gruyter (1986)** |
| "No printed proof of Reidemeister's theorem is on file, so the theorem is below T2 at every on-file locator; it is an open source item for the operator under rule 7, not dismissed" | `sm-11:47–50` | — | **the verdict is right; its stated ground is stale.** See `RECOMMENDATION.md` §4 |
| knot clause = LM property (1), p. 110, deduced as Proposition 22 (statement p. 133, proof pp. 133–134, §3 begins p. 132; tables begin p. 137); at one component `H_K ∈ Z[a^{±2},z^2]` under `l = ia, m = −iz`, "stronger than what is used here" | `sm-11:59–66` | LM p. 110 property (1) verbatim; Prop. 22 statement p. 133, proof pp. 133–134; §3 header "**§3. ALGEBRAIC PROPERTIES OF THE NEW POLYNOMIAL**" at the foot of p. 132; p. 137 opens the tabulation and its coding key | **all correct.** The `c = 1` consequence checked exactly (`work/checks.py` C1a/C1b): same-parity monomials land in `Z[a^±1,z^±1]`, opposite-parity ones do not |
| Chmutov–Polyak "eq. (1) and Remarks 1–2 print this document's normalization verbatim and both halves of the knot clause in its own variables"; Jaeger not on disk; "a corroboration, not a premise" | `sm-11:71–75` | CP **p. 1 eq. (1)**: `aP(D_+) − a^{-1}P(D_-) = zP(D_0)`, `P(unknot) = 1`, unlink `((a−a^{-1})/z)^{k−1}`; CP **p. 3 Remarks 1–2**: parity in `a` and `z` by component count, lowest `z`-power `= 1−k`, knots have no negative `z` powers | **correct and verbatim.** CP attributes existence to `[HOM, PT]` and the state-sum identity to `[Ja, Proposition 2]`, unprinted — so CP is T1 here, not a T2 root. The registry's "corroboration, not a premise" is the right grade |
| "every cited source quantifies over a different ring (LM and Lickorish over `Z[l^±1,m^±1]`; FYHLMO over a proper subring; PT over a Conway algebra)" | `sm-11:80–84` | FYHLMO **p. 240 Main Theorem**: "a unique function P from the set of isotopy classes of tame oriented links to the set of **homogeneous Laurent polynomials of degree 0 in x, y, z**" | **correct** for LM, Lickorish and FYHLMO, checked at the bytes. The PT clause is **carried** from the SM1 L-1 seat, not re-read here |
| reversal and mirror = LM Prop. 10(i),(ii), p. 123; connected sum and split union = LM Props. 9 and 8, p. 122 | `sm-11:100–105` | LM p. 123 Prop. 10(i) `P(rev K) = P(K)`, (ii) `P(K̄)(l,m) = P(K)(l^{-1},m)`; p. 122 Prop. 8 (split union, factor `μ`), Prop. 9 (connected sum, multiplicative) | **all four correct at the page.** Cost named in `T2_DELTA.md` §5 |
| "`lem:homflyrows` is available whole by citation to LM Propositions 9, 8 and 22 at two components (with `λ = lk`; seat L-1) — recorded as an available route" | `sm-11:106–109` | LM Prop. 22, p. 133: the lowest `m`-power is `1−c` with coefficient `(−l²)^{−λ}(−(l+l^{-1}))^{c−1}∏p_0^j(l)`, `λ` the total linking number | **the `c = 2` row matches** `lem:homflyrows`'s third formula under the substitution; recorded as available, correctly not consumed |
| "No uniqueness clause of Literature input `lit:homfly` is consumed by any proof of this frame" | `sm-11:94–96` | frame-wide `\ref{lit:homfly}` sweep, 33 sites, each read | **holds on SM6's bytes.** The struck clause (R-25-33 / F-25-131) is gone from `sm-3:917–921`; no site pairs `lit:homfly` with a uniqueness consumption |
| C4 (narrowing two over-consuming citations) "is taken in round 4: the Reidemeister-I step in `cf:lem-curl` and the Reidemeister-III step in `prop:R-partial` now cite `lp:core`" | `sm-11:123–128` | `sm-4:1307–1309` | **landed** at `prop:R-partial`; `cf:lem-curl`'s status records the same |

---

## D. What is consumed and is **not** an L-1 statement — recorded so the entry is not over-read

- **D1.** The uniqueness `lp:core` states in its own body ("the unique function on this exact diagram domain satisfying this skein and all these initialization values", `sm-3:1050–1054`) is proved internally from the `(N,b)` induction (`sm-3:1141–1149`) and consumes **no** L-1 uniqueness. Only the identification `P = H` does.
- **D2.** `lp:coefficient-transport` is a campaign step, not a literature statement. No source on disk prints it. It stays flagged under rule 8; SM6 flags it correctly on `sm-3:991` and at `sm-11:878`.
- **D3.** The step "`H` is `R`-valued" — i.e. that LM's `F_D` lands in `Z[a^±1,z^±1]` after `l = ia, m = −iz` — is consumed at B2 and is **not** at `lit:homfly`'s cited locators. It **is** at LM Prop. 22 (p. 133, proof pp. 133–134), which the registry already cites but scopes to `c = 1`. This is the single missing item of the recommendation.
