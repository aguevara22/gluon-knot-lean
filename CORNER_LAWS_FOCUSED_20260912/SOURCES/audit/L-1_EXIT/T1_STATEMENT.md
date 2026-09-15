# L-1 EXIT — T1: statement comparison at the cited locators

T1 = the source's full text on disk, hashed and logged; the statement **at the
cited locator** says what the manuscript uses, checked word by word — hypotheses
and conclusion, objects and quantifiers.

Source hashes and page maps: `ACCESS_AUDIT.md`. Frame: SM6,
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`.
Quotation is kept to short operative fragments; everything else is paraphrase
with the page, which is what a word-by-word check needs and all it needs.

---

## 1. `lit:homfly` (`sm-3:917–921`) against LM pp. 112–113 and p. 120

**SM6 says.** There is a map on oriented link diagrams into `Z[a^±1,z^±1]`,
invariant under the three Reidemeister moves and planar isotopy, equal to 1 on
the crossing-free circle, satisfying `aH_+ − a^{-1}H_- = zH_0` on every skein
triple; its value depends only on the oriented link presented by `D`.

**LM p. 112 (theorem statement, foot of the page) says.** There is a *unique*
function associating to each `K ∈ 𝒴` an element `P(K) = K(l,m) ∈ Z[l^±1,m^±1]`
which depends only on the isotopy class of the oriented link, such that
(I) `lK_+(l,m) + l^{-1}K_-(l,m) + mK_0(l,m) = 0` for a right/left/vacuous
crossing triple (p. 113), and (II) `𝒰(l,m) = 1` for the one-component unknot
(p. 113). Here `𝒴` is the set of generic **based ordered oriented** link
projections (p. 112 items (5) and (2)–(4)), `Z[l^±1,m^±1]` is fixed by p. 112
item (8), and *ascending* — SM6's UNDER-first — is p. 112 item (6).

**Deltas, exactly:**

| | SM6 | LM at the cited locator | disposition |
|---|---|---|---|
| ring | `Z[a^±1,z^±1]` | `Z[l^±1,m^±1]` | **DELTA.** Not a wording difference: the substitution `l = ia, m = −iz` sends `Z[l^±1,m^±1]` into `Z[i][a^±1,z^±1]`, and landing in `Z[a^±1,z^±1]` is a further fact. See §5 |
| skein | `aH_+ − a^{-1}H_- = zH_0` | `lK_+ + l^{-1}K_- + mK_0 = 0` | same relation under the same substitution, up to the unit `−i`. Checked exactly (`work/checks.py` C3; broken-substitution control C3b fails as it must) |
| unknot value | 1 on the crossing-free circle | (II), `𝒰(l,m) = 1` | **match** |
| invariance | the three Reidemeister moves and planar isotopy | Prop. 4(n) p. 115 (per level); plane isotopy p. 112 item (4) | **match**, with SM6's own level bookkeeping (§2) |
| descent | "depends only on the oriented link presented by `D`" | LM p. 120, closing sentence of the theorem's proof | **match as a statement**; its proof depth is §6 |
| domain | oriented link **diagrams** | based ordered oriented **projections** `𝒴` | LM's `P` is proved independent of basepoints and order (Props 1, 2, 6), so it descends to diagrams. **No gap**, and SM6's `lp:lm` imports exactly those independence clauses |
| uniqueness | **absent** — struck in round 4 | present in LM's statement, over `Z[l^±1,m^±1]` | **correctly absent.** R-25-33 / F-25-131 landed; verified on SM6's bytes at `sm-3:917` ("There is a map"), and no `\ref{lit:homfly}` site in the frame pairs it with a uniqueness consumption |

## 2. `lp:lm` (`sm-3:935–960`) against LM §1, pp. 111–120

Each clause matched to a printed sentence. Rows marked `[carried]` were
established clause-by-clause by the SM2 seat
(`evidence/source_audit/L-1-L-5_SM2/T2_DELTA_SM2.md`, lane verified) and
re-confirmed here at the locator rather than re-read in full.

| `lp:lm` clause | LM locator | verdict |
|---|---|---|
| the function is *the one constructed in LM §1*, "not an arbitrary function with similar values" | *The Recursive Definition (n)*, p. 113 | match |
| the ring `Z[l^±1,m^±1]` | p. 112 item (8) | match |
| independent of component order | Prop. 6(n), p. 119, conclusion at the top of p. 120 | match `[carried]` |
| independent of basepoints | Prop. 2(n), p. 114 | match `[carried]` |
| independent of the order of required switches | Prop. 1(n), p. 114 | match `[carried]` |
| defined modulo positive page isotopy | p. 112 item (4) — projections equivalent under an isotopy of the plane | match, wording delta only ("positive page isotopy" vs "isotopy of the plane") |
| the skein `lF_+ + l^{-1}F_- + mF_0 = 0` and `μ = −(l+l^{-1})m^{-1}` | p. 113, formula (I) and (II′) | match. `μ ↦ (a−a^{-1})/z` exactly (`checks.py` C4) |
| initialization `F_D = μ^{c-1}` on every based ordered `c`-component UNDER-first diagram | *Inductive Hypothesis (n−1)* (II′) and *The Recursive Definition (n)*, p. 113 | match |
| "UNDER-first" | p. 112 item (6), LM's *ascending* | match, definitionally |
| invariance under each ordinary oriented Reidemeister move, applied at the level given by the maximum crossing count of the supplied sequence (`sm-3:953–956`) | Prop. 4(n), p. 115 | **statement matches**; the level bookkeeping is SM6's own one-line reading. **New this pass:** that exact inference is *printed* in Lickorish GTM 175 **p. 172** — the closing paragraph of Thm 15.2's proof draws `P` invariant under **all** Reidemeister moves from the observation that any finite collection of moves stays within `𝒟_n` for some `n` |
| the **exclusion** of the p. 120 inference from arbitrary ambient isotopy (`sm-3:957–958`) | LM p. 120, closing sentence | match — the declined sentence occurs once, and SM6 declines it explicitly |

## 3. `lp:lm-uniqueness` (`sm-3:962–979`) against LM p. 120 and GTM Thm 15.2

**SM6 says.** LM prove that `F_D` is the only map from oriented link diagrams
(mod plane isotopy) into `T = Z[l^±1,m^±1]` that depends only on the isotopy
class of the oriented link, is 1 on the unknot and satisfies the source skein;
uniqueness is asserted among **all** such maps, with **no restriction on the
support or on the coefficients** of a competitor; a map on diagrams that is
invariant under planar isotopy and the three Reidemeister moves depends only on
the isotopy class by **Reidemeister's theorem**; and no statement over
`Z[a^±1,z^±1]` is imported.

**LM p. 120 says.** Suppose `𝒬` were *"another such function from 𝒴 to
Z[l^±1,m^±1]"* different from `𝒫`; take the least `k` with a disagreement in
`𝒴_k`; since the two agree on `𝒴_{k-1}`, formula I forces a disagreement at an
unlink; but induction on the number of components makes them agree on unlinks
in `𝒴_k`.

| | SM6 | LM p. 120 | verdict |
|---|---|---|---|
| competitor unrestricted in support/coefficients | asserted | **verbatim support**: the only qualifier LM place on `𝒬` is *"another such function"*, i.e. the three hypotheses of the theorem; no support, parity or coefficient condition appears | **match**, and this is the load-bearing clause for `lp:coefficient-transport` |
| ring | `T = Z[l^±1,m^±1]`, "the source's" | `Z[l^±1,m^±1]` | **match**; SM6 says outright that nothing over `Z[a^±1,z^±1]` is imported here |
| domain | oriented link diagrams mod plane isotopy | `𝒴` (based ordered oriented projections mod plane isotopy) | **match up to forgetting basepoints and order**, which LM's Props 1, 2, 6 license |
| hypothesis on the competitor | "depends only on the isotopy class of the oriented link" | same | **match** |
| the bridging sentence (R-move invariance ⟹ isotopy-class dependence, by Reidemeister's theorem) | printed inside the statement body | **not in LM.** It is the campaign's own conversion step, resting on Reidemeister's theorem | **DELTA**, correctly disclosed by the environment's own status line ("with Reidemeister's theorem") and at `sm-11:35–50` |
| "the same statement is Theorem 15.2 of Lickorish" | asserted | GTM **p. 168**: a unique function on **`{Oriented links in S³}`** into `Z[l^±1,m^±1]`, 1 on the unknot, satisfying the same skein | **imprecise as printed.** GTM 15.2 quantifies over functions on **links**, not on diagrams. The two coincide only after the same descent the bridging sentence supplies. A one-clause wording item, not a mathematical gap |

## 4. `lp:coefficient-transport` (`sm-3:981–992`) — statement-level check

Not a literature statement; a campaign step. At statement level I checked only
that its hypotheses are exactly what its consumers can supply and that it
claims no more than the transport:

- hypotheses: two maps into `R`, planar-isotopy- and Reidemeister-invariant, 1 on the crossing-free circle, campaign skein. Each of the four consumers (B2, B4, B5 of the consumption map) establishes all four for both of its maps at the site. **Consistent.**
- it disclaims existence, ambient-isotopy invariance and any descent theorem (`sm-3:989–990`). **Consistent with its proof**, which produces `Q_D = φ(F_D)` and concludes equality, never existence.
- it is tagged `new`, attributed to Codex S54-P1 = P-25-10, and flagged for source cross-check under rule 8 (`sm-3:991`). **Correct tagging.**

## 5. The ring step, stated precisely — this is the one T1 defect

`lit:homfly` asserts `H_D ∈ Z[a^±1,z^±1]`. Its cited locators give
`F_D ∈ Z[l^±1,m^±1]`. Under `l = ia, m = −iz`, a monomial `l^j m^k` acquires the
coefficient `i^j(−i)^k`, which is a rational integer **iff `j ≡ k (mod 2)`**
and is `±i` otherwise (`work/checks.py` C1a and the negative control C1b, all
exponents `−8 … 8`).

The parity `j ≡ k (mod 2)` for every monomial of `F_L`, at **every** component
count, is exactly **LM property (1), p. 110**, deduced as **LM Proposition 22**
(statement p. 133, proof by induction on `(n,s)` pp. 133–134). So the ring of
`lit:homfly` is available at T2 **in the same source**, one citation away — but
it is **not** at the locators `lit:homfly` cites, and the registry cites Prop. 22
only for the `c = 1` knot clause (`sm-11:59–66`).

Independently, **Chmutov–Polyak p. 1 eq. (1)** prints the campaign's ring,
skein, unknot value and unlink value verbatim, and **p. 3 Remarks 1–2** print
the parity in `a` and `z` by component count and the lowest `z`-power `1−k`.
That is the campaign-ring form of the same fact, but CP rest existence on
`[HOM, PT]` and the parity on `[Ja, Proposition 2]`, unprinted and not on disk
(E-25-3). **CP is a T1 corroboration, not a T2 root** — which is exactly how
`sm-11:71–75` grades it.

## 6. Reidemeister's theorem — statement on file, at the bytes

- **Lickorish GTM p. 3.** Statement present, in the direction L-1 needs (equivalent links ⟹ their diagrams are related by Reidemeister moves and an orientation-preserving plane homeomorphism), prefaced *"With a little careful thought"*. No numbered theorem, no proof.
- **Lickorish GTM p. 2.** Its input — that equivalent links differ by a finite sequence of triangle moves — is introduced with *"This result will be assumed"*, its proof pointed to reference **[17]**, which the GTM reference list resolves to **Burde–Zieschang, *Knots*, de Gruyter (1986)**.
- **LM p. 120.** LM use a **stronger** form: the move sequence is required not to increase the crossing number beyond `n`. SM6's own consumption of Reidemeister (the bridging sentence of `lp:lm-uniqueness`, and `sm-4:29–34`) needs only the **unbounded** form, because its maps are invariant under *every* move. This is a genuine and correct piece of care by the frame, and it is worth recording that the frame does **not** inherit LM's bounded claim.

**T1 verdict.** `lp:lm`: T1 clean. `lp:lm-uniqueness`: T1 clean over the source
ring, with one imprecise cross-reference (GTM 15.2's domain) and one campaign
bridging sentence correctly disclosed. `lit:homfly`: T1 for clauses (b), (c),
(d) and (e); **below T1 for the ring of clause (a)** at the locators it cites,
repairable by one citation already present elsewhere in the same entry.
