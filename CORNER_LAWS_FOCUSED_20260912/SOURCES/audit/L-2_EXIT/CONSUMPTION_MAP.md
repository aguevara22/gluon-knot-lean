# L-2 EXIT — CONSUMPTION MAP (frame SM6)

What the exit frame consumes under the L-2 heading, with the SM locator and,
where a published statement is involved, the source locator. Frame pin:
`FRAMED_MANIFEST_SM6.sha256` self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`, 20/20
verified by this seat before any byte below was cited.

**The governing fact of this map, checked at the bytes:** under R-25-14, L-2
is no longer a literature input. The bridge is a **printed proof** occupying
`sm-3-statesum.tex:337–785`, and **that block contains no `\cite` at all**
(`sed -n '330,800p' sm-3-statesum.tex | grep -n cite` → empty). The registry
says the same in its own words at `sm-11-registry.tex:162–163`: *"Carter and
Smale are not premises."* Consequently **no published statement is a premise
of anything SM6 proves under L-2**; the published material appears only as
declared corroboration in the registry's support sentence, and that is where
the T1/T2 obligation of this entry now lives.

## 1. The printed proof and its lemmas (all in `sm-3-statesum.tex`)

| SM object | locator (env / proof) | what it states | status tag in the frame |
|---|---|---|---|
| admitted diagram class + compactification sentence | 337–351 (prose under the subsection heading "An internal named-record bridge") | "A diagram here is a finite polygonal immersion, or a regular smooth immersion with finitely many transverse double points and possible finitely many corners away from crossings… all SM subpolygon diagrams and their regular clean modifications are included… compactify the oriented plane to an oriented sphere. All topological extensions needed for the bridge are proved below." | prose (no tag) |
| `def:positive-lift` | 325–335 | positive crossing `det(u_o,u_u)>0`; the positive lift of a subpolygon | definition |
| `def:gauss-record` | 352–370 | the **named record**: occurrence set `M`, successor `s`, fixed-point-free pairing `τ`, over/under bit, sign `σ(c)=sgn det(u_{c,O},u_{c,U})` (eq. 358–360); named-record isomorphism `Φ`; the positive PL extension `Φ̄`; empty-`M` clause | definition |
| `lem:gauss-pl-model` | 372–379 / proof 380–421 (+ multi-component note 423–426) | finite PL shadow models by orientation-preserving ambient isotopies of the page, retaining names, four-ray orders, traversal and over/under | `proved (refereed: bench A …; transcribed from RC fd:pl-model (C016))` |
| `lem:gauss-two-discs` | 428–436 / proof 437–542 | constructive polygonal two-disc theorem incl. the exterior region; prescribed positive PL boundary maps extend | `proved (refereed: bench A …; RC fd:pl-discs)` |
| `lem:gauss-sphere-isotopy` | 544–550 / proof 551–615 | **every positive PL self-homeomorphism of the sphere is isotopic to the identity through positive topological homeomorphisms** | `proved (refereed: bench A …; RC fd:sphere-isotopy)` |
| `lem:gauss-height-isotopy` | 617–624 / proof 625–669 | two continuous height assignments with the same strict over/under order give ambient-isotopic oriented links | `proved (refereed: bench A …; RC fd:height-isotopy)` |
| **`lit:gauss`** (Named-record bridge) | **671–683 / proof 684–785** | one-component oriented generic diagrams in the admitted class, in the oriented plane; a visit bijection preserving oriented cyclic order, pairing, over/under and `sgn det(u_o,u_u)` ⟹ the diagrams present the same oriented knot, i.e. **their compatible lifts in `S^3` are joined by an ambient isotopy preserving traversal orientation**; the crossing-free case included (679); no preservation of the unbounded face or of infinity assumed or asserted (680–681) | `proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC fd:gauss, printed in place of registry L-2 under ruling R-25-14, flagged for source cross-check (C016))` |

Dependency record agrees: `DAG.md:101–106` lists `lit:gauss` at sm-3:671
with dependencies `def:gauss-record`, `def:positive-lift`,
`lem:gauss-{pl-model,two-discs,sphere-isotopy,height-isotopy}`.

Named appeals inside the proof block, all checked (grep over sm-3:330–800 for
`standard|well[- ]known|classical|it is known|theorem of|Jordan|Schoenflies|
Alexander|Euler|cf\.|\\cite`): "Jordan or Schoenflies" appears once, at
**line 438**, *to disclaim their use* ("Here is a finite triangulation and
disc construction, so no Jordan or Schoenflies conclusion is being assumed");
"Euler" at **line 490** names a characteristic the proof computes itself;
"Alexander" occurs only as the name of the isotopy the proof prints
explicitly — `\label{eq:gauss-alexander}` at **line 604** with the formula at
605–606, and "two Alexander isotopies" at **line 612**. **No unproved published input is
appealed to anywhere in the block.**

## 2. The registry entry L-2 (`sm-11-registry.tex:130–172`)

| part | locator | content |
|---|---|---|
| heading + disposition | 130–143 | "Named-record bridge — a printed proof, no longer a literature input"; the four prerequisites named; printed under R-25-14 because the cold seat found the cited sources below T2 and below T1 at any locator (F-25-61); bench A refereed and cleared it; **flagged for source cross-check under rule 8**; "an internal printed proof, not a ``T3'' (R-25-13; F-25-62)"; "The conclusion is oriented knot equivalence in `S^3`, without a fixed-infinity assertion." |
| published partial supports | 144–163 | the four sources, each with an explicit scope clause (table §3) and the closing "Carter and Smale are not premises." |
| consumers | 164–172 | `\ref{lit:gauss}` occurs in exactly one proof, `prop:star-torus`; in no proof of `sec:statesum` or `sec:knotlaws`; `thm:C-S3`, `prop:C-chamber`, `prop:C-silent` route through `rp:record-polynomial`, `lc:presentations`, `lp:core` (F-25-59, F-25-79); the terms fixed in `rem:crossing-record` (F-25-60) |
| status table rows | 521–525 | the five items with their provenance and tags |
| rule-8 flag | 876–877 | "Flagged for source cross-check under rule 8: Theorem `lit:gauss` (the composite statement)…" |

## 3. Every published statement named under L-2, with source locator

None is a premise (§ above). Each was read at its page by this seat.

| source, as cited in SM6 | SM locator | source locator, verified at the bytes | what the source actually states there |
|---|---|---|---|
| Carter, `\cite[Theorem (1.3), p. 282, and the filling corollary of Section 2.3]{Carter}` | sm-11:145–148 | Carter 1991, printed **p. 282 §(1.3)**; the corollary sentence at the end of **§(2.3), printed p. 283** | Thm (1.3) verbatim: "Stable geotopy classes of immersed curves correspond to isomorphism classes of Gauss paragraphs." §2.3 closing: "From this equivalent definition and Theorem (1.3), Gauss paragraphs classify filling immersed curves up to a homeomorphism of the surface." |
| Smale, `\cite[Theorem 6, p. 625]{Smale}` | sm-11:149–153 | Smale 1959, **printed p. 625** | "The space Ω of all orientation preserving diffeomorphisms of `S²` has as a deformation retract the rotation group SO(3)", with (a)–(d) |
| Kneser 1926 (named, unfetched; E-25-4) | sm-11:151–153 | Smale **printed p. 621**: "The analogue of Theorem A for the topological case was proved by H. Kneser [2]"; reference [2] on **p. 626**: Math. Z. **25** (1926) 362–372 | the topological analogue; **not on disk** |
| Dowker–Thistlethwaite, `\cite[Corollary 1.2, p. 24]{DowkerThistlethwaite}` | sm-11:154–158 | DT 1983, **printed p. 24** (Cor. 1.2); Rule 1 at **printed p. 20**; the standing scope sentence at **printed p. 21**; Cor. 1.1 at **pp. 23–24** | Cor. 1.2 verbatim: "If S is realizable, there is a unique orientation f such that (S,f) is realizable, and the realization of (S,f) is unique up to orientation preserving homeomorphism of `S²`." Preceded by "The following is a restatement of Corollary 1.1." Rule 1: "(i) n ≥ 3; (ii) no proper subinterval [i,j] mod 2n … is mapped onto itself by the involution a". p. 21: "From now on, we consider only sequences satisfying Rule 1." |
| Read–Rosenstiehl, `\cite[Theorem 6, p. 871]{ReadRosenstiehl}` | sm-11:159–162 | RR, **printed p. 871** = PDF page 266 | "Theorem 6. If S is a valid crossing sequence with r connected components then there exist on the sphere `2^{r-1}` distinct curves having S as crossing sequence." **with a printed proof** (bipartite `I(S')` splitting; each 2-connected component of G unique up to duality, by the lemma immediately above), plus a worked r = 3 example |

Bibliography rows checked at `sm-refs.bib`: `Carter` (line 6), `Smale`
(line 7), `DowkerThistlethwaite` (line 52), `ReadRosenstiehl` (line 53).
The RR row reads *Colloq. Math. Soc. János Bolyai* **18**, Combinatorics
(Keszthely 1976), Vol. II, North-Holland, **1978**, pp. 843–876. Verified at
the volume's own bytes: the paper's running head reads "18. COMBINATORICS,
KESZTHELY (HUNGARY), 1976", the copyright page reads "Budapest, Hungary,
**1978**", the volume title page reads "VOL. II", the paper opens on printed
p. 843 (PDF 238) and ends on printed p. 876 (PDF 271). **The bib's 1978 is
the imprint year and is correct**; the ledger's shorthand "Read–Rosenstiehl
1976" is the colloquium year. No defect.

## 4. The consumer

| consumer | locator | what it asks of the bridge |
|---|---|---|
| `prop:star-torus` (the star is a torus knot) | statement `sm-7-anchors.tex:338–342`; **proof 343–351** | For `r ≥ 2`: `sv:star-record`, *by its polygon-level clause*, supplies the complete decorated record bijection between the actual positive star (the polygonal positive lift of `K_r`) and the standard closure `B_r`; "Both are knots. Theorem `lit:gauss` therefore identifies their oriented knot types in `S³`." Tag: `transcribed (unrefereed)` with bench A's SM2 clearance and the round-5 F-25-163 touch recorded |
| `rem:crossing-record` (definitions, **not a proof**) | `sm-4-knotlaws.tex:6–34` | (a) fixes *crossing record* = the named record of `def:gauss-record` (and notes that for a positive lift every sign is +1, so the content is cyclic order + pairing + over/under); (b) fixes the over/under bit as the chirotope datum `det(λ̃_i,λ̃_j)>0`, constant on a chamber; (c) fixes *present the same oriented knot* **by the statement of `lit:gauss`**, and states that the only proof using the notion is the star/torus identification |

Byte check of the registry's consumer claim, run by this seat:
`grep -n "ref{lit:gauss}" *.tex` returns 7 hits — `sm-11` ×4 (registry
prose/tables), `sm-7:341` (a `\status` line) and **`sm-7:347` (inside
`prop:star-torus`'s proof, 343–351)**, and `sm-4:26` (**inside the remark
6–34, not inside any proof**). The registry's sentence at sm-11:164–166 is
therefore **exactly true as written**. `DAG.md:230` lists `prop:star-torus`
with dependency `lit:gauss`; `DAG.md:176` lists `thm:C-S3` **without** it.
The three records — registry, DAG, proof text — now agree.

Hypothesis discharge at the consumer, checked: `lit:gauss` requires
**one-component** diagrams in the admitted class; the proof supplies
"Both are knots" (`B_r` is the closure of `(σ_1…σ_{r-1})^{2r+1}` and
`gcd(r,2r+1)=1`), and the class sentence at sm-3:339–345 explicitly admits
"all SM subpolygon diagrams and their regular clean modifications", which is
the clause covering `sv:star-record`'s corner-rounded `D_r`.
