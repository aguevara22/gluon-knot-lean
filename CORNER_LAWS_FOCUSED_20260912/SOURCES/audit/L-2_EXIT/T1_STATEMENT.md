# L-2 EXIT — T1: each cited published statement against the frame's words

T1 (`phase2/VERIFICATION_STANDARD.md`): the source's full text on disk,
hashed and logged; the theorem **at the cited locator** states exactly what
the manuscript uses — hypotheses, conclusion, objects, quantifiers, checked
word by word.

**What T1 means for L-2 on SM6, stated before anything else.** On SM1 the
question was whether Carter + Smale carry `lit:gauss`'s composite statement.
They do not, and R-25-14 answered it by removing the literature input: SM6
prints the bridge as a proof that cites nothing (CONSUMPTION_MAP §1). So the
T1 question on SM6 is **not** "does a source prove the bridge" — nothing in
SM6 claims that — but the narrower and fully answerable one: **does each
sentence of the registry's support paragraph say what the source says at the
page it names?** That is what §§1–4 below check. §5 records what the frame
does *not* claim, so the entry is not read as stronger than it is.

Frame pin as in ACCESS_AUDIT §A0. Source hashes as in ACCESS_AUDIT §1.

---

## 1. Carter 1991 — `sm-11-registry.tex:145–148`

**The frame's sentence.** "Carter [Theorem (1.3), p. 282, and the filling
corollary of Section 2.3] classifies shadows (no over/under data) modulo word
reversal and global exponent flip under a filling hypothesis, with no
three-dimensional conclusion and the zero-crossing case unaddressed."

**Read at the bytes by this seat**, printed pp. 281–287:

| clause of the frame's sentence | what Carter's text says, and where | verdict |
|---|---|---|
| the locator "Theorem (1.3), p. 282" | §(1.3) on printed **p. 282**: "Theorem. Stable geotopy classes of immersed curves correspond to isomorphism classes of Gauss paragraphs." | **resolves; exact** |
| "the filling corollary of Section 2.3" | last sentence of §(2.3), printed **p. 283**: "From this equivalent definition and Theorem (1.3), Gauss paragraphs classify filling immersed curves up to a homeomorphism of the surface." (the abstract states the same with "fill … in the sense that the complementary regions are disks") | **resolves; exact.** The section locator carries no page claim, and the sentence is in §2.3 |
| "classifies shadows (no over/under data)" | §(2.1), p. 282: the record is made by "recording the double points in order … The exponent is +1 if the other sheet crosses from left to right … Left and right are determined by the orientation of the image surface G." **No over/under datum appears anywhere in the paper** | **correct** |
| "modulo word reversal and global exponent flip" | §(2.2), p. 283, isomorphism moves: "(1) cyclically permuting …; **(2) reversing the sequence of any words**; (3) permuting the alphabet set A; **(4) changing all the exponents from + to − and vice versa**; (5) permuting the order …" | **correct, verbatim** |
| "under a filling hypothesis" | filling is the hypothesis of the §2.3 corollary and of the abstract; Theorem (1.3) itself is stated for *stable* geotopy (surgery allowed) | **correct**, and the frame is right to attach the hypothesis to the pair of locators it cites |
| "with no three-dimensional conclusion" | the conclusion is a homeomorphism of surfaces (§2.3 "geotopic … a homeomorphism h: G₁→G₂ such that hγ₁=γ₂"). Three-manifolds occur only in §4's summary of the *companion* paper | **correct** |
| "the zero-crossing case unaddressed" | §(3.1), p. 284: "The vertices are the elements of the set A. The oriented edges are the two-letter syllables found in the cyclic Gauss words". The one-letter word is handled explicitly ("there is an edge aa"); **an empty alphabet yields no complex**, and §3.2's proof matches complementary *polygons*, of which there are none | **correct** |

**T1 verdict, Carter: REACHED for the frame's sentence.** Every clause is
what the paper says at the locator named.

---

## 2. Smale 1959 — `sm-11-registry.tex:149–153`

**The frame's sentence.** "Smale [Theorem 6, p. 625] concerns diffeomorphisms
of the sphere, whereas the bridge's sphere-isotopy step is printed for the map
it produces (Lemma `lem:gauss-sphere-isotopy`) and cites neither Smale nor
Kneser 1926, the topological reference Smale names (unfetched; escalation
E-25-4, needed only under the seat's alternative route R2, not taken)."

| clause | source / frame bytes | verdict |
|---|---|---|
| "Theorem 6, p. 625" | printed **p. 625**: "Theorem 6. The space Ω of all orientation preserving diffeomorphisms of S² has as a deformation retract the rotation group SO(3). In fact there is a homotopy H_v: Ω→Ω such that for each f∈Ω (a) H_v(f)(x) is C^∞ in (v,x), (b) H_0(f)=f, (c) H_1(f) is a rotation of S², and (d) if f∈SO(3), H_v(f)=f." | **resolves; exact** |
| "concerns diffeomorphisms of the sphere" | p. 621: Ω is "all orientation preserving **C^∞ diffeomorphisms** of S²"; "a diffeomorphism is a differentiable homeomorphism with differentiable inverse" | **correct** |
| "Kneser 1926, the topological reference Smale names" | p. 621, verbatim: "The analogue of Theorem A for the topological case was proved by H. Kneser [2]"; reference [2], p. 626: "H. Kneser, Die Deformationssätze der einfach zusammenhängenden Flächen, Math. Z. vol. 25 (1926) pp. 362–372" — a full article. (Reference [3], Munkres, is "Abstract 548-137, Notices Amer. Math. Soc. vol. 5 (1958) p. 582", an announcement; SM6 does not cite it) | **correct** |
| "the bridge's sphere-isotopy step is printed for the map it produces" | `lem:gauss-sphere-isotopy`, sm-3:544–550: "Every **positive PL self-homeomorphism** of the sphere is isotopic to the identity through **positive topological homeomorphisms**" — the homeomorphism category, i.e. exactly the object Smale's theorem does **not** cover | **correct, and load-bearing**: this is why the category mismatch that sank the SM1 citation is no longer a defect |
| "cites neither Smale nor Kneser 1926" | `grep cite` over sm-3:330–800 → **empty** | **correct** |

**T1 verdict, Smale: REACHED for the frame's sentence.**

---

## 3. Dowker–Thistlethwaite 1983 — `sm-11-registry.tex:154–158`

**The frame's sentence.** "Dowker–Thistlethwaite [Corollary 1.2, p. 24] give
the orientation-preserving refinement under their Rule 1 (n ≥ 3, no proper
invariant subinterval), restated there from Corollary 1.1 without a printed
proof — this corrects the Phase 1.99 record 'proved via Lemma 1' — and outside
the low-crossing and composite subpolygons of this document."

| clause | source bytes | verdict |
|---|---|---|
| "Corollary 1.2, p. 24" | printed **p. 24**: "Corollary 1.2. If S is realizable, there is a unique orientation f such that (S, f) is realizable, and the realization of (S, f) is unique up to orientation preserving homeomorphism of S²." | **resolves; exact** |
| "the orientation-preserving refinement" | the conclusion "unique up to **orientation preserving** homeomorphism of S²" is precisely the refinement of Theorem 1's bare "homeomorphism" | **correct** |
| "under their Rule 1 (n ≥ 3, no proper invariant subinterval)" | Rule 1, printed **p. 20**, verbatim: "(i) n ≥ 3; (ii) no proper subinterval [i, j] mod 2n of {1,2,…,2n} is mapped onto itself by the involution a: k ↦ a_k." Printed **p. 21**: "From now on, we consider only sequences satisfying Rule 1." | **correct** |
| "restated there from Corollary 1.1 without a printed proof" | p. 24, immediately before Cor. 1.2: "The following is a restatement of Corollary 1.1." No proof paragraph follows Cor. 1.2; the text runs on to the `φ_i` construction | **correct** |
| "this corrects the Phase 1.99 record 'proved via Lemma 1'" | Lemma 1's proof ends on p. 23 with "…which proves the lemma, and hence also the theorem", after which **Cor. 1.1 is stated and is itself followed by no proof paragraph** (the next text, "Note that if two directed arcs cross each other…", sets up the definition of f). So the refinement step is unprinted at **both** corollaries | **correct — and, if anything, understated**; see T2_DELTA §3 |
| "outside the low-crossing and composite subpolygons of this document" | DT p. 20's own justification of Rule 1: a two-element invariant interval means "the projection would be immediately reducible"; a longer proper invariant interval means "K is the composite of two knots each with at least three crossings"; and "If K can be projected with no crossings, it is regarded as unknotted. Thus S cannot be the trivial sequence for which n = 0" | **correct** |

**T1 verdict, DT: REACHED for the frame's sentence.**

---

## 4. Read–Rosenstiehl — `sm-11-registry.tex:159–162`

**The frame's sentence.** "Read–Rosenstiehl [Theorem 6, p. 871] (printed
proof) show that a valid crossing sequence with r interlace components has
`2^{r-1}` realizing curves on the sphere — the published reason the bridge's
over/under and sign clauses are indispensable."

| clause | source bytes | verdict |
|---|---|---|
| "Theorem 6, p. 871" | printed **p. 871** (PDF page 266): "Theorem 6. If S is a valid crossing sequence with r connected components then there exist on the sphere 2^{r−1} distinct curves having S as crossing sequence." | **resolves; exact** |
| "(printed proof)" | a proof paragraph follows at the same page ("Proof. If the bipartite graph I(S′) has r components then the vertices may be divided into two classes … By virtue of the above lemma, for each connected component of S the corresponding 2-connected component of G is unique up to duality"), plus a worked r = 3 example | **correct** |
| "r interlace components" | the theorem's "r connected components" is unpacked in its own proof as the components of the **bipartite interlacement graph I(S′)**; interlacement is the paper's own vocabulary (p. 847-region: "the binary relation of interlacement between the pairs of letters") | **correct as a gloss** |
| "on the sphere" | the theorem says "on the sphere"; the example's closing note distinguishes sphere from plane ("The two curves differ actually on the plane by the choice of the infinite face"), which is why the count is 2^{r−1} and not 2^r | **correct, and the right category** for `lit:gauss`, whose own statement disclaims any fixed-infinity assertion (sm-3:680–681) |
| "the published reason the bridge's over/under and sign clauses are indispensable" | RR's datum is the **crossing sequence alone** — cyclic order plus pairing, with no exponent, no over/under. The theorem exhibits, with proof, distinct sphere curves sharing that datum | **supported, with one precision** (T2_DELTA §4): RR proves that clauses (a)+(b) **alone do not suffice**; it does not certify that over/under + sign are the *correct* or *sufficient* supplement. The frame does not claim it does — but a reader may over-read "indispensable" |

**T1 verdict, RR: REACHED for the frame's sentence**, with the precision above.

---

## 5. What SM6 does *not* claim, recorded so the entry is read at its strength

- **No published source is a premise.** sm-11:162–163 says it; the byte check
  (no `\cite` in sm-3:330–800) confirms it. The nine-item residue the SM1
  seat enumerated (plane→S², automatic filling, PL admission, the
  over/under→shadow dictionary, the orientation-preserving refinement, the
  zero-crossing case, homeomorphism→isotopy, S²→S³, a definition of
  "presents") is not carried by citation on SM6: every one of those steps is
  printed inside sm-3:337–785 or fixed by `rem:crossing-record`.
- **The entry is not called T3.** sm-11:141–142: "an internal printed proof,
  not a ``T3''" (R-25-13; F-25-62). Checked by this seat: `grep -n T3
  sm-11-registry.tex` returns four hits — lines 10–11 (the section preamble:
  "no Lean formalization or formal T3 certificate is claimed … and the words
  ``T3 available'' are not used"), line 142 (L-2's disclaimer) and line 246
  (L-3's). A `grep -rn "T3 available"` over the whole frame returns exactly
  **one** hit — sm-11:11, inside the preamble sentence that declares the words
  are not used. No entry claims the tier.
- **The composite is flagged under rule 8**, twice: sm-11:139–141 and
  sm-11:876–877. This is the correct disposition for a bench proof standing
  where no published statement of the composite has surfaced.
