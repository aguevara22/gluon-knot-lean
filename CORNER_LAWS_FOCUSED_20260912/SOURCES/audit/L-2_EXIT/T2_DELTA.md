# L-2 EXIT — T2 DELTA: what was read at proof depth, and what was not

T2 = T1 **plus** the source's own proof of the cited statement read and
checked to establish it, every reduction followed. This file records, per
source, (i) whether this seat read the proof **at the pages**, (ii) the delta
between what the source proves and what SM6 attributes to it, and (iii) the
one question the charter puts to this seat about the frame's own text:
**are the printed proof's steps complete relative to the supports?**

---

## 0. The frame-level answer, first

Because the printed bridge cites nothing (CONSUMPTION_MAP §1), **no source
carries any load in SM6 under L-2**, and therefore no delta between a source
and the frame can open a hole in a proof. The T2 exposure of this entry is
confined to the four scope clauses in `sm-11-registry.tex:144–163`. Each is
checked below at the source's own proof depth where a proof exists, and the
absence of a proof is recorded where it does not.

Correspondingly, the question "is the printed proof complete relative to the
supports" has a precise answer on SM6, and it is not the SM1 answer:

- On **SM1** the bridge was a citation, and nine enumerated steps of the used
  statement sat in no read literature (prior seat, `T2_PROOF.md` §5).
- On **SM6** every one of those nine is printed or defined inside the frame.
  This seat located each at a byte:

| step (prior seat's numbering) | where SM6 discharges it |
|---|---|
| 1. plane → `S²` with the standard orientation | class prose sm-3:345–346 ("To retain the outer region in the construction, compactify the oriented plane to an oriented sphere") + the proof's first sentence, sm-3:685–687 |
| 2. automatic filling (disc complementary regions) | sm-3:722–736, the regular-neighbourhood / complementary-disc paragraph, explicitly refusing the abstract-ribbon shortcut (733–736: "Connectedness of an abstract ribbon alone would not prove this…") |
| 3. PL / polygonal admission | `lem:gauss-pl-model`, sm-3:372–421 |
| 4. over/under and σ → the ray/rotation datum | the sign paragraph sm-3:697–701 and `eq:gauss-ray-order` with its justification, sm-3:703–713 |
| 5. orientation-preserving refinement | produced by construction: sm-3:738–750, concluding at 746–750 ("The resulting named PL sphere homeomorphism $h$ preserves ambient orientation, the oriented traversal and the over/under designation separately") |
| 6. zero-crossing case | sm-3:772–778 ("If there are no crossings, both shadows are embedded oriented circles…"); the theorem asserts it at 679 |
| 7. homeomorphism → isotopy of `S²` | `lem:gauss-sphere-isotopy`, sm-3:544–615, **in the homeomorphism category** |
| 8. isotopy of `S²` → equality of oriented knots in `S³` | suspension paragraph sm-3:756–770 + `lem:gauss-height-isotopy`, sm-3:617–669 |
| 9. a definition of "presents" | `rem:crossing-record`(c), sm-4:24–29, referred to the statement of `lit:gauss` |

**This is a location check, not a referee's verdict.** Bench A refereed the
argument (tag at sm-3:682, cleared 2026-09-05T15:51:04Z). This seat's finding
is the source-side one: **the printed proof appeals to no published theorem**
— the only proper names in the block are Jordan/Schoenflies (line 438,
disclaimed), Euler (line 490, computed), Alexander (line 604's label, formula
printed) — so there is **no unsourced citation** anywhere in it, and nothing
in it is below T2 *by reason of a source*. Whether each printed step is
*valid* is bench A's lane, not this seat's.

---

## 1. Carter 1991 — proof READ AT THE PAGES by this seat

**Read:** §3.1 (pp. 284–285), the canonical cell complex — vertices = the
letters of A, oriented edges = the two-letter syllables, the four compass
directions determined by starring and exponents, faces read off by the
printed "always turn left" table (p. 285); §3.2 (pp. 285–286), the proof
proper — (⇒) one sentence, "Geotopies cannot change the intersection
information of the curve"; (⇐) build the canonical surface, map the cycles
into G through γ, approximate each cycle by an embedded circle disjoint from
the image, surger G along it, iterate until every region is simply connected,
then match the complementary polygons through their bounding cycles.
"This completes the proof."

**Does it establish Carter's own theorem?** Yes at the level of published
surface topology, and self-containedly: the paper's planarity references
([7] DT, [11] Lovász–Marx, [14] RR) appear in §1.2 as history, not as
dependencies. Two honest caveats, both recorded because T2 requires
following reductions:

- the surgery step ("if this approximating circle represents some homotopy,
  then the surface G can be surgered along the circle", p. 285) is asserted,
  not carried out — normal compression for a six-page PAMS note;
- the construction takes crossing labels as vertices, so **n = 0 has no
  canonical complex**, confirmed by this seat at p. 284.

**Delta against SM6's sentence: none.** SM6 attributes to Carter exactly the
shadow-level, filling, unoriented-quotient content that his statement and
proof carry, and explicitly says the zero-crossing case is unaddressed and
there is no three-dimensional conclusion. **T2 reached for Carter's own
theorem; the frame's claim about it does not exceed it.**

*Not carried over, deliberately.* The prior seat observed that re-running
Carter's §3.2 **construction** with exponent-fixing data would yield an
orientation-preserving `h`, and correctly refused to call that "Carter proves
it". SM6 does not make that move at all — Carter is not a premise — so the
temptation is closed rather than managed.

## 2. Smale 1959 — proof read at the cited pages; the chain not re-read here

**Read by this seat:** p. 621 (Theorems A and B; the Kneser and Munkres
sentences; the definitions of Ω, ℑ, S), p. 625 (Theorem 6 with (a)–(d) and
the opening of its proof: Ω̄ ⊂ Ω with `e¹(f), e²(f)` orthonormal, shown to be
a deformation retract), p. 626 (the retraction `G_v`, the rotation `α(f)`,
`K_v(f) = T_v(f∘α(f))α(f)^{-1}`, "obtained by composing G_v and K_v").
**Not re-read by this seat:** pp. 622–624 (Lemmas 1–3, Theorems 4–5). The
prior seat read all six pages and its record stands as theirs
(`phase25/LITERATURE.md`, 2026-09-05T15:14:41Z entry).

**Delta against SM6's sentence: none, and the delta that mattered on SM1 is
gone.** On SM1 the citation was load-bearing and the category was wrong
(Smale: C^∞ diffeomorphisms; the bridge produces a homeomorphism; Smale
himself defers the topological case to Kneser). SM6 (a) does not use Smale,
(b) says the mismatch out loud, and (c) prints the homeomorphism-category
statement itself as `lem:gauss-sphere-isotopy`. **Kneser 1926 is therefore not
a dependency of SM6**; E-25-4 is an optional archival upgrade, not a blocker.

## 3. Dowker–Thistlethwaite 1983 — the refinement's proof is ABSENT, checked

**Read by this seat:** Rule 1 with its full justification paragraph (p. 20);
the standing scope sentence and the definition of a realization, with
conditions (α),(β),(γ) on G (p. 21); the last page of Lemma 1's induction
(p. 23, Case 1 and Case 2, ending "…which proves the lemma, and hence also
the theorem"); Corollary 1.1 (pp. 23–24); Corollary 1.2 and the following
`φ_i` construction (p. 24). The **body** of Lemma 1's induction (pp. 22–23
opening) was read by the prior seat, not re-read here.

**The deflation, re-verified first-hand.** Corollary 1.1 is stated
immediately after Lemma 1's proof and is followed by no proof paragraph — the
next text ("Note that if two directed arcs cross each other in the oriented
plane…") sets up the definition of the orientation `f`. Corollary 1.2 is
introduced verbatim as "The following is a restatement of Corollary 1.1" and
likewise carries none. **So the orientation-preserving refinement is
unprinted at both corollaries**, and SM6's "restated there from Corollary 1.1
without a printed proof — this corrects the Phase 1.99 record 'proved via
Lemma 1'" is right, and if anything mild: the phase-1.99 record is corrected,
and the residual unprinted step is at Cor. 1.1 as much as at Cor. 1.2.

**Delta: the frame is accurate; one precision is available.** DT's `f(i)` is a
per-visit *left/right* datum defined on p. 24 ("f(i) = 1 if the arc p([a_i−1,
a_i+1]) crosses the arc p([i−1,i+1]) from right to left"). It is **not** an
over/under bit and not `σ = sgn det(u_o,u_u)`; translating between them is the
campaign's own dictionary. SM6 does not assert otherwise — it says only that
DT "give the orientation-preserving refinement", which is true of DT's own
objects — but a reader could take "the orientation-preserving refinement" to
mean the refinement *for the SM's decorated record*. Since DT is not a
premise, this cannot damage a proof; it is an **editorial precision**, logged
in RECONCILIATION as an observation, not a finding.

## 4. Read–Rosenstiehl — Theorem 6's printed proof read at p. 871

**Read:** the lemma immediately above Theorem 6 (two 2-connected plane graphs
without bicycles, same edge set and same bicycle space, are topologically
identical or dual), Theorem 6, its proof, and the r = 3 worked example with
its closing remark that (d) and (e) "generate the same diagonal on the sphere.
The two curves differ actually on the plane by the choice of the infinite
face." Also read: the paper's opening (p. 843) defining a crossing sequence,
and p. 847 on interlacement.

**Checked:** the argument closes — bipartiteness of `I(S′)` splits the
vertices in `2^{r−1}` ways, each split gives a plane graph, each 2-connected
component being determined up to duality by the lemma. The count is *on the
sphere*, the plane/infinite-face ambiguity having already been quotiented —
which is the same quotient `lit:gauss` takes (sm-3:680–681, and the proof's
closing paragraph 780–784).

**Delta, stated precisely.** RR's datum is the crossing sequence alone:
cyclic order + pairing, **with no exponent and no over/under**. Theorem 6
therefore proves that clauses (a)+(b) of the bridge's hypothesis **cannot
suffice** — two diagrams can share them and admit no orientation-preserving
sphere homeomorphism carrying one to the other, since the underlying curves
are already distinct on the sphere. That is a genuine published refutation of
the weakened bridge, and it bites exactly at the step the printed proof
performs (construction of the named PL sphere homeomorphism `h`,
sm-3:738–750). **What RR does not do** is certify that over/under and sign
are the correct or sufficient supplement; sufficiency is the printed
theorem's own claim. SM6's phrase "the published reason the bridge's
over/under and sign clauses are indispensable" is true on the "necessary"
reading and silent on the "sufficient" one; logged as an observation.

**Cross-source consistency check, run by this seat** (it substantiates two of
the frame's scope clauses at once): RR's example `S = ABCEFGEFGDBCDA` has
r = 3 and four distinct sphere curves; the block `EFGEFG` occupies positions
4–9 and is closed under the pairing, i.e. it is **a proper invariant
subinterval**, which is exactly what DT's Rule 1(ii) forbids. DT's uniqueness
and RR's multiplicity are therefore consistent, and Rule 1(ii) is precisely
the hypothesis that suppresses the extra interlacement components. Both scope
clauses in `sm-11-registry.tex:154–162` are correct for the same structural
reason.

---

## 5. What this seat did NOT read

- Smale pp. 622–624; the opening of DT Lemma 1's induction (pp. 22–23 start).
  Both were read by the prior seat; neither is a premise of SM6.
- Kneser 1926 and Roseman 2000 — **not on disk**; routes in ACCESS_AUDIT §2.
  Neither is a dependency of SM6's L-2 material.
- The RC source module `phase198/manuscript/RC_v4/d2_foundations.tex` (the
  port's origin). The prior seat read it in full and matched it to the SM
  text; this seat's object is SM6's bytes, and the port's *provenance* is the
  curator's replay lane, not a source question.
