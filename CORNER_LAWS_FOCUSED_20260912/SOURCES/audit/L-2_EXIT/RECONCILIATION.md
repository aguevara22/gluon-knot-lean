# L-2 EXIT — RECONCILIATION: every L-2 ledger row against SM6's bytes

Verdict vocabulary: **addressed** = the row's repair is present at a byte this
seat read on SM6, and the row's substance is answered; **open** = still live
on SM6; **lapsed** = the row's object no longer exists in the frame, so the
row can neither be met nor breached.

Rows of the L-2 class, taken from `phase25/evidence/curator/LEDGER.md`
(`grep -n "gauss\|L-2\b"` returns F-25-59, 60, 61, 62, 63, 79, 85, 136, 163
and E-25-1, E-25-4; F-25-58 is an L-3 row that names L-2 only in passing).
Frame pin as in ACCESS_AUDIT §A0.

| row | what it required | verdict on SM6 | the byte |
|---|---|---|---|
| **F-25-58** (source L-3; L-2 named only as the co-consumed entry) | print the contact dictionary; reorder L-3's sources Geiges-first with the page; note the edition | **not this seat's row** — L-3's. Recorded here only because the task list names it: the L-3 entry now runs `sm-11:173–254` and the bib's `Etnyre` row carries the arXiv-v2 note (`sm-refs.bib:9`). No L-2 obligation attaches | sm-11:173–254; sm-refs.bib:9 |
| **F-25-59** | make DAG and the proof cite `lit:gauss` where used (registry ↔ DAG ↔ proof disagreed on `thm:C-S3`) | **addressed**, by the opposite and better resolution: `thm:C-S3` no longer consumes the bridge at all. All three records now agree. `grep -n "ref{lit:gauss}"` over the frame returns no hit in any `sm-4` proof; `DAG.md:176` lists `thm:C-S3` without `lit:gauss`; the registry states the routing through `rp:record-polynomial`, `lc:presentations`, `lp:core` | sm-11:164–170; DAG.md:176; sm-4 (no proof hit) |
| **F-25-60** | define "crossing record" and "present the same oriented knot" | **addressed.** `rem:crossing-record` (sm-4:6–34) fixes both, plus the chirotope clause (b) the row asked for: (a) crossing record = the named record of `def:gauss-record`, with the positive-lift simplification; (b) the over/under bit is `det(λ̃_i,λ̃_j)>0`, constant on a chamber; (c) "present the same oriented knot" = the conclusion of `lit:gauss`, ambient isotopy of the compatible `S³` lifts | sm-4:6–34, esp. 24–29 |
| **F-25-61** (the verdict row: L-2 below T2 and below T1 at any locator) | R-25-14's disposition: print the RC port as the frame's proof, refereed by bench A; keep the published partial supports with exact scope; flag for source cross-check | **addressed.** The proof is printed at sm-3:337–785 with the four lemmas, tagged `proved (refereed: bench A …)`; the four supports are printed with their scope clauses and every clause of every scope sentence was verified at the source pages by this seat (T1_STATEMENT §§1–4); the rule-8 flag appears twice | sm-3:337–785; sm-11:130–163, 876–877 |
| **F-25-62** | correct the DT record ("proved via Lemma 1" overstates) and stop calling L-2 "T3 available" | **addressed, on both halves.** The registry says Cor. 1.2 is "restated there from Corollary 1.1 without a printed proof — this corrects the Phase 1.99 record 'proved via Lemma 1'", which this seat re-verified at DT pp. 23–24; and it says the bridge is "an internal printed proof, not a ``T3''". `grep -rn "T3 available"` over the frame returns one hit, sm-11:11, inside the sentence declaring the words are not used | sm-11:154–158, 141–142, 10–11 |
| **F-25-63** | add Read–Rosenstiehl Thm 6 to L-2's support sentence | **addressed.** Printed at sm-11:159–162 with the locator "Theorem 6, p. 871", verified by this seat at the page together with its printed proof and worked example. One precision, logged as an observation below | sm-11:159–162 |
| **F-25-79** | the "contact and global consumers of §3" wording is wrong (the only consumer is `prop:star-torus`); move the Roseman pointer from L-2 to L-1 | **addressed, both halves.** The consumer sentence at sm-11:164–170 is exactly true at the bytes (7 `\ref{lit:gauss}` hits: 4 registry, 1 `\status` line, 1 in `prop:star-torus`'s proof, 1 in a remark — none in any other proof). "Roseman" occurs once in the frame, inside **L-1**, saying the request belongs to L-1's route and not to L-2 | sm-11:164–170; sm-11:113–116 |
| **F-25-85** | record row (L-3/L-4 corroborations) | **not an L-2 row**; no L-2 obligation. Listed because its text mentions `fd:gauss-integrand`, an unrelated label in the contact section (sm-3:2831) | — |
| **F-25-136** | mechanism-4 repairs; touches `lem:gauss-two-discs` only as a downstream user (`cb:embedded-rotation`) | **not an L-2 source row.** Checked only that `cb:embedded-rotation` still cites `lem:gauss-two-discs` and carries a bench-A clearance | DAG.md:166 |
| **F-25-163** | `prop:star-torus` attributed to `sv:star-record` a bijection the lemma exported only for the rounded diagram `D_r` | **addressed** (author/bench-A class, but it is L-2's sole consumer, so this seat checked it): `sv:star-record`'s statement now carries the polygon-level clause ("The rounding creates and removes no crossing visit, so the positive lift of `K_r` itself … has the same decorated record as `D_r`"), and `prop:star-torus`'s proof cites it by name ("by its polygon-level clause") | sm-7:198–201 (clause), sm-7:343–351 (proof) |
| **E-25-1** — Roseman 2000 | escalated, never dismissed | **open with the operator; blocks nothing in L-2.** This seat re-ran the publisher route (403) and confirmed at the bytes that the frame routes the request to L-1. No step of SM6's L-2 material needs it. **This seat does not withdraw the escalation** — it remains L-1's, by the frame's own words | ACCESS_AUDIT §2.2; sm-11:113–116 |
| **E-25-4** — Kneser 1926 | escalated, never dismissed | **open with the operator; not a dependency of SM6.** Eight routes tried by this seat (six new), all blocked; Crossref confirms the bibliographic record exactly as Smale's reference [2] reads at p. 626. SM6's sphere-isotopy step is the printed `lem:gauss-sphere-isotopy`, in the homeomorphism category, citing nobody — so the category gap that made Kneser necessary on SM1 no longer exists | ACCESS_AUDIT §2.1; sm-3:544–615; sm-11:151–153 |

## Observations (precision, not findings)

Neither bears on soundness, because **no source is a premise** on SM6
(sm-11:162–163, and the byte check: no `\cite` in sm-3:330–800). Both are
about how a reader may take a support sentence. Recorded so the entry is not
over-read; neither is proposed as a repair.

- **O-1 (DT's `f` is not the SM's decorated record).** sm-11:154–155 says DT
  "give the orientation-preserving refinement". DT's orientation `f` is a
  per-visit *left/right* datum (p. 24: "f(i) = 1 if the arc p([a_i−1,a_i+1])
  crosses the arc p([i−1,i+1]) from right to left"), not an over/under bit and
  not `σ = sgn det(u_o,u_u)`. The refinement is DT's, for DT's objects; the
  translation to the SM's record would be the campaign's own step, and the
  frame neither performs nor needs it.
- **O-2 ("indispensable" is the necessity half).** sm-11:161–162 calls RR
  Thm 6 "the published reason the bridge's over/under and sign clauses are
  indispensable". What RR proves at p. 871 is that cyclic order + pairing
  **alone do not suffice** (`2^{r−1}` distinct sphere curves share them).
  That clauses (c),(d) are the *right* supplement, and sufficient, is the
  printed theorem's own claim, not RR's. The frame does not assert otherwise.

## Rows of the charter's generic list that are not L-2's

The charter's reconciliation list (F-25-80…84, 108–110, 138–142, 144–145,
149, 152–155, 159, E-25-1…6) is common to the five exit seats. Of these,
only **E-25-1** and **E-25-4** touch L-2, and both are handled above.
E-25-2 (Franks–Williams) is L-4's, E-25-3 (Jaeger) and E-25-6
(Reidemeister) are L-1's, E-25-5 (Rutherford) is L-3/L-4's; F-25-80…84,
108–110, 144–145, 152–155, 159 belong to L-1, L-3, L-4, L-5. No L-2 row is
left unaccounted for: the `grep` over the ledger named above returns nothing
else.
