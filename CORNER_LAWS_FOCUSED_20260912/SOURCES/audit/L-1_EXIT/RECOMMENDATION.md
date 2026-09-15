# L-1 EXIT — RECOMMENDATION

Cold source seat `source L-1 EXIT`, Phase 2.5 exit-frame source pass.
Audited object: **frame SM6**, `phase25/frames/SM6/`, manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`,
`shasum -a 256 -c` run from inside the frame **before any reading**: 20/20 OK.
Evidence: `ACCESS_AUDIT.md`, `CONSUMPTION_MAP.md`, `T1_STATEMENT.md`,
`T2_DELTA.md`, `RECONCILIATION.md`, `work/`.

This is the **source side**. Nothing here is a referee acceptance, a bench
grade, or a statement that any printed proof of SM6 is correct. Bench A's holds
are untouched and cleared by nothing in this lane.

---

## 1. VERDICT

**L-1 is BELOW T2 on SM6 — for exactly two items, both bounded, one of which
the frame already prints as open.**

Per statement:

| statement | depth reached | root |
|---|---|---|
| `lp:lm`, ten clauses | **T2** | LM §1, pp. 111–120; Props 1, 2, 4, 6 and the Recursive Definition. Two residues in LM's Prop. 6(n) named by the SM2 seat remain, and are now **closable against a second on-disk printed proof** (Lickorish GTM 175 pp. 171–172) |
| `lit:homfly` (b) Reidemeister and planar invariance, (c) unknot value, (d) skein | **T2** | LM Prop. 4(n) p. 115 (proof pp. 115–117); formulas (II) and (I), p. 113 |
| `lit:homfly` (a) existence **over `Z[a^±1,z^±1]`** | **below T1 at its cited locators** | LM's Theorem is over `Z[l^±1,m^±1]`. The ring is one citation away at T2 in the same source — **MISSING ITEM 1** |
| `lit:homfly` (e) descent | **below T2** | LM p. 120 states it; it imports **Reidemeister's theorem**, with no printed proof on file — **MISSING ITEM 2 = E-25-6** |
| `lp:lm-uniqueness`, source-ring form on links | **T2, strengthened this pass** | LM p. 120 **and** Lickorish GTM 175 Thm 15.2, p. 168, with a **complete printed proof pp. 168–172** whose uniqueness paragraph (p. 172) writes out the step LM compress |
| `lp:lm-uniqueness`, the **diagram-level** form SM6 states | **below T2** | its bridging sentence converts R-move invariance into isotopy-class dependence **by Reidemeister's theorem** — again MISSING ITEM 2 |
| `lp:coefficient-transport` | **campaign step, rule 8; verified a third time here** | no source prints it; it inherits the Reidemeister dependency through `lp:lm-uniqueness` |
| registry entry L-1, every locator | **all resolve; all say what the entry says** | see `CONSUMPTION_MAP.md` §C |

**Deflate, plainly.** L-1 being below T2 is **not a regression and not a
concealed defect**: the frame prints the reason itself at `sm-11:47–50` and
`sm-11:900–901`. Rounds 2–5 did close everything F-25-53, 54, 55, 56, 110 and
131 asked for, verified at the bytes in `RECONCILIATION.md`. What is left is one
registered input whose proof is not on file, and one citation.

**Blast radius, stated so it is not over-read.** `lp:core` carries 67 `\ref`s and
`lit:homfly` 33; the identification `P = H` is on the main chain through
`thm:floor` and `thm:comparison`. So MISSING ITEM 2 is load-bearing frame-wide —
but it is load-bearing as a **classical, universally accepted theorem whose
statement is on file and whose proof is not**, which is a very different thing
from an unsupported step. Do not report L-1 as "unsourced".

---

## 2. MISSING ITEM 1 — the ring of `lit:homfly` (new this pass)

**The finding.** `lit:homfly` (`sm-3:917–918`) asserts a map into
`Z[a^±1,z^±1]`. Its status line (`sm-3:922`) cites LM *Theorem, pp. 112–113;
proof pp. 113–120; isotopy-class descent p. 120*. **At all three locators the
theorem is over `Z[l^±1,m^±1]`.** Under `l = ia, m = −iz` a monomial `l^j m^k`
picks up `i^j(−i)^k`, which is a rational integer **iff `j ≡ k (mod 2)`** and is
`±i` otherwise (verified exhaustively for `−8 ≤ j,k ≤ 8`, with the opposite-parity
negative control, `work/checks.py` C1a/C1b). So integrality in the campaign ring
is a **further fact**, and it is consumed: `lp:core`'s identification paragraph
(`sm-3:1164–1177`) needs `H` to be `R`-valued in order to be one of the two maps
`lp:coefficient-transport` identifies, at **every** component count.

**Why this is not circular and not serious.** `lp:core` proves the same
integrality for `P` by its own `M_c` induction. Nothing is assumed twice and
nothing is assumed falsely. The defect is a **citation defect**: the clause is
true, is at T2, and is in a source the entry already cites — just at a locator
the status line does not name and at a scope the registry does not reach.

**The repair — one citation, no new mathematics.**

> **C1 (must).** On `lit:homfly`'s status line, add to the existing LM locators:
> *the coefficient ring under `l = ia`, `m = −iz` from LM property (1), p. 110,
> proved as their Proposition 22 (statement p. 133, proof pp. 133–134), whose
> parity clause holds at every component count*. And at `sm-11:59–66`, widen the
> Prop. 22 sentence, which currently reads the clause only "at one component", to
> say that the same proposition supplies the campaign ring for all `c` and the
> `c = 1` strengthening in addition.

**C2 (should, and cheap).** `sm-11:71–75` already records Chmutov–Polyak
[eq. (1) and Remarks 1–2] as printing the campaign normalization verbatim. I
verified both at the bytes: CP **p. 1 eq. (1)** prints the ring, the skein
`aP_+ − a^{-1}P_- = zP_0`, the unknot value and the unlink value `δ^{k-1}`; CP
**p. 3 Remarks 1–2** print the `a`/`z` parity by component count and the lowest
`z`-power `1−k`. That is MISSING ITEM 1's content **in the campaign's own
variables**. Keep it exactly where it is — as corroboration — because CP rest
existence on `[HOM, PT]` and the parity on `[Ja, Proposition 2]`, unprinted and
not on disk (E-25-3). Adding a page number (`p. 3`) to the Remarks citation is
the whole change.

---

## 3. What this pass strengthens, at no cost to the frame

> **C3 (should).** Cite **Lickorish GTM 175, Theorem 15.2, p. 168, with its proof
> pp. 168–172**, at `lp:lm-uniqueness` and at `lp:lm` — not merely as "the same
> statement" (`sm-11:37`), but as a **second complete printed proof**.

Three things follow from GTM's proof, all read at the bytes this pass:

1. **The one compression the SM2 seat could not close in LM is closed.** LM's p. 120 uniqueness asserts the propagation step without writing it out; GTM p. 172 writes the uniqueness argument out in full. Two independent published proofs, both on disk.
2. **`lp:lm`'s level bookkeeping is published.** `lp:lm` (`sm-3:953–956`) currently states as the campaign's own reading that one takes the maximum of the finitely many crossing counts and applies source Prop. 4 at that level. **GTM p. 172 prints exactly that inference.** Under rule 8, a published sentence beats a campaign reading; cite it.
3. **The two residues in LM Prop. 6(n)** — the asserted selection of the disc, and the basepoint/ascending-witness compatibility (`T2_DELTA.md` §4) — are covered by GTM pp. 171 through a different, **constructive** route (innermost loop, innermost 2-gon, the 3-gon of Lemma 15.1 proved on p. 167, Type III across the 3-gon, Type II removal), with the basepoint placement justified in the same paragraph. I read GTM pp. 171–172 and checked that it covers both; I did **not** merge it against LM's own figures, so this is a **route**, not a completed discharge.

Two wording items, recorded, neither filed as a finding:

- `sm-11:37` says GTM Thm 15.2 is "the same statement" as LM p. 120's uniqueness. GTM 15.2 quantifies over functions on **oriented links**; LM p. 120 and `lp:lm-uniqueness` quantify over functions on **diagrams**. They coincide only after the descent the bridging sentence supplies. One clause would fix it.
- `sm-11:34` says "pp. 107–110 are their Section 0". Printed p. 111 carries both the tail of §0's property list and the §1 header (page render `work/lm-05.png`). No consumer is affected.

**A published cross-check for the rule-8 flag, found this pass.** LM
**Prop. 10(ii)**, p. 123, gives the obverse through the involution fixing `m` and
swapping `l ↔ l^{-1}`, i.e. `(a,z) ↦ (−a^{-1}, z)` after `φ`. SM6's mirror
paragraph (`sm-3:4528–4553`) derives `P_{D̄}(a,z) = P_D(a^{-1}, −z)` internally,
using `ι: (a,z) ↦ (a^{-1}, −z)` defined at `sm-3:4537`. **The two agree on exactly the monomials with
`p ≡ q (mod 2)` and disagree off that locus** — and that parity is precisely LM
Prop. 22. Verified exhaustively with the off-locus disagreement as a negative
control (`work/checks.py` C2/C2b). So the frame's internally derived mirror and
LM's printed symmetry are **consistent**. This is a corroboration of the
transport chain against a printed LM proposition; it is **not** a proof of
`lp:coefficient-transport`, and the rule-8 flag at `sm-3:991` and `sm-11:878`
**stays**.

---

## 4. Reidemeister's theorem at proof depth — what is on file after E-25-6

**Answer to the charter's standing question, in three parts.**

**(a) What the frame says is right.** `sm-11:41–50` registers the theorem with
three locators, grades it below T2 at every on-file locator, and calls it an open
source item for the operator under rule 7, not a dismissal. `sm-11:900–901` lists
it as not repaired and recorded open. **This seat endorses that disclosure
without qualification.** It is the correct handling of rule 7.

**(b) The statement on file is weaker than the registry's own description.**
Lickorish GTM p. 3 states the direction L-1 needs, prefaced *"With a little
careful thought"*. But GTM **p. 2** additionally declares its own input assumed:
the triangle-move characterisation of link equivalence is introduced with *"This
result will be assumed"*, with the proof pointed to reference **[17]**, which the
GTM reference list resolves to **Burde–Zieschang, *Knots*, de Gruyter (1986)**.
So the on-file statement lacks a proof **and** rests on an explicitly assumed
prerequisite.

**(c) E-25-6's premise "neither on disk" is stale, and the escalation must be
restated rather than repeated.** Before relaying any unfetchability I searched
the whole campaign folder. Inside it, in a Phase 1.98 evidence lane, are (hashes
in `ACCESS_AUDIT.md`):

- Reidemeister, *Knot Theory* — **1983 English translation of the 1932 *Knotentheorie***, `phase198/evidence/codex/rc2_reidemeister_depth_author_v1/source/reidemeister_1932_english.pdf`
- **Burde–Zieschang–Heusener, *Knots* 3e** — publisher preview Ch. 1 §§A–C, same lane; and a fuller copy at `phase198/evidence/codex/rc2_tame_category_source_author_v1/burde_zieschang_heusener_3ed.pdf`
- **Alexander–Briggs 1927**, same lane
- **Queffelec 2024**, a transversality proof of Reidemeister's theorem, same lane

**I did not read any of them at proof depth**, and I claim nothing about whether
they close the theorem. The Phase 1.98 lane that did read them reported that they
do **not** close it on the manuscript's declared topological/PL domain (its own
`REPORT.md`: "no safe depth-only integration found"; "Do not integrate this
package as positive evidence"; BZH defers topological/PL equivalence to a
corollary absent from the preview). Phase 1.98 is frozen and confers no positive
status; I cite it only as evidence of what is on disk and which routes were
walked.

> **C4 (escalation to the operator, by name).** E-25-6 stands. Restate it as:
> *the texts are on disk; what is missing is a printed proof of Reidemeister's
> theorem **in a category the manuscript's use actually needs**.* The narrower
> question, which is the one a T2 reading would have to answer, is:
>
> **SM6 consumes only the direction "equivalent oriented links ⟹ their diagrams
> are related by a finite sequence of Reidemeister moves and an
> orientation-preserving plane homeomorphism", with NO bound on the crossing
> number along the sequence** (verified: `lp:lm-uniqueness`'s bridging sentence,
> `sm-3:971–976`, and `sm-4:29–34`; the frame explicitly declines LM's bounded
> p. 120 form at `sm-3:957–958`). The operator's hunt should therefore be for a
> **printed proof of the unbounded PL statement**, for which the named candidate
> is **Burde–Zieschang, *Knots*, de Gruyter (1986), Chapter 1** — Lickorish's own
> [17] — in a copy that carries the chapter beyond the publisher preview.
>
> This is a **narrower and cheaper** request than E-25-6 as filed, and it should
> replace it. Nothing is dismissed; the goal stays paused where the standard
> says it pauses.

**Not recommended: a bench proof.** Rule 8 is explicit and the order is fixed.
There is a structurally available internal route (the campaign already proves an
initialization-based uniqueness in `lp:core` that needs no isotopy hypothesis,
and Lickorish GTM pp. 171 constructs the ascending-diagram reductions by explicit
moves), but **this seat neither walked it nor recommends it**, and states plainly
that it has not checked whether it works. Fetch first; the operator hunts; only
then, and flagged.

---

## 5. LM Propositions 8, 9, 10, 22 as chain-shortening citations

**Answer: they shorten the campaign's chain and lengthen the source reading, and
they remove no premise. SM6's current posture is correct — do not change it.**

Read at proof depth this pass (`T2_DELTA.md` §1): Props 8, 9 and 10 are all
proved in LM §2 from the linear-skein module `L(P)`, whose **free** generation by
the unknot class (p. 121) rests on §1's main theorem **including its uniqueness
clause**; and Prop. 22's own proof (pp. 133–134) invokes **Prop. 8** in its
separated-union branch. So the whole family sits strictly **above** what L-1
already imports. Citing them adds LM pp. 120–123 to the T2 reading burden.

Two concrete calls:

- **`lem:homflyrows`** — `sm-11:106–109` records it as available whole from Props 9, 8 and 22 at two components and keeps the printed proof. I checked the `c = 2` row of Prop. 22 against the lemma's third formula and they match under the substitution. **Keep as recorded.** If it is ever switched to the citation, LM §2 comes with it, and that should be a deliberate decision, not a simplification.
- **`cf:thm-carrierfloor(R)`** — Prop. 10(i) is about **links**; clause (R) is stated and proved **at the diagram level**, and the diagram-level form is what `prop:C-reversal` consumes. `sm-11:99–100` records Prop. 10(i) as available-not-consumed. **That is the right call and should stand.** On the source side this pass agrees with the withdrawal recorded in R-25-34.

> **C5 (should).** Where the registry describes these as routes "available whole",
> add the cost in one clause — that they rest on LM §2's linear skein, which rests
> on the main theorem the entry already imports — so that no later round reads
> "available whole" as "cheaper".

---

## 6. Escalations to the operator

1. **E-25-6, restated** — see C4. The one item keeping L-1 below T2. A named, narrower request: a printed proof of the **unbounded PL** Reidemeister statement; named candidate **Burde–Zieschang, *Knots*, de Gruyter (1986), Ch. 1**, beyond the on-disk preview.
2. **E-25-3 (Jaeger 1990)** — stays **conditional and lapsed**; nothing in SM6 consumes Chmutov–Polyak. Worth a hunt only if the operator wants the ring and the knot clause rooted in the campaign's own variables rather than transported from LM.
3. **E-25-1 (Roseman 2000)** — correctly attributed to this entry's global-Reidemeister route at `sm-11:112–115`; stands with the operator; blocks nothing here; no fetch attempted this pass.

No source was dismissed for fetchability. No bench proof is proposed or endorsed.

---

## 7. What this seat did not do

Refereed no printed proof of SM6 and cleared no bench-A hold. Wrote no proof of
anything. Did not re-read LM Props 1, 2, 5, 6 in full, any LM figure, or
Przytycki–Traczyk — those rows are marked `[carried]` with the lane and hash.
Did not open Reidemeister 1932, Burde–Zieschang–Heusener, Alexander–Briggs or
Queffelec at proof depth. Did not run the frame's instruments; where `DAG.md` is
quoted it was checked against my own `\ref` sweep, not re-executed. Did not
touch any frame, any other lane, `NEWSM/`, `informal draft/`, any `v7` letter
file, `.env` or `challenge/sealed/`. Called no advisor. Created no GCP instance.
No network request of any kind was made this pass.
