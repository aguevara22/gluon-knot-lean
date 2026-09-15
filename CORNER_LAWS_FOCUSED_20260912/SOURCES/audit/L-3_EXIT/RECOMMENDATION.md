# L-3 EXIT — RECOMMENDATION

Registry entry **L-3** (`reg:etnyre`), literature input `src:contact`, on the
**exit frame SM6** (manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`, `shasum -c`
**20/20 OK**, verified before anything was read). Cold seat `source L-3 EXIT`,
charter `phase25/evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`.
Stamp 2026-09-06T01:56:31Z. Evidence: `ACCESS_AUDIT.md`, `CONSUMPTION_MAP.md`,
`T1_STATEMENT.md`, `T2_DELTA.md`, `RECONCILIATION.md`, artefacts in `work/`.

---

## 0. Verdict

> ## **KEEP AT T2.**
>
> All five clauses SM6 consumes from L-3 have a T2 witness **at a page SM6
> prints**, and this seat read each of those pages and each of those proofs.

| clause consumed | witness SM6 prints | depth this seat reached |
|---|---|---|
| $r=(D-U)/2$ | Etnyre eq. (5), §2.6.2, **p. 14** | **T2** — printed argument read |
| $tb=w-(D+U)/2$ | **Geiges book Prop. 3.5.9, p. 117** | **T2** — printed proof read; chain (Prop. 3.4.14 p. 113 with its proof, Defs 3.5.1/3.5.4 pp. 114–115, Ex. 3.5.8 p. 116) followed to completion |
| $sl(T_+(L))=tb(L)-r(L)$ | Etnyre Lemma 2.22, eq. (17), §2.9, **p. 19** | **T2** — full printed proof read |
| $sl=$ front writhe, on `def:transverse-front` | **Geiges book Prop. 3.5.32, p. 127** and **survey §3.1 Lemma 3.3, p. 46** | **T2** — both printed proofs read; every reduction lands on disk |
| $sl_{\rm SM}$ (the $\partial_y$ pushoff) $=$ the literature's $sl$ | Etnyre §§2.6.3–2.6.4, **p. 15**; Geiges survey Def. 3.2 and following ¶, **p. 45** | **T2** — the independence argument is printed at p. 45 and was read |

**This is the specific thing the SM2 seat said was missing.** On SM2 three of
these five had no T2 witness among the sources SM2 cited for them (F-25-80,
F-25-81). On SM6 all three do, and the citations are exact at the bytes.

**No item is below T2. Nothing is missing.** There is therefore no "exact
missing item" to name under the charter's "below T2" branch.

## 0.1 The confirmation registry L-3 asks for, given

Registry L-3 (sm-11:186–191) records the Legendrian-$tb$ chain as "read by the
Codex bench, 15:55Z, **pending the seat's confirmation**; ruling R-25-20(3)".

> **This seat confirms it.** Geiges book **Prop. 3.5.9 is on printed p. 117**
> and reads $\mathtt{tb}(K)=\mathrm{writhe}(K_F)-\tfrac12\#(\mathrm{cusps}(K_F))$
> (verified on the rendered page at 4×, not only in the text layer); its proof
> is printed there and was read; its chain resolves — Prop. 3.4.14 statement
> p. 113 with its proof completing on p. 114, Def. 3.5.1 p. 114, Def. 3.5.4
> p. 115, Ex. 3.5.8 p. 116 — all inside the cited span pp. 111–117.

The registry may drop the "pending" clause. Detail in `T2_DELTA.md` §1.

## 0.2 Deflation, said plainly

"T2" here means: the statement is at the cited locator, and the source's
**printed proof** was read and its reductions followed. It does **not** mean the
campaign has an independent proof of any of these, and it does **not** upgrade
Etnyre eq. (9), which stays what SM6 itself calls it — a source that "states
it". Three picture-level steps inside otherwise complete printed proofs are
asserted rather than computed (`T2_DELTA.md` §4); **this seat printed no
substitute for any of them** (rule 8). The verdict is a claim about depth of
reading, not a clearance of `fd:contact`, which remains **held by bench A**.

---

## 1. One finding for the ledger

### **O1 — the identification is placed correctly but invoked nowhere.** (medium; structural, not source-depth)

`rem:sl-convention` (sm-3:3010–3021) is the block that identifies the frame's
own $sl(T)=\ell(T,T+\epsilon\partial_y)$ — defined at
\eqref{fd:framed-linking}, inside `fd:linking-calculus` — with **the
literature's** self-linking number, and it carries the two citations that
license it. It is exactly where round 3 put it (F-25-81) and its citations are
exact (`T1_STATEMENT.md` rows 6 and 11).

**But no proof and no statement in the frame references it.**
`\ref{rem:sl-convention}` occurs five times: sm-3:2823 (a `\status` line) and
sm-11:193, 223, 548, 872 (registry prose and a table). In particular, the proof
of `fd:contact` — the **sole** consumer of `src:contact` (DAG.md:304) — makes
the crossing at sm-3:3438–3439:

> Summing the source transverse-front writhe formula proves
> \eqref{fd:front-writhe}.

\eqref{fd:front-writhe} is a statement about the **SM's** $sl(T)$; "the source
transverse-front writhe formula" is a statement about the **source's**. The
step from one to the other is precisely `rem:sl-convention`, and it is not
cited there. The frame's own instrument cannot see this: a remark referenced
by no proof is not an orphan under the ruler's gates, and the DAG's literature
column for `rem:sl-convention` is empty.

**Severity, deflated.** This is **not** a source-depth deficiency and does not
put L-3 below T2 — the warrant exists, is printed, and is at T2. It is a
citation-chain gap of the same class the campaign has been closing all phase
(F-25-153 was its twin on the L-4 side: a lemma applied through a bare display
instead of by label). `fd:contact` is a **held** item, so this belongs to the
referee lane as much as to the source lane.

**Repair (one clause, no mathematics).** In `fd:contact`'s proof, at
sm-3:3438–3439, cite the remark by label — e.g. "Summing the source
transverse-front writhe formula, whose $sl$ is the number of
\eqref{fd:framed-linking} by Remark~\ref{rem:sl-convention}, proves
\eqref{fd:front-writhe}." Equivalently, add the `\ref` inside `src:contact`
at the front-writhe clause. Either makes the warrant visible to the instrument.

---

## 2. Four observations — recorded, no repair demanded

**O2 — `src:contact` cites two results proved in the other contact convention,
with no pointer at the site.** (low, editorial) The block opens by fixing
$\ker(dz-y\,dx)$ (sm-3:3340) and then cites Geiges book Prop. 3.5.9 and
Prop. 3.5.32, both proved in $\ker(dZ+X\,dY)$ with the front page $(Y,Z)$
(book Def. 3.2.2, p. 96, and p. 96's $\alpha_{st}=dz+x\,dy$, both read). The
transport is printed — at sm-3:2373–2375, 966 lines earlier, and in full in
registry L-3 — but the block carries no cross-reference to it. Likewise
`rem:sl-convention` writes "$\partial_X$" and "$(X,Y,Z)=(-y,x,z)$" without
saying, at that site, that the capitals are Geiges's letters (the survey at
p. 45 writes them lower case). **The composition is valid** — I re-derived
$\Phi^*(dZ+X\,dY)=dz-y\,dx$, $\det\Phi=+1$, $\partial_X=-\partial_y$, the front
page and the over/under correspondence (`T1_STATEMENT.md` §3) — so this is
readability, not correctness. Optional one-clause fix: a `\ref` from
`src:contact` to the provenance paragraph.

**O3 — F-25-83's "page-precise Etnyre locators inside `src:contact`": the
locators are section- and equation-precise, without page numbers.** (low)
`\cite[Sections~2.1 and~2.4]{Etnyre}` and `\cite[Section~2.6.2, equations~(5)
and~(7); Section~2.6.4, equation~(9); Section~2.9, Lemma~2.22,
equation~(17)]{Etnyre}` carry no pages; a page appears only in
`rem:sl-convention` ("p. 15") and on the Geiges citations. All six resolve at
the bytes (pp. 4, 10, 14, 14, 15, 19), so nothing is unfindable, and an
equation number is arguably tighter than a page. The row is ruled **closed on
SM4**; this is recorded as a factual note, **not a reopening**, for the
curator's judgement.

**O4 — one uncited comparative sentence remains inside a held statement.**
(low) `fd:linking-calculus`'s statement still ends its mixed-crossing paragraph
with "Thus it has exactly the linking normalization used in the source's front
calculations" (sm-3:2803–2804), a comparison with the literature carrying no
citation, inside a statement environment. It concerns the *normalization* of
$\ell$ (that it is the ordinary linking number), which the lemma proves for
itself, so it is weaker than the identification F-25-81 moved out. Bench A owns
the placement question on this held item.

**O5 — two positive records.**
(i) The Geiges *survey* Lemma 3.3's single external reduction is to
**[98] = N. Saveliev, *Lectures on the Topology of 3–Manifolds*, de Gruyter
1999** (verified in the survey's bibliography, p. 85), which is **not on disk**.
It is **not an escalation**: the fact it is cited for is proved on disk, with a
complete printed proof, at **Geiges book Prop. 3.4.14, p. 113** — a citation
SM6 already carries. Registry L-3's parenthetical "one reduction … to a book
not on disk" now describes a *redundancy*, and could say so.
(ii) **Two T2 witnesses are available on disk for the two clauses that still
rest on Etnyre alone**, and SM6 cites neither: **Geiges book Prop. 3.5.19,
p. 121** (proof p. 122, read) gives $\mathrm{rot}(K)=\tfrac12(c_--c_+)$ =
Etnyre eq. (5); **Prop. 3.5.36, pp. 128–129** (proof read) gives
$\mathtt{sl}(K_\pm,\Sigma)=\mathtt{tb}(K)\mp\mathrm{rot}(K,[\Sigma])$ =
Etnyre Lemma 2.22. **Not recommended as repairs** — both Etnyre locators
already reach T2, and Prop. 3.5.19's sign convention (coorientation by
$\partial_z$; trivialisation $e_1=\partial_X$, $e_2=\partial_Y-X\partial_Z$)
would need its own transport line. Recorded so a later round has the option.

---

## 3. Conditions from the earlier seats — all four taken

| condition | origin | status on SM6 |
|---|---|---|
| **C1** print the contact conventions and the dictionary | SM1 L-3 seat | **taken.** `src:contact` sm-3:3340–3343; transport sm-3:2373–2375 and registry L-3 sm-11:202–211; the SM1 two-form composition is dissolved |
| **C2** separate the transverse **lift** from the L-3 citation | SM1 L-3 seat (F-25-57) | **taken.** `cf:thm-carrierfloor`(C) constructs it: "We now construct the transverse lift rather than import a front criterion" (sm-3:4452–4453) |
| **C3** Geiges primary, with the page and "printed proof"; Etnyre demoted | SM1 L-3 seat (F-25-58, reversed on SM2 by F-25-80) | **taken.** sm-3:3356–3361 |
| **C4** strike L-3 from "replace by the available T3 proof" | SM1 L-3 seat | **taken.** No such text in SM6 (grep). R-25-13 wording is present and correct at sm-11:232–236, and "T3" never appears as a claim for L-3 |

## 4. What this seat did **not** do

Did not referee any proof of the frame — `fd:contact`, `fd:linking-calculus`,
`fd:generic-front` and `cf:thm-carrierfloor` are **held by bench A** and nothing
here clears them. Did not audit L-1, L-2, L-4 or L-5, beyond checking at the
ledger bytes that their rows are not L-3's. Did not re-verify F-25-85's
comparison-source corroborations in full (they concern comparison sources, not
L-3 premises); they stand as the SM2 seat's claims. Did not open an escalation.
No advisor call, no GCP instance, no network fetch. No frame byte, no other
lane, `NEWSM/`, `informal draft/` v7 file, `challenge/sealed/` or `.env` read or
written.
