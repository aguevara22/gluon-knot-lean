# L-5 on the EXIT frame SM6 — RECONCILIATION

Every ledger row of the L-5 class, judged **on SM6's bytes**, with the byte
that settles it. Verdicts are this seat's claims about what is printed, not
grades of anyone's work. Frame pin: `ACCESS_AUDIT.md`.

Legend — **addressed**: the repair is present at the anchor and does what the
row asked; **open**: still wrong or still missing on SM6; **lapsed**: the row's
premise no longer exists on SM6, so nothing is owed; **carried**: verified by an
earlier seat and not re-established here, named as carried.

---

## Part A — the rows named in this seat's charter

### F-25-72 — Gorsky's defects mis-described *(closed on SM2)*

**ADDRESSED on SM6.** sm-11:341–347 reads: "the Appendix carries an index slip
($P_s^{2k}$ for $P_s^{k}$) and is otherwise algebraically identical to his
Theorem 3.1; the genuine sign slip is in his Corollary 3.4, p. 11, outside the
Appendix; neither lies on this document's path."

At the bytes, Gorsky **p. 11**: (3.7) prints
$P^k_s(T_{n,n+1})=(-1)^kq^{k(k+1)}\frac{1}{[n-k]_{q^2}}\binom{n-1}{k}_{q^2}\binom{2n-k}{n+1}_{q^2}$,
and the next line prints "At the limit $q=1$ we have
$(-1)^{k-1}P^k_s(T_{n,n+1})=\dots$" — **the sign slip, at p. 11, outside the
Appendix: confirmed by this seat.** The Appendix index-slip half is **carried**
from the SM1/SM2 seats (Gorsky is a comparison source on SM6 and its Appendix
was not re-read this pass). "Neither lies on this document's path" is true:
Gorsky is cited only in the registry, at sm-11:346 and 348.

### F-25-73 — two undeclared convention traps *(closed at A5 on SM3)*

**ADDRESSED on SM6**, both halves, at `rem:torus-conventions` (sm-7:1698–1720):

- the bracket, clause (1): "his $[k]!$ in equation (9.6) and Theorem 9.7 is
  $\prod_{i=1}^{k}(1-q^i)$, not the $q$-integer factorial, which would be off
  by $(1-q)^{n-1}$" — **verified** against Jones's own Check 9.8, p. 359, and
  the discrepancy factor is right ($[k]!=[k]_q!(1-q)^k$ with $\beta+\gamma=n-1$).
  SM6 also prints the definition inside the theorem statement, sm-7:1430.
- the mirror, clause (2) — **verified** at DGR §2.3 ("For us, the standard
  $T_{a,b}$ has negative crossings"), BEM p. 1888 (their mirror transformation
  and $p_0^{K^*}(c^2)=p_0^K(c^{-2})$), and Gorsky Cor. 3.3 p. 11 (the $q=1$
  value $\frac{(-1)^{n-1}}{n}\binom{m-1}{n-1}$ at the **top** index $k=n-1$).

**New corroboration, from this pass:** the same non-standard bracket
$[k]!=(1-q)(1-q^2)\cdots(1-q^k)$ is printed in **Wenzl's 1985 thesis, p. 32** —
an independent published witness for clause (1). Not required; recorded as a
strengthening available to the author (see `RECOMMENDATION.md` O2).

### F-25-74 — four editorial items *(closed at A5 on SM3)*

**ADDRESSED on SM6**, all four:

| sub-item | SM6 byte | verdict |
|---|---|---|
| BEM listed flatly among "Sources" though (3.35) is unproved there | sm-11:348–350 "state the generating function without proof there (a cross-check only, exact for the whole $z^0$ row)" | **addressed**, and **verified at both editions**: BEM introduce (3.35) with "Using the above results, and performing various simple manipulations, we find the following expression" — no proof at the locator (arXiv v1, and published Ann. Henri Poincaré **p. 1888**) |
| DGR bib entry lacks the arXiv id | sm-refs.bib:17 `note={arXiv:math/0505662; the cited section numbering is that of arXiv v2}` | **addressed** |
| Jones (9.6)'s "$\alpha,\beta\ge0$" is a root misprint, not to be copied | `rem:torus-conventions`(3), sm-7:1714–1717; SM6's own display prints $\beta,\gamma\ge0$ at sm-7:1438–1439 | **addressed**, and the misprint **re-confirmed at Jones p. 359** by this seat |
| the SM1 sentence "enters no other proof" was false | sm-11:365–369, now "…derives the coefficient from Lemma `hsm:terminal` directly and enters no other proof: the triangle values that hypothesis (f) of Theorem `thm:uniqueness` needs are taken in the proof of Theorem `thm:comparison` from Lemma `lem:corner-values`(i) directly" | **addressed and verified this pass** — see F-25-12/F-25-145 below |

### F-25-75 — the corner slot is occupied *(closed on SM2, no source obligation)*

**ADDRESSED / no obligation.** `thm:C-star` (sm-7:1651–1697) computes
$c(K_r)=(-1)^{r-1}\mathrm{Cat}_r$ outright, so nonvanishing is internal, and
`rem:torus-conventions`'s closing sentence (sm-7:1717–1720) both records
$\min\deg_aH_{T(r,2r+1)}(a,0)=2-2r^2$ as the seat's report **and** says
"nothing in this document uses the nonvanishing". Nothing is owed to a source.

### F-25-97 — `hd:branching-blocks` displayed where $H_0$ is undefined

**ADDRESSED on SM6.** The display reads
$V_\lambda|_{H_{n-1}}=\bigoplus_{\mu\nearrow\lambda}V_\mu\ (|\lambda|=n\ge2)$
at **sm-7:652–656**, and the status line records the round-3 repair at
sm-7:664–666.

**Confirmed correct at the source, independently:** Wenzl's $H_n(q)$ has
generators $g_1,\dots,g_{n-1}$ (p. 361) and he never instantiates (2.5)/(2.6) at
$n=1$; SM6 defines $H_n$ "For $n\ge1$" (sm-7:617). $n\ge2$ is the right bound,
and every consumer I inspected has its base at size 1 or 2.

### F-25-108 — the containment sentence *(closed on SM4)*

**ADDRESSED on SM6, and re-verified at the bytes.** sm-11:357–367 now says the
supplied object is `hd:tableau-source`, consumed by `hd:complete`, `hd:hooks`
and `hd:trace`, hence by `hd:jones-torus`, `hsm:terminal`, `thm:C-star` and
`lit:torus`; and that `lit:torus` itself is consumed by no proof.

Both halves check:

- `DAG.md:309–311` lists exactly `hd:complete`, `hd:trace`, `hd:hooks` as
  consumers of `hd:tableau-source`; at the bytes the four edges are sm-7:718
  (`\ref`, `hd:complete`'s statement), 761 (`\eqref{hd:matrix}`), 1044
  (`\eqref{hd:branching-blocks}`, inside `hd:trace`'s proof) and 1174 (`\ref`,
  inside `hd:hooks`'s proof).
- no DAG row lists `lit:torus` as a parent, and `\ref{lit:torus}` occurs only at
  sm-11:318, 324, 363 (×2), 373, 845, 919 and sm-7:1701, 1712.

**One wording point, not a defect (see O4):** the parenthesis "(its reference
occurs only in this registry)" is slightly narrow — two of the references are in
`rem:torus-conventions`, sm-7:1701 and 1712. Neither is a proof, so the claim's
substance (no proof consumes it) stands.

### F-25-109 — cross-entry dependence and the thesis bib entry *(closed on SM4)*

**C7 (L-1 dependence): ADDRESSED and verified.** sm-11:369–376 states it, and
the bytes bear it out: the `bf:` preamble at **sm-7:398–406** names exactly
`lp:lm`, `lp:core`, `rp:record-polynomial` and `lp:split-circle`; and
`lit:torus`'s proof closes with "Theorem~\ref{lp:core} identifies its local $P$
with $H$" at **sm-7:1645–1646**.

**C8 (thesis bib entry): the entry is PRESENT — and it now contradicts the
registry.** `sm-refs.bib:57` reads
`@phdthesis{WenzlThesis, … note={UMI 8603724; the copy on file was consulted for its title pages only}}`,
while sm-11:331–334 lists "the generating-series notation of Wenzl's 1985
thesis" among "the sources' normalization defects" and says those defects "are
disclosed at Literature input `hd:tableau-source`".

**Three separate problems, all new on SM6 and all raised here as conditions
C1–C3 of `RECOMMENDATION.md`:**

1. the thesis is **not** disclosed at `hd:tableau-source` — `WenzlThesis` and
   the word "thesis" occur nowhere in `sm-7-anchors.tex`; the disclosure
   paragraph (sm-7:667–674) names only p. 365 and (3.6);
2. calling it a **"normalization defect"** mis-describes the source — I read
   thesis p. 32 and it is a *different presentation*, internally consistent
   (see `T1_STATEMENT.md` §5), not a misprint. This is the same class of error
   F-25-72 was;
3. the bib note ("consulted for its title pages only") and the registry's
   substantive claim about the thesis's notation **cannot both be the record**.
   The note is accurate for the author's own consultation
   (`phase25/LITERATURE.md`, 2026-09-05T19:29:30Z, "author (round 3) — Wenzl
   1985 thesis, title pages (DEPTH: identification only)"), which makes the
   registry clause the one to fix.

"on file and consumed by nothing" is **true**: `WenzlThesis` occurs only at
sm-11:333 and sm-refs.bib:57.

### F-25-149 — `hsm:notation`'s locator *(closed on SM6)*

**ADDRESSED, verified at both ends.** SM6's status line (sm-7:380) cites RC
`p12:source-evaluation` "(torus_dictionary: the definition
$P_J(D;t,x)=P_D(t^{-1},x)$, the unknot value and the UNDER-first
initialization) and RC braid_finite for its use".

- At `phase198/manuscript/RC_v4/torus_dictionary.tex:50–61` the lemma
  `p12:source-evaluation` **does** carry $P_{J,D}(t,x)=P_D(t^{-1},x)$, and its
  proof (:85–90) carries the skein $t^{-1}P_{J,+}-tP_{J,-}=xP_{J,0}$ and the
  UNDER-first value $((t^{-1}-t)/x)^{b-1}$.
- `braid_finite.tex:189` reads "For the Jones notation of
  Lemma~\ref{p12:source-evaluation}, the last …" — it **defers**, exactly as the
  row said. The superseded locator did not carry the statement; the new one
  does.
- The DAG edge the row also asked for is present: `DAG.md:231` lists
  `hsm:notation`'s parents as `lp:core`, `lp:split-circle`,
  `rp:record-polynomial`, and the proof cites `lp:split-circle` at sm-7:391–393.

**Source-side note this seat adds (not a defect):** the new locator is an
**internal** RC document, not a published source. `hsm:notation` consumes **no
L-5 literature** — it is an L-1-backed change of variables into Jones's letters,
whose published counterpart (Jones Prop. 6.2, p. 348) SM6 cross-checks in
`rem:torus-conventions` and does not import. Worth stating explicitly in the
registry (see O1).

### F-25-158 — a directive inside `hsm:terminal`'s statement *(closed on SM6)*

**ADDRESSED, verified.** The statement block (sm-7:1493–1503) now carries only
hypothesis and conclusion; "Use the normalized positive-braid
formula~\eqref{hd:jones-formula} of Theorem~\ref{hd:jones-torus} for this
diagram…" is the **first sentence of the proof**, sm-7:1505–1507, and the status
line records the move at sm-7:1502.

### F-25-159 — `lit:torus`'s locator *(closed on SM6)*

**ADDRESSED, verified at the RC bytes on both sides.**

- The new locator carries the statement: RC `an:bem-catalan`,
  `d7_anchors.tex:199–205`, display `an:torus-coefficient`
  $[a^{2-2r^2}z^0]P_{T(r,2r+1)}(a,z)=(-1)^{r-1}\mathrm{Cat}_r$.
- The old locator does **not**: RC `hd:section` (`d9b_hecke.tex`) closes with
  "The campaign mirror $c=a^{-1}$, $z_B=-z$ and Catalan extraction remain the
  separate internal proof of Lemma~\ref{an:bem-catalan}" (:1199–1201).
- "whose exponent and Catalan steps this proof reprints" is accurate: RC prints
  $2-2r^2$ at `an:terminal-degree` (:251–253) and the three-step Catalan chain
  at `an:terminal-coefficient` (:255–260); SM6 reprints both at sm-7:1630–1633
  and 1635–1641.
- The route difference is real: RC reaches it **through the mirror and the BEM
  row** (`d7_anchors.tex:207–228`), SM6 through `hsm:terminal` on the positive
  closure, with "No mirror of the knot or change of writhe is made"
  (sm-7:1518).

---

## Part B — the other L-5-touching rows

### F-25-12 and F-25-145 — the downstream-consumer sentences

**ADDRESSED on SM6, and verified this pass** (the SM2 seat left this
unverified; I read the bytes):

- `thm:comparison`'s proof discharges hypothesis (f) with "**(f)
  Lemma~\ref{lem:corner-values}(i)** gives corner coefficient $1$ for either
  oriented triangle" — `sm-6-comparison.tex:306–307`
  (`9709df2eab4ab68b92b4394123746e2db19e1a252f40a8a228aa82eb28d788ef`).
  `\ref{thm:C-star}` does **not** occur in `sm-6-comparison.tex`.
- Frame-wide, `\ref{thm:C-star}` occurs at sm-7:1701 (inside
  `rem:torus-conventions`, prose) and sm-11:362, 365, 849, 874 (registry prose).
  **No proof consumes `thm:C-star`.** The registry sentence at sm-11:365–366 is
  therefore true.

### F-25-103 — `hsm:notation`'s unquantified inheritance clause *(closed on SM5)*

**ADDRESSED on SM6.** sm-7:373–379 enumerates them: planar isotopy, the three
Reidemeister moves and the value 1 on the crossing-free circle (`lp:core`); the
split-union rule (`lp:split-circle`); the displayed skein; and the full
named-record equality (`rp:record-polynomial`). A consumer can now tell what it
may use.

---

## Part C — escalations

**E-25-1 … E-25-6: none is an L-5 item, and this seat files no new one.**

| escalation | bearing on L-5 |
|---|---|
| E-25-1 Roseman 2000 | L-2 |
| E-25-2 Franks–Williams | L-4 |
| E-25-3 Jaeger | L-1, already recorded LAPSED |
| E-25-4 Kneser 1926 | L-2 |
| E-25-5 Rutherford IMRN | L-3/L-4 |
| E-25-6 Reidemeister's theorem at proof depth | L-1; it reaches L-5 only through the shared L-1 dependence (`lp:core` ← `lit:homfly`), and is L-1's row to carry |

**Every published locator SM6 cites for L-5 was found and read at the printed
page this pass.** Nothing is blocked; nothing is dismissed for fetchability.
