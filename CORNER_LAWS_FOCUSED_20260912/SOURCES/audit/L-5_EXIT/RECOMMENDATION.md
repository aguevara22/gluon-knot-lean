# L-5 on the EXIT frame SM6 — RECOMMENDATION

Seat: `source L-5 EXIT`, cold, on frame **SM6**
(`FRAMED_MANIFEST_SM6.sha256` = `38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`,
20/20 verified before reading). Verdicts are **this seat's claims about what is
printed**, not statuses. Everything below is on SM6's bytes.

---

## VERDICT

> **KEEP L-5 AT T2.**
>
> The entry's single retained published premise, Literature input
> `hd:tableau-source` (sm-7:640–674), is at **T2 on all four of its clauses**:
> each is verified word for word at the printed Wenzl page, and each source
> proof was read and checked to establish it, with every compression named and
> closed. The Jones locators are at **T1 exact**, which is the required depth
> because on SM6 Jones is a cross-check and not a premise. **No source is
> blocked and no escalation is filed.**
>
> **Nothing is missing that would put the entry below T2.** Three conditions
> follow, all **registry/bibliography editorial** and all about one sentence —
> the 1985-thesis clause. They are the same class of defect as F-25-72 (a
> source's defect mis-described), which is why they are marked *must*, not
> because a premise is unsupported.

**What must not be reported.** Not "L-5 is proved". Not "the torus route is
source-free". The route rests on four external statements of Wenzl §2 at T2,
on L-1 through `lp:core`/`lp:lm`/`rp:record-polynomial`/`lp:split-circle`, and
on the global premise `lit:homfly` through `lp:core`; and the printed section is
tagged **transcribed (unrefereed)** at `hsm:notation`, `hd:jones-torus`,
`hsm:terminal` and `lit:torus` — proof-side refereeing is bench A's lane and
nothing here clears it.

---

## Depth reached, per statement consumed

| statement | depth | root, at the printed page |
|---|---|---|
| `hd:tableau-source` **W-1** the tableau matrices, content-difference convention, nonnegative root, zero off-diagonal at a forbidden swap | **T2** | Wenzl **(2.3), (2.4), p. 363**; relations (H3)/(H2) p. 363 and (H1) p. 364; positivity **Lemma 2.1(iii),(iv), p. 362**; hypothesis $n$-regular p. 363 |
| **W-2** the literal branching, one block per removable box, $n\ge2$ | **T2** | Wenzl **(2.5), (2.6), p. 364**, via the printed bijection $t\mapsto t'$ |
| **W-3** nonzero content difference for entries differing by $\le2$ | **T2** | Wenzl **Lemma 2.11(a), p. 371**; proof p. 372 with Fig. 1, followed and closed |
| **W-4** distinct size-$n\ge3$ partitions have distinct predecessor sets | **T2** | Wenzl **Lemma 2.11(b), p. 371**; proof p. 372, three cases, three one-line compressions named and closed |
| the exclusion clause (no irreducibility / completeness / trace-weight / root-of-unity theorem imported) | **verified on both sides** | Wenzl (2.1)/(2.2) p. 361, **Thm 2.2 p. 365**, **Prop. 2.10 p. 371**, **(3.5)/(3.6) p. 376**, **Thm 3.6(a) p. 378**, each with a printed SM6 counterpart carrying its own proof |
| the Jones cross-checks: **Def. 6.1** and **Prop. 6.2** p. 348; **Fig. 5.3 / (5.4) / (5.5)** p. 346; **Thm 9.7** p. 359; the bracket via **Check 9.8** p. 359 | **T1 exact** — the required depth for a cross-check | Jones 1987. Thm 9.7's own derivation chain was **not** re-read this pass; the SM1 L-5 seat's T2 on it is recorded as that seat's reading |
| the disclosed source defects: Wenzl p. 365 base case, eq. (3.6), Thm 3.6(a); Jones (9.6)'s "$\alpha,\beta\ge0$" | **all four confirmed at the printed page and confirmed NOT imported** | see below |
| Gorsky Cor. 3.3 / Cor. 3.4 p. 11; BEM (3.35) (both editions); DGR §2.3, §2.5 | **T1** | comparison sources on SM6, not premises |
| Wenzl 1985 thesis, printed p. 32 | **located, hashed, page image read; no clause graded** | consumed by nothing |

### The four disclosed defects, confirmed and confirmed not imported

1. **Wenzl p. 365** prints "$\pi_{[2]}(e_1)=1\ne0=\pi_{[1^2]}(e_1)$"; his own
   p. 361 $a_d$ and p. 363 (2.3) give $a_{-1}=0$ on the one-row tableau and
   $a_{+1}=1$ on the one-column tableau — **the labels are interchanged**
   (verified in exact arithmetic). SM6 states the correct convention and says
   the sentence "is not used" (sm-7:667–670).
2. **Wenzl (3.6), p. 376** has $\eta$-free numerator $q-q^{j-i}$ where (3.5)
   with his own special choice gives $1-q^{j-i+1}$; one box: printed $-1$
   against $+1$. SM6 prints the **correct** numerator at `hd:correct-numerator`
   (sm-7:1090–1093) and the one-box weight $(\mathfrak a-\mathfrak b)/(1-q)=1$
   at sm-7:1046–1047.
3. **Wenzl Theorem 3.6(a), p. 378** routes its weight vector through (3.6)
   explicitly ("with $w_\lambda=s_\lambda(\eta,q)$ (see (3.6))"), so SM6's
   clause "nor the weight assertion of Theorem 3.6(a) is imported after a
   silent correction" is **exactly on target**. `hd:trace` proves existence,
   compatibility, the Markov equation and uniqueness internally.
4. **Jones (9.6), p. 359** prints "$\alpha,\beta\ge0$" where "$\gamma,\beta\ge0$"
   is required — there is no $\alpha$ in the formula, and Thm 9.7 three lines
   below is correct. SM6 prints $\beta,\gamma\ge0$ and states the misprint
   (`rem:torus-conventions`(3)).

### Independent positive control

Evaluating **Jones's Theorem 9.7 exactly as printed** (p. 359), with
$[j]!=\prod_{i=1}^j(1-q^i)$ and $\lambda=a^{-2}q^{-1}$ ($z=0\iff q=1$), the
coefficient at $a^{-(r-1)(2r+2)}z^0$ of $T(r,2r+1)$ is
$-2,\,5,\,-14,\,42,\,-132$ for $r=2,\dots,6$ — i.e. $(-1)^{r-1}\mathrm{Cat}_r$,
matching SM6's `hsm:terminal-value` and `lit:torus`. Of five deliberate breaks
run at $r=4$, **three fire** ($q$-integer bracket $\to0$; sign $\to+14$;
exponent swap $\to+14$); the $\lambda=a^{-2}$ break does **not** discriminate at
$q\to1$ and the prefactor break is degenerate — both reported as
non-discriminating, not as firing controls.

---

## Conditions on the T2 keep

### C1 (must) — the thesis clause is not disclosed where the registry says it is

sm-11:331–335 asserts that the listed defects "are disclosed at Literature
input~\ref{hd:tableau-source} and in the phase evidence". **At
`hd:tableau-source` only two are** — Wenzl's p. 365 base case and (3.6)
(sm-7:667–674). The thesis is disclosed nowhere in `sm-7-anchors.tex`: the
strings `WenzlThesis` and `thesis` do not occur in that file at all. Either
name the phase evidence for that item alone, or drop the item from that
conjunction.

### C2 (must) — the thesis's notation is not a "normalization defect"

I read thesis printed **p. 32** at the page image. What is there is a
*different, internally consistent presentation* of the same weights:
$\{\lambda\}(w,z,q)=\frac{\prod_{1\le r<s\le m}(1-q^{d(r,s)})}{\prod_{r=1}^m[\lambda_r+m-r]!}R^{wz}_\lambda$,
with $d(r,s)=\lambda_r-\lambda_s+s-r$, $[k]!=(1-q)(1-q^2)\cdots(1-q^k)$,
$R^{wz}_\lambda$ the array $q^{i-1}z+q^{j-1}w$, and
$\{\lambda\}(\eta,q)=\{\lambda\}(\eta(1+q)-q,\ 1-\eta(1+q),\ q)$. Under
$z\mapsto\mathfrak a$, $w\mapsto-\mathfrak b$ its box factors are **exactly**
Jones's Figure 5.3 and SM6's `hd:jones-boxes`. **There is no misprint here to
disclose.**

Grouping it with two genuine misprints under "the sources' normalization
defects" is the same class of error F-25-72 was — a source's defect
mis-described — and F-25-72 was a *must*. The accurate statement, if the clause
is kept, is a **convention trap**: *Wenzl's thesis writes the same weights with
its letters $w,z$ swapped relative to Jones's $w,z$ (thesis $z$ = Jones's $w$;
thesis $w$ = $-$Jones's $z$), and uses the same non-standard $[k]!$.*

### C3 (must) — the bib note and the registry clause contradict each other

`sm-refs.bib:57` records that the copy on file "was consulted for its title
pages only". That is an accurate record of the author's consultation
(`phase25/LITERATURE.md`, 2026-09-05T19:29:30Z, "Wenzl 1985 thesis, title pages
(DEPTH: identification only)"). It cannot stand beside a substantive registry
claim about the thesis's notation. Fix the registry clause (C1/C2), not the
note — or, if the clause is to carry content, attribute it to the reading that
produced it (this lane, `T1_STATEMENT.md` §5) and update the note to match.

**Simplest form that satisfies C1–C3** (registry text only, no proof body
touched, and nothing about the entry's tier changes):

> …the sources' normalization defects — Wenzl's printed p.~365 base case and
> eq.~(3.6), disclosed at Literature input~\ref{hd:tableau-source}, and Jones's
> equation~(9.6), disclosed at Remark~\ref{rem:torus-conventions} — are stated
> and no silently corrected expression is imported. Wenzl's 1985
> thesis~\cite{WenzlThesis} is on file and consumed by nothing; its printed
> p.~32 gives the same weights in a different presentation, with the letters
> $w,z$ interchanged relative to Jones's and the same non-standard
> $[k]!=\prod_{i\leq k}(1-q^i)$ (phase evidence, seat
> \texttt{L-5\_EXIT}).

---

## Observations (should / optional; none blocks the keep)

**O1 (should).** `hsm:notation`'s status locator is now RC
`p12:source-evaluation` — an **internal** RC document, not a published source.
The lemma is proved internally, its DAG parents are `lp:core`,
`lp:split-circle`, `rp:record-polynomial`, and **it consumes no L-5 literature
at all**. Its published counterpart is Jones **Prop. 6.2, p. 348**, which SM6
cross-checks in `rem:torus-conventions` and deliberately does not import (RC
`torus_dictionary.tex:42`: "Jones's global existence and invariance argument is
not used"). One clause in the L-5 entry saying so would prevent a reader taking
the RC locator for a source. *(Verified: the F-25-149 repair itself is correct —
the new locator does carry the definition, the unknot value and the UNDER-first
initialization; the superseded one deferred to it.)*

**O2 (optional, positive).** `rem:torus-conventions`(1)'s bracket claim has a
**second published witness** found this pass: Wenzl's 1985 thesis, printed
p. 32, defines $[k]!=(1-q)(1-q^2)\cdots(1-q^k)$. If C2's rewrite keeps the
thesis clause, this is the natural thing for it to say.

**O3 (optional).** The disclosure paragraph names "printed p. 365" and "(3.6)"
but gives no page for **Theorem 3.6(a)**; it is on **p. 378**, and (3.5)/(3.6)
are on **p. 376**. Adding the two page numbers costs a few characters and makes
the disclosure checkable without a search.

**O4 (optional).** sm-11:363–364 says `lit:torus`'s "reference occurs only in
this registry". Two of its references are in `rem:torus-conventions`
(sm-7:1701, 1712). Neither is a proof, so the substantive claim — no proof
consumes it — is true and verified; "occurs in no proof" would be exact.

**O5 (optional).** The sentence at sm-11:337–341 — "the T2 weight is carried by
Jones (Theorem 9.7, its derivation chain read) for the polynomial and by Gorsky
… for the coefficient extraction" — is correctly attributed and dated to the
SM1 seat, but it describes the **superseded** premise structure; on SM6 the only
retained external premise is `hd:tableau-source` and Jones and Gorsky are
cross-checks. A past-tense marker ("on the route SM1 registered") would remove
the ambiguity.

---

## What this seat verified that had not been verified before

- **F-25-12 / F-25-145 at the bytes.** `thm:comparison`'s hypothesis (f) cites
  `lem:corner-values`(i) directly (`sm-6-comparison.tex:306–307`), and
  `\ref{thm:C-star}` occurs in **no proof** frame-wide. The SM2 seat left this
  as a registry claim; it is now checked.
- **The BEM locator resolves in the edition the bibliography names.** The
  published Ann. Henri Poincaré text is on disk
  (`phase198/.../brini_eynard_marino_2012_published.pdf`, `cc6eec5e…`) and
  numbers the generating function **(3.35)** on **printed p. 1888**, identically
  to arXiv v1 — so `\cite[eq.~(3.35)]{BEM}` is not a preprint-only locator.
- **"final arXiv versions (v3 and v2)" confirmed against the live submission
  histories** (arXiv:1003.0916 → v3 7 Oct 2011; arXiv:math/0505662 → v2
  7 Dec 2005).
- **Wenzl Theorem 3.6(a), p. 378, read**, which is what makes the SM's
  "not imported after a silent correction" clause verifiable rather than
  plausible: 3.6(a) points at (3.6) by name.
- **Wenzl's Lemma 2.1(i), (ii), (vi)** — asserted on p. 362 as "straightforward
  computations", never printed — verified in exact rational arithmetic, together
  with SM6's own `hd:axial-sum` / `hd:axial-relation` restatement of (ii).
- **Wenzl's 1985 thesis read past its title pages** (printed p. 32), which is
  what produced C1–C3 and O2.

---

## Escalations to the operator

**None.** Every published locator SM6 cites for L-5 — Wenzl 1988 pp. 361–365,
371–372, 376, 378; Jones pp. 346, 348, 359; Gorsky p. 11; BEM (3.35) in both
editions; DGR §§2.3, 2.5; the 1985 thesis — was found and read at the printed
page inside the campaign folder. **No L-5 source is blocked, and none of
E-25-1 … E-25-6 is an L-5 item.**

---

## What this seat did not do

Wrote no proof of anything (rule 8): every arithmetic check ran on a **source's
own algebra** or on a formula the source printed, in exact rationals with
deliberately broken controls, and the two non-firing controls are reported as
non-firing. Refereed no printed proof — the `transcribed (unrefereed)` tags on
`hsm:notation`, `hd:jones-torus`, `hsm:terminal` and `lit:torus`, and bench A's
`proved (refereed …)` tags on the `hd:` chain, are proof-side and are neither
touched nor cleared here. Did not re-read Jones's Thm 9.7 derivation chain,
Gorsky's Appendix, or the proofs of the Wenzl results SM6 excludes. Did not
read `sm-6-comparison.tex` beyond the single hypothesis-(f) paragraph named
above. Inherited no verdict: the SM1 `L-5` and SM2 `L-1-L-5_SM2` lanes were
checksum-verified and read as evidence of what was read at which bytes, and
every clause graded here was re-established from the page images listed in
`ACCESS_AUDIT.md` §A2.
