# L-4 EXIT — RECOMMENDATION on frame SM6

Seat `source L-4 EXIT`, cold, seated by
`evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`. Audited object: frame **SM6**,
manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`,
`shasum -c` **20/20 OK** before anything was read. Verdicts are on SM6's bytes
only. Stamp 2026-09-06T01:56:55Z.

Everything below is **this seat's claim**, not a status. The kernel of the
matter is stated first, the deflation immediately after it.

---

## 1. Verdict

> ### L-4 (`reg:slbound`): **KEEP AT T2.**
> Four editorial repairs, one observation, two escalations carried. **No
> premise defect, no missing source, nothing below T2 on the route this
> document prints.**

**What "T2" means here, said precisely.** L-4's whole literature interface is
one environment, `ng:finite-word` (`sm-3-statesum.tex`:2169–2205). Against
`phase2/VERIFICATION_STANDARD.md`:

* **T1 — full text on disk, hashed, statement at the cited locator.** Ng
  (`5e57702f…`) and Rutherford (`024dc444…`) are on disk and were read at this
  seat's own extraction. **Both printed locators resolve**: Ng's Lemma 1 on
  p. 6, Figure 1 on p. 7, the closing on p. 8; Rutherford's Lemma 3.2 statement
  at the foot of p. 9, its proof pp. 10–12. The registry's tighter parenthetical
  (*"statement p. 9, proof pp. 10–12"*) is exact.
* **T2 — the source's proof read and checked to establish the used statement.**
  This seat read **all ten SubCases of Rutherford pp. 10–12** and matched them
  against SM6's 14-row table: every row has a Rutherford counterpart and every
  SubCase is represented (`T2_DELTA.md` §2). The descent SM6 uses is the descent
  proved there.

**The deflation, and it is the whole of it.** The imported *statement* is not
either source's printed sentence — it is the campaign's consolidation of the
source's **proof**. SM6 says so, in the environment itself
(`sm-3`:2196–2205) and again in the registry (`sm-11`:269–274), in three named
ways. **This seat verified each of the three at the sources, independently:**

| SM6's disclosed departure | verified at |
|---|---|
| a **chain** where Ng gives a **step** | Ng p. 6 — *"we can turn $F$ into a front which either has lower $s$, or the same $s$ and lower $s'$"* |
| Rutherford's **two ruling-polynomial terminal branches** replaced by geometric shortcuts | Rutherford p. 11 Case 1 SubCase 5 with $N_1=N_2=0$ and p. 12 Case 2 SubCase 3 — **exactly two** branches close on *"the polynomial is 0 by (ii)"* |
| the **arm-extension bound supplied** where Rutherford asserts finiteness | Rutherford p. 10 — *"Since $N_1$ and $N_2$ can only be increased a finite number of times this will complete the inductive step"*, no reason printed |

So the honest wording is: **the entry is at T2 on the portion it imports**, and
one clause of the `lit` environment — the arm-extension bound — is a
campaign-supplied reason riding inside a literature block, **declared as such by
the block**. That is what R-25-13's "resting on a declared source fact" and
rule 8's cross-check flag are for, and SM6 uses both. Whether the supplied
one-sentence reason (`sm-3`:2273–2277) is adequate is a **proof-referee**
question; `ng:finite-word` is `lit`-tagged and `ng:local-front-bound` and
`ng:deletions` are held transcriptions. **This seat clears none of them.**

**Two further things the exit frame gets right, and they are not small.**

1. **SM1's seam is structurally gone, not papered over.** F-25-51's defect was a
   bound on $\overline{sl}$ (a maximum over Legendrian representatives) applied
   to one constructed transverse knot. SM6's `ng:local-front-bound` is per-front
   and says so twice (`sm-3`:1898–1899, :3386–3388); the transverse↔Legendrian
   bridge is **constructed** (`fd:transverse-neighborhood`, cleared) rather than
   cited; Ng's Theorem 1, Corollary 1 and $\overline{sl}$ are **consumed by no
   proof**.
2. **The load-bearing input is now visible to the ordering instrument, and its
   hypothesis is discharged.** F-25-107's repair (`fd:ng-bound`, round 3) and
   F-25-153's (the discharge from `fd:generic-front`, round 5) are both present
   at the bytes, and the discharge covers every clause of `ng:front-domain`
   (`CONSUMPTION_MAP.md` §3).

---

## 2. The charter's standing question: does "T3 available" appear anywhere?

**No.** Grep over every `sm-*.tex`, `README.md`, `DAG.md` and
`DISCREPANCIES.md` of SM6 returns four occurrences of the string `T3`, and
**all four are disclaimers**:

* `sm-11-registry.tex`:10–13 — the registry preamble states the rule:
  *"no Lean formalization or formal T3 certificate is claimed (operator ruling
  R-25-2), and the words ``T3 available'' are not used: an internal derivation
  resting on a declared source fact is described as such, with what it buys
  (ruling R-25-13)."*
* `sm-11`:142 — L-2: *"it is an internal printed proof, not a ``T3''"*.
* `sm-11`:246 — inside L-3, reporting a seat's verdict.

For L-4 specifically, R-25-13's positive requirement is met in full at
`sm-11`:275–283: the derivation is named, its **resting** on the source fact is
stated, **what it buys** is stated (removes the maximization and every
ambient-invariance premise; narrows the literature dependence to the finite
Ng–Rutherford word procedure plus the L-1 polynomial interface), and the
**non-removal** is stated (*"it does not remove Ng and Rutherford from the
trusted base"*). **F-25-52 and the L-4 half of F-25-56 are satisfied.**

---

## 3. Repairs — four, all editorial, none touching a proof body

**X-1 — the bridge's sub-locator names the wrong sentence (two sites).**
`sm-11`:283–287 and `sm-11`:876–878.

At Etnyre's bytes, **Lemma 2.22 / eq. (17) is $sl(T_\pm(L))=tb(L)\mp r(L)$**.
The sentence SM6 quotes — *"every transverse knot is transversely isotopic to
the positive transverse pushoff of a Legendrian knot"* — is at Etnyre **§2.9,
p. 20**. Since the entry flags `fd:transverse-neighborhood` for rule-8
cross-check *against that statement*, the pointer has to reach it.

> Suggested wording, offered as a proposal, not an edit — registry L-4:
>
> … and the published statement of record for that step, "every transverse knot
> is transversely isotopic to the positive transverse pushoff of a Legendrian
> knot", is Etnyre \cite[Section~2.9, p.~20, the Legendrian push-off paragraph
> and the sentence following Theorem~2.23]{Etnyre} (the sign convention that
> matches Ng's is his Lemma~2.22, equation~(17)), against which …
>
> and, in the §11 rule-8 list: "Lemma \ref{fd:transverse-neighborhood}'s
> construction (against Etnyre §2.9, p. 20)".

**X-2 — the closure count in L-4 is stale.** `sm-11`:307–310 reads
*"(33 statements; declared inputs …)"*. The frame's own `DAG.md`:5 reads
**38**. Cross-frame check: SM4 DAG 33 / registry 33 (consistent); SM5 DAG 36 /
registry 33; **SM6 DAG 38 / registry 33**. The declared-input list is correct.
Repair: the number, from `DAG.md`. *(A frame that contradicts itself on a
countable instrument reading is the cheapest possible finding to close and the
most embarrassing to leave in an exit frame.)*

**X-3 — `@article{Ng}` carries no retained-version note.** Every Ng locator in
SM6 resolves on the retained **15-page author preprint, arXiv:0709.2141v1
(13 Sep 2007)**; the bib entry names the **IMRN 2008** printing. The frame's
three other preprint-based entries each carry a version note, and `Etnyre`'s was
added in response to **F-25-84**, this exact defect. Repair: one field.

> `note={arXiv:0709.2141v1, 13 September 2007; the page and figure locators
> cited in this document were verified on that retained 15-page author version
> and not on the IMRN printing}`

**X-4 — a fourth spelling of the degree symbol, and one use outside `def:adeg`'s
scope.** F-25-137's repair introduced `\deg_a`, `\max\deg_a`, `\mindeg_a`
(`sm-3`:1887–1892; `sm.tex`:47 declares only the macro `\mindeg`). Six later
sites write `\min\deg_a` — `sm-3`:4330, 4552, 4553, 4743, 4747 and
`sm-4`:682 — and `sm-3`:4579 writes `\mindeg_z`, a degree in $z$, while
`def:adeg` is stated *"For a nonzero Laurent polynomial $f$ in $a$"*. It shows
in print: `sm.pdf` **p. 108** carries "min deg$_a$" and "mindeg$_a$" within two
lines. Repair: one spelling throughout, and either widen `def:adeg` to a
general variable or give the $z$-degree its own sentence.

**O-3 (observation, offered rather than filed) — the entry's clearance
sentence.** `sm-11`:262–266 says *"the theorem and the front lemmas cleared by
bench A, Lemma `ng:deletions` held"*. The six front lemmas do carry
`proved (refereed: bench A, 2026-09-05T15:51:04Z)` and `ng:deletions` is held —
but **`ng:local-front-bound` itself reverted to `transcribed (unrefereed)`**
after the round-5 touch, as its own tag and `DAG.md`'s census both record. The
registry preamble does scope referee status to SM2, so the sentence is
defensible; a reader of the exit frame nonetheless sees "cleared" with no sign
of the reversion, and the round-5 lemma `ng:smoothing-record` — now inside the
L-4 chain, licensing the symbol $P_{S(F)}$ that `fd:ng-bound` exports — is not
mentioned by the entry at all. Curator's call whether this is worth a hunk.

---

## 4. Escalations, restated by name — neither blocking

**E-25-2 — Franks & Williams, Trans. AMS 303 (1987) 97–108.** Still not on disk
(folder-wide sweep this pass). Routes tried this pass: AMS PDF → **HTTP 403**;
open-access search → citing literature only. **No verdict is recorded against
the source.** It does not block L-4: SM6 cites it twice, both in the registry,
in **no proof**, and Morton's own p. 109 gives *"[2] J. FRANKS and
R. F. WILLIAMS. Braids and the Jones polynomial. (Preprint 1985)"* with his
Corollary 1 attributed to "[5], [2]" — so the entry's role clause for it is
checkable without it.

**E-25-5 — Rutherford, IMRN 2006, Art. ID 78591 (Lemma 3.3).** Still not on
disk. OUP returns abstract and references only. **New this pass, and it is why
the row should stay open rather than be quietly retired:
`arxiv.org/abs/math/0511097` has exactly one version, v1.** There is no arXiv
route to the published numbering or wording, so the campaign's four typed
corrections of the malformed index strings (`sm-3`:2283–2291) — which this seat
re-verified as accurate and complete against the arXiv bytes — can be checked
against the published proof **only** if the operator supplies the IMRN text.
Low priority, not blocking.

**If one wanted L-4 with no residual at all, the exact missing item is that
one text**, and nothing else. That is the honest form of the answer to
"below T2 with the exact missing item": there is no missing item that puts the
entry below T2; there is one that would retire its last source-side residual.

---

## 5. What this seat did **not** certify

* No printed proof of SM6 was refereed. `ng:deletions` and
  `ng:local-front-bound` are held; `fd:generic-front`, `fd:transverse-neighborhood`,
  `fd:linking-calculus`, `cp:finite-contact-path` and `cf:thm-carrierfloor` were
  not audited as proofs. The check performed on the F-25-153 hop is a
  **citation** check: the clauses `fd:generic-front` *states* cover the clauses
  `ng:front-domain` *requires*.
* The adequacy of SM6's supplied arm-extension reason is **not** certified.
* Morton's proof, Bennequin, the Geiges book and the Geiges arXiv survey were
  **not** re-read; where their depths are used they are attributed to the L-4
  seat, the L-3 seat and the SM2 seat respectively.
* L-1 (`lit:homfly`, `lp:lm`, `lp:lm-uniqueness`) and L-3 (`src:contact`) are
  named on the route but are other seats' entries; Etnyre eq. (9) is checked
  here **as a statement** only, because this seat's charter names it.
* No frame byte, no other lane, `NEWSM/`, `informal draft/`, v7 letter file,
  `.env` or `challenge/sealed/` was written; none of the last four was read.
  No advisor call. No GCP.

---

## 6. One-line summary for the dashboard

**L-4, exit frame SM6: T2 — keep.** Both locators resolve; Rutherford's proof
read to its ten SubCases and matched row by row to SM6's table; the three
disclosed widenings re-verified at the sources; "T3 available" absent; F-25-51,
52, 56, 83, 107, 142, 153 **addressed**, F-25-137 **addressed with two notation
residues**. Four editorial repairs (X-1 wrong Etnyre sub-locator ×2 sites, X-2
stale closure count 33 vs the frame's own 38, X-3 missing Ng version note,
X-4 two degree-symbol spellings) and one observation (O-3 stale clearance
sentence). E-25-2 and E-25-5 open with the operator, neither blocking; arXiv
has only v1 of E-25-5.
