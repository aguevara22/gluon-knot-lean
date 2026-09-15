# L-4 EXIT — T2 DELTA: what was read at proof depth, by whom, and what was not

Rule 8 binds throughout: **no bench proof is offered here as a substitute for a
published one.** Where a source asserts, this file says "asserted" and stops.
Where an earlier seat did the reading, this file **names that seat** and does
not re-badge its depth as its own. Stamp 2026-09-06T01:56:55Z; frame SM6
verified 20/20 first.

---

## 1. Ng pp. 6–8 + Figure 1 — read at proof depth by this seat

### 1.1 What Ng prints as the proof

Ng's Lemma 1 (p. 6) is stated and then, in his own words, **sketched**: *"For
completeness, we sketch here the proof of the lemma."* The sketch is two
sentences of setup —

> Consider the portion of $F$ immediately to the right of the rightmost left
> cusp of $F$. By using Legendrian Reidemeister moves II and III if necessary,
> we can assume that this portion of $F$ has one of the forms shown on the left
> hand side of Figure 1.

— then **Figure 1 itself** (p. 7), a two-column picture of initial fronts and
their simplifications with three arrow types (solid = skein crossing changes,
dashed = destabilizations or deletions of trivial unknots, equalities =
Legendrian isotopies), and one closing sentence (p. 8):

> In each case, the use of skein crossing changes, Legendrian isotopy,
> Legendrian destabilization, and/or the removal of trivial unknots yields a
> simpler front (one with lower $s$, or the same $s$ and lower $s'$). The
> lemma, and Theorem 2, follows. □

**Depth reached at Ng alone: below T2.** The case analysis is carried by a
figure and by the phrase *"In each case"*; Ng does not enumerate the cases in
text, and he attributes the lemma to Rutherford. This is not a criticism of Ng
— he says he is sketching — it is the statement of where the chain has to go
next, and both SM6 and the earlier seats send it there.

### 1.2 The surrounding induction, read (pp. 6, 8)

To be sure the lemma is doing the work SM6 uses it for, this seat read the
induction that consumes it. p. 6: the induction is on $s(F)$; base $s(F)=2$ is
the standard Legendrian unknot; a tangle replacement gives three fronts of
which *"the last two of the resulting fronts have lower $s$ than $F$ and are
covered by the induction assumption, while the first has the same $s$"*; the
secondary induction is on $s'(F)$, *"the number of singularities to the right
of the rightmost left cusp of $F$"*. p. 8, *Proof of Theorem 1*: the oriented
case, *"a minor modification of the proof of Theorem 2"*, with
$c_\downarrow(F)-\tilde\imath(F)\ge0$ replacing $c(F)-\tilde\imath(F)\ge0$, and
*"We now apply Lemma 1 as before."*

**This matches the shape SM6 prints in `ng:local-front-bound`'s proof**
(`sm-3`:2313–2345): strong induction on $s(F)$, base $s=2$ a standard circle,
backward traversal of the chain, cusp-skein step handled by
`ng:cusp-skein`'s inequality. **The correspondence is structural, not verbatim:
SM6's induction is over its own $B(F)=D(F)-w(F)-d(F)-1$, proved internally,
whereas Ng's is over $c_\downarrow-\tilde\imath$ for an abstract $i$.** SM6
says exactly this at :2297–2300 (*"The local polynomial/count certificates above
and the following degree induction are separate arguments."*).

### 1.3 Ng's Corollary 1, read at p. 8

*"Define $i(L)=\max\text{-deg}_a P(L)(a,z)+1$. By the skein relation and
normalization for the HOMFLY-PT polynomial, the conditions in Theorem 1 hold,
and Theorem 1 then gives the HOMFLY-PT bound."* One sentence; the verification
of conditions (a) and (b) is left to the reader. The **L-4 seat re-derived it
independently** (`L-4/T2_PROOF.md`; LITERATURE entry of 2026-09-05T15:08:37Z)
and that reading is theirs. **Not consumed by SM6** — recorded because registry
L-4 makes a claim about it, and the claim is accurate.

---

## 2. Rutherford pp. 10–12 — read at proof depth by this seat, at its own extraction

This is where Ng's *"In each case"* becomes text, and it is the root SM6's
14-row case table follows.

**The reduction, followed.** Rutherford first reduces Lemma 3.2 to statement
(A) by the observation that *"since the fronts on the RHS of (i) have less
crossings then the fronts on the LHS, if the theorem holds for one of the
fronts on the LHS it must hold for the other"*. Then: nested inductions, outer
on $L$ = the number of left cusps of $W$ (*"The base case is handled entirely
by (ii)"*), inner on $M:=N+cr(Y)$ after writing $W=Xl^{N-2,N}_mY$ at the
rightmost left cusp, base $M=2$ by (iii) plus the outer hypothesis. The
inductive step is a **procedure depending on the first letter of $Y$** that
either reduces $N$ or $cr(\cdot)$, or increases one of $N_1,N_2$.

**All ten cases read** (Case 1 $Y=\sigma_iY'$, SubCases 1–5, p. 10–11; Case 2
$Y=r_iY'$, SubCases 1–5, p. 12). Their outcomes:

| branch | Rutherford's outcome | SM6's row |
|---|---|---|
| C1S1 $i<m-N_1-1$ or $i>m+N_2+1$ | commutes into $X$, decreasing $cr(Y)$ | "Crossing outside the strings and their next neighbors → Commute into $X$" |
| C1S2 $i=m-N_1-1$ or $m+N_2+1$ | append to a parenthesis, increasing $N_1$ or $N_2$ | "Crossing at a next neighboring position → Extend that arm string" |
| C1S3 $i=m-N_1$ or $m+N_2$, $i\neq m$ | $N_1$ skein moves, then a **type II** removes two crossings | "Crossing at an occupied outer string endpoint → … Expose type II and remove two crossings" |
| C1S4 interior $i$ | **type 3** move plus planar isotopy, $cr(Y)$ down by 1 | "Crossing strictly inside a string → Type III, then commutations" |
| C1S5 $i=m$ | one string empty ⇒ **type 2**; both empty ⇒ *"the value of the polynomial is 0 by (ii)"*; neither ⇒ skein + type 3, $c(Y)$ down by 1 | three rows: "Middle crossing, exactly one nonempty string", "Middle crossing, no strings → the $l_i\sigma_i$ shortcut", "Middle crossing, both strings nonempty" |
| C2S1 $i<m-N_1-1$ | commutes into $X$, decreasing $N$ | "Right cusp beyond an arm's next neighbor → Commute into $X$ with the correct two-strand index shift" |
| C2S2 $i=m-N_1-1$ | $N_1$ skein moves reach $Xl_{m-N_1}r_{m-N_1-1}\ldots$, *"which is has a zig-zag"* | "Right cusp at a next neighbor → … Expose a zigzag, then delete it" |
| C2S3 $i=m-N_1$ | *"The inclusion of the factor $\sigma_{m-N_1}r_{m-N_1}$ shows that the polynomial is 0 by (ii)"* | "Right cusp at a string endpoint → Expose $\sigma_ir_i$ → Crossed-cusp shortcut" |
| C2S4 interior $i$ | planar isotopy exposes $\sigma_i\sigma_{i-1}r_i$, **type 2** removes two crossings | "Right cusp strictly inside a string → Commute to expose type II" |
| C2S5 $i=m$ | both empty ⇒ disjoint unknot, (iii) + outer hypothesis; one empty ⇒ **type 1**; neither ⇒ skein arranges $\sigma_m\sigma_{m+1}r_m$, **type 2** | three rows: "Middle right cusp, neither string nonempty / exactly one string nonempty / both strings nonempty" |

**The 14 rows of SM6's table are Rutherford's ten SubCases with the four
multi-outcome ones split out.** No row of SM6's table lacks a Rutherford
counterpart, and no Rutherford SubCase is unrepresented.

**Depth reached: T2 at this root** for the descent SM6 uses, with two named
residuals:

* **R-a (the source's own gap, not the SM's).** The finiteness of arm-string
  extension is **asserted**: *"Since $N_1$ and $N_2$ can only be increased a
  finite number of times this will complete the inductive step"* (p. 10). No
  reason is printed. SM6 supplies one ("bounded by the active strand count",
  :2192–2193, :2273–2276). **Under rule 8 this is a bench-supplied step and
  SM6 declares it as such.** This seat did not check that the supplied reason
  is correct — that is a proof referee's job, not a source seat's — and does
  not certify it.
* **R-b (the source's malformed indices).** §3 below.

**What SM6 imports is not Lemma 3.2's printed conclusion.** Lemma 3.2 concludes
about the **ruling polynomial** $R_K$; SM6 imports **statement (A)**, the
combinatorial core of the proof, and says so. The residual is therefore
categorical, not repairable by more reading: *the imported statement is the
campaign's consolidation of a published proof, not a published sentence.* SM6
prints that disclosure at :2196–2205, and the registry repeats it at
`sm-11`:269–274.

---

## 3. Rutherford's malformed index strings — SM6's disclosure re-verified at the bytes

SM6 discloses four defects at `sm-3`:2283–2291. Checked one by one in **this
seat's own extraction**:

| SM6's claim | Rutherford, at the bytes | verdict |
|---|---|---|
| impossible printed range on p. 11 | Case 1, **SubCase 4**: *"$m-N_1>i>m$ or $m<i<m+N_2$"* — the first alternative is empty for $N_1\ge0$; the second is well formed, and the displayed argument treats the interior range | **confirmed** |
| impossible printed range on p. 12 | Case 2, **SubCase 4**: *"$m-N_1>i>m$"* — empty | **confirmed** |
| duplicated $m+2$ on p. 11 | Case 1, SubCase 5: *"$(\sigma_{m+2}\sigma_{m+2}\ldots\sigma_{m+N_2})$"*, in all four lines of the display | **confirmed** |
| the two-strand-shifted analogue on p. 12 | Case 2, SubCase 5: *"$(\sigma_{m+2-2}\sigma_{m+2-2}\ldots\sigma_{m+N_2-2})$"* — and the neighbouring **SubCase 4** prints the correct shifted string *"$(\sigma_{m+1-2}\sigma_{m+2-2}\ldots\sigma_{m+N_2-2})$"*, which is what fixes the intended reading | **confirmed** |

**SM6's disclosure is accurate and complete on all four**, and its sentence
*"The malformed literal strings are not imported as identities: the actual
strand operations and Ng's Figure 1 specify the moves used here"* is the right
form. This is an **independent re-verification** of what the SM2 seat found
(F-25-85); the two extractions agree.

**Residual, unchanged and not closable by disclosure:** the corrections are the
campaign's reading of a malformed printed proof. The clean fix is the published
IMRN text (Lemma 3.3). **E-25-5**, and this pass adds a fact that closes off the
cheap route: `arxiv.org/abs/math/0511097` has **only v1** — there is no arXiv
version carrying the published numbering. Operator fetch, low priority, not
blocking, for the reason above (the descent was read in the source's own case
structure and every SM6 row has a counterpart there).

---

## 4. Etnyre — proof depth on the two clauses in this seat's charge

* **eq. (9), §2.6.4, p. 15 — proof NOT reached at the locator.** The entire
  justification is *"The argument for this formula is exactly like the one for
  Equation (8)."* Eq. (8) is the **Lagrangian** $tb$ formula, whose own
  justification (p. 15) is *"In the Lagrangian projection think about trying to
  pull $L'$ straight up."* The front $tb$ formula, eq. (7), carries a
  $-\frac12\#\text{cusps}$ correction that eq. (8) does not, and what makes it
  vanish for a transverse front is not stated at the locator. **Below T2 at
  Etnyre.** SM6 does not rest it there: `src:contact` names Geiges arXiv
  Lemma 3.3 p. 46 and the book Prop. 3.5.32 p. 127 as the **printed proofs** and
  says only that *"Etnyre's equation (9) … states it"*. The T2 grades for those
  two witnesses are the **L-3 seat's** (book Prop. 3.5.32) and the **SM2 seat's**
  (arXiv Lemma 3.3, T2 modulo one off-disk reduction to Saveliev); this seat
  **did not re-read either**, and does not re-badge their depths.
* **§2.9, pp. 19–20 — read.** Lemma 2.22 carries a printed proof (the
  $t(\cdot,\cdot,\cdot)$ twisting computation, read here), with the compressions
  the SM2 seat named. The **bridge sentence** on p. 20 (*"By considering the
  obvious annulus between $T$ and $T_l$ it is easy to see that the positive
  transverse push off of $T_l$ is $T$"*) is preceded by a construction —
  $\xi_{sym}=\ker(dz+r^2d\varphi)$ on $M=\mathbb R^3/(z\mapsto z+1)$, the
  Moser-technique neighbourhood $N\cong S_a$, the torus $T_b$ with $b^2=1/n$,
  the leaf $T_l$ — and closed by *"it is easy to see"*. **Depth at Etnyre: a
  printed construction with the final step asserted.** SM6 does not consume it
  (it constructs the bridge internally and flags the construction for rule-8
  cross-check), so no verdict on the SM turns on this depth; it matters only
  that the cross-check target be the right sentence (finding X-1,
  `T1_STATEMENT.md` §4.2).

---

## 5. What this seat did **not** do

* Did **not** re-read Bennequin, and did not read Morton's proofs. Morton's
  statements, dictionary and reference list were read here; the **full 3-page
  proof reading is the L-4 seat's**, cited as theirs.
* Did **not** re-read the Geiges book or the Geiges arXiv survey. Their T2
  grades belong to the L-3 seat and the SM2 seat respectively.
* Did **not** referee any printed proof of SM6. `ng:deletions` and
  `ng:local-front-bound` are held items; the arm-extension reason SM6 supplies,
  the $B$-arithmetic of `ng:deletions`/`ng:circle`/`ng:cusp-skein`, and
  `fd:generic-front`'s construction are **not certified here**. What this seat
  checked is that the *hypotheses* of `fd:ng-bound` are discharged by clauses
  `fd:generic-front` actually states (`CONSUMPTION_MAP.md` §3) — a citation
  check, not a proof referee.
* Did **not** write a proof of anything.
* Did **not** touch a frame byte, `NEWSM/`, `informal draft/`, any v7 letter
  file, `.env`, `challenge/sealed/`, or any lane but this one (the two
  predecessor L-4 lanes were read, hashes verified first).
* No advisor call. No GCP.

---

## 6. Depth table

| id | statement | locator | depth | read by |
|---|---|---|---|---|
| NG-1 | Lemma 1: one step to lower $s$, or same $s$ and lower $s'$ | Ng p. 6, Fig. 1 p. 7, closing p. 8 | **statement + sketch; below T2 at Ng alone** (author's own word: "sketch") | this seat |
| NG-2 | the $s$/$s'$ double induction consuming Lemma 1 | Ng pp. 6, 8 | read; structural correspondence to SM6's induction confirmed | this seat |
| NG-3 | §1.2 normalization $aP_+-a^{-1}P_-=zP_0$, $P_\bigcirc=1$ | Ng p. 5 | **T1 verbatim** against `lit:homfly` | this seat |
| NG-4 | Cor. 1 from Thm 1 with $i=\max\text{-deg}_aP+1$ | Ng p. 8 | proof read (one sentence); **the independent re-derivation is the L-4 seat's** | this seat (reading) / L-4 seat (re-derivation) |
| RU-1 | statement (A) and its nested induction, ten SubCases | Rutherford p. 9 (stmt), pp. 10–12 (proof) | **T2 at the root**, with residuals R-a (arm extension asserted) and R-b (malformed indices) | this seat |
| RU-2 | the four malformed index strings | Rutherford pp. 11–12 | **re-verified independently**; SM6's disclosure accurate and complete | this seat |
| RU-3 | the published IMRN wording (Lemma 3.3) | IMRN 2006 Art. ID 78591 | **not reached — blocked, E-25-5; arXiv has only v1** | — |
| MO-1 | Thm 1 for any diagram; Cor 1 for closed braids; $v=a^{-1}$ | Morton pp. 107–108 | statement level here; **proof reading is the L-4 seat's** | this seat / L-4 seat |
| MO-2 | [2] = Franks–Williams | Morton p. 109 | read | this seat |
| FW | Franks–Williams itself | Trans. AMS 303 (1987) 97–108 | **not reached — blocked, E-25-2**; consumed by no proof of SM6 | — |
| ET-1 | eq. (9) $sl(T)=\mathrm{writhe}(\Pi(L))$ | Etnyre §2.6.4 p. 15 | **T1 with three defects; T2 not reached at this locator** | this seat |
| ET-2 | Lemma 2.22 eq. (17) $sl(T_\pm(L))=tb\mp r$ | Etnyre §2.9 p. 19 | printed proof read | this seat |
| ET-3 | the bridge: every transverse knot is the positive pushoff of a Legendrian | Etnyre §2.9 **p. 20** | printed construction, final step asserted | this seat |
| — | eq. (9)'s T2 witnesses (Geiges book Prop. 3.5.32; arXiv Lemma 3.3) | — | **T2**, not re-read here | L-3 seat / SM2 seat |
| — | Bennequin Thm 3, the classical form | — | not read here; consumed by no proof | L-4 seat |
