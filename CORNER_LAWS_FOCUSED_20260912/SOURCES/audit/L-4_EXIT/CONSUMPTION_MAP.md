# L-4 EXIT — CONSUMPTION MAP on frame SM6

Everything registry entry **L-4** (`reg:slbound`) puts into the document, with
the **SM locator** (file, line span, PDF page of `sm.pdf`) and the **source
locator**, checked at the source's own bytes by this seat unless the row says
otherwise. Frame SM6 verified 20/20, self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`, before any
reading. Stamp 2026-09-06T01:56:55Z.

Scope note. L-4 is the **only** registry entry in this seat's charge. `L-1`
(`lit:homfly`, `lp:lm`, `lp:lm-uniqueness`) and `L-3` (`src:contact`) are named
where the route consumes them, and one L-3 clause — Etnyre eq. (9) — is checked
at the statement because this seat's charter names it; their verdicts belong to
the L-1 and L-3 exit seats.

---

## 0. The route, and where L-4 enters it

```
thm:floor  (sm-3:4573)
 └─ cf:thm-carrierfloor (C)  (sm-3:4279)
     └─ fd:contact  (sm-3:3402, PDF p. 92)          <- the L-4 consumer
         ├─ src:contact        (sm-3:3339, PDF p. 91)  ....... L-3
         ├─ fd:ng-bound        (sm-3:3377, PDF p. 91)     <- the L-4 hop
         │   ├─ ng:local-front-bound (sm-3:2304, PDF p. 77)
         │   │   ├─ ng:finite-word     (sm-3:2169, PDF p. 76) . L-4 LEAF
         │   │   ├─ ng:front-domain, ng:smoothing-record, def:adeg
         │   │   └─ ng:commutation, ng:front-I/II/III, ng:deletions,
         │   │      ng:circle, ng:cusp-skein
         │   ├─ ng:front-domain (sm-3:1825, PDF p. 71)
         │   ├─ ng:smoothing-record (sm-3:1843, PDF p. 71)
         │   └─ lp:core                                     ....... L-1
         ├─ fd:transverse-neighborhood, fd:generic-front,
         │  fd:linking-calculus, cp:finite-contact-path   [internal]
         └─ lit:homfly                                      ....... L-1
```

**Exactly one `\begin{literature}` environment carries L-4: `ng:finite-word`.**
The whole rest of the `ng:` chain — nine statements — is a `RC ng_front (C029)`
transcription with **no source premise**. This is the shape the SM2 seat
recorded; it is unchanged on SM6, and the closure is now visible to the ruler
(F-25-107; `DAG.md`:292 and the leaf table at `DAG.md`:300).

---

## 1. The literature statement — `ng:finite-word`

| | |
|---|---|
| **SM locator** | `sm-3-statesum.tex`:2169–2205 (`\begin{literature}[Finite front-word reduction]`), PDF p. 76; its aftermatter at :2207–2214 (case-table preamble), :2216–2271 (the 14-row `longtable`), :2273–2281 (nested-descent paragraph), :2283–2291 (index-defect disclosure), :2293–2300 (the negative-scope paragraph) |
| **Status tag** | `lit: finite Ng--Rutherford word procedure; Registry~\ref{reg:slbound}; round~3: the scope of the import stated, F-25-83` |
| **Source locator as printed** | `\cite[pp.~6--8 and Figure~1]{Ng}` and `\cite[Lemma~3.2, pp.~8--12 of the arXiv version]{Rutherford}` — **inside the block** |

**What the block imports.** For an actual finite front word on
`ng:front-domain`, a **finite principal chain** to a front of smaller $s$,
built from (1) typed disjoint-gadget commutations and the three local front
moves, (2) the cusp-skein crossing interchange, (3) zigzag deletion, the
crossed-cusp shortcut, or deletion of a separated standard front circle; $s$
does not increase before the first strict decrease; secondary progress is
measured at complete block boundaries; arm-string extension is bounded by the
active strand count; at each cusp-skein interchange the compatible smoothing
branch has smaller $s$.

**The scope sentence (:2196–2205), verbatim in substance and checked clause by
clause at the sources:**

> This is the constructive word procedure, not a quantification over arbitrary
> Legendrian isotopies. The imported content is the source's finite descent,
> not its printed sentence: Ng's Lemma 1 gives one step, iterated here until
> $s$ decreases; Rutherford's two ruling-polynomial terminal branches are
> replaced here by the geometric shortcuts of Lemma `ng:deletions`; and the
> finiteness of arm-string extension, which Rutherford asserts, is given its
> reason here (seat L-3/L-4 on SM2, R6; F-25-83).

| clause of the scope sentence | source bytes this seat read | verdict |
|---|---|---|
| "Ng's Lemma 1 gives one step" | Ng p. 6: *"Lemma 1 (Rutherford [23], Lemma 3.3). Via skein crossing changes, Legendrian isotopy, Legendrian destabilization, and the removal of trivial unknots, we can turn $F$ into a front which either has lower $s$, or the same $s$ and lower $s'$."* | **accurate** — one step, with the "same $s$, lower $s'$" alternative |
| "Rutherford's two ruling-polynomial terminal branches" | Rutherford p. 11 Case 1 SubCase 5 (*"If they are both 0 the value of the polynomial is 0 by (ii)"*) and p. 12 Case 2 SubCase 3 (*"The inclusion of the factor $\sigma_{m-N_1}r_{m-N_1}$ shows that the polynomial is 0 by (ii)"*) | **accurate, and the count is exactly two**: these are the only two branches Rutherford closes on a ruling-polynomial value. (Case 2 SubCase 2 ends *"which is has a zig-zag"* — a geometric terminal, matching Ng's destabilization, not a polynomial evaluation.) |
| "the finiteness of arm-string extension, which Rutherford asserts" | Rutherford p. 10: *"Since $N_1$ and $N_2$ can only be increased a finite number of times this will complete the inductive step."* — no reason given | **accurate**; SM6 supplies "bounded by the active strand count" (:2192–2193, :2273–2276) |

**Locators, at the bytes.** Ng's Lemma 1 is on **p. 6**, followed by *"For
completeness, we sketch here the proof of the lemma"*; **Figure 1 is on p. 7**;
**p. 8** closes the lemma (*"The lemma, and Theorem 2, follows."*) and then
proves Theorem 1 and Corollary 1. Rutherford's **Lemma 3.2** statement is at
the foot of **p. 9**; its proof, isolating **statement (A)**, runs **pp. 10–12**
in Case 1 ($Y=\sigma_iY'$) and Case 2 ($Y=r_iY'$), five SubCases each; **p. 8**
carries the proof of the skein relations for $R_K$ and $B_K$ and opens the
tangle-word presentation. So the block's `pp. 8--12` is correct and generous;
the registry's tighter `statement p.~9, proof pp.~10--12` is exact. **Both
locators resolve.**

**Version note, checked:** Ng's own reference [23] (p. 15) names
*Int. Math. Res. Not. 2006, Art. ID 78591; math/0511097*, and the retained PDF
is arXiv `math/0511097v1`, which numbers this **Lemma 3.2**. SM6 says this at
:2290–2292 (*"Ng cites the published numbering Lemma 3.3; the retained
Rutherford arXiv version numbers this proof Lemma 3.2"*) — accurate.

---

## 2. The internal chain that consumes `ng:finite-word`

Only `ng:local-front-bound` **edges** it in the ruler's leaf table (`DAG.md`
"consumer | leaf": the single row `ng:local-front-bound | ng:finite-word`).
Grep finds five `\ref{ng:finite-word}` in `sm-3-statesum.tex` — :2295 (the
block's own negative-scope paragraph), :2311 and :3387 (status tags), :2323
(inside `ng:local-front-bound`'s proof, the edge) and :3374 (prose between
`src:contact` and `fd:ng-bound`, which the ruler does not edge).
The other rows below are named because this seat's charter names them and
because they carry the symbols the L-4 export is written in.

| item | SM locator | what it is | tag on SM6 |
|---|---|---|---|
| `ng:front-domain` | `sm-3`:1825–1841, PDF p. 71 | the **domain**: actual map of a nonempty finite union of parameter circles; finitely many transverse double points and ordinary semicubical cusps; no other singularities; no vertical tangency on a regular arc; $x''(0)\neq0$ at every cusp; cusps meet no other strand; smaller-$dz/dx$ branch over; downward cusp = upper arm to lower arm; defines $D(F)$, $w(F)$, $s(F)$ and the rounding $S(F)$ | definition (no tag; the legend tags only definition-free statements) |
| `ng:smoothing-record` | `sm-3`:1843–1851, proof to :1863, PDF p. 71 | any two roundings $S(F)$ have the same full named record, so $P_{S(F)}$ is rounding-independent | `new (round~5: … F-25-136)` |
| `def:adeg` | `sm-3`:1887–1892, PDF p. 72 (printed as **Definition 3.35, "degrees in $a$"**) | for nonzero $f\in\ZZ[z^{\pm1}][a^{\pm1}]$: $\deg_af=\max\deg_af$ the largest $a$-exponent with nonzero coefficient, $\mindeg_af$ the smallest | definition |
| `ng:defect` display | `sm-3`:1894–1899 | $d(F)=\deg_aP_{S(F)}$, $B(F)=D(F)-w(F)-d(F)-1$ | — |
| `ng:deletions` | `sm-3`:2007–2012, proof to :2043, PDF p. 73 | **"Deleting an empty zigzag lowers $s$ by two and cannot increase $B$; applying the crossed-cusp shortcut lowers $s$ by one and cannot increase $B$."** Proof displays `ng:zigzag-counts` ($\Delta w=\Delta d=0$, $\Delta D\in\{0,-2\}$) and `ng:crossed-cusp-counts` ($\Delta d=0$, $\Delta w=1$, $\Delta B\in\{-2,0\}$), each followed by its $s$ sentence | `transcribed (unrefereed): RC ng_front (C029); round~5: the $s$ consequence of both branches carried into the statement …, F-25-142` — **held** |
| `ng:cusp-skein` | `sm-3`:2075–2082, proof to :2164, PDF p. 74 | for either principal direction, $B$ of the earlier branch $\ge\min(B(\text{other principal}),B(\text{compatible smoothing}))$; the smoothing has one fewer singularity, the principal branches the same | `proved (refereed: bench A, 2026-09-05T15:51:04Z; transcribed from RC ng_front (C029))` |
| `ng:local-front-bound` | `sm-3`:2304–2312, proof to :2347, PDF p. 77 | $w(F)-D(F)\le-\deg_aP_{S(F)}-1$ for **every** front on the domain | `transcribed (unrefereed): RC ng:local-front-bound (C029); consumes Literature input ng:finite-word; cleared by bench A on SM2 … and again on SM5 … before the round-5 citation of ng:smoothing-record` — **reverted to held by the round-5 touch** |
| `fd:ng-bound` | `sm-3`:3377–3388, proof to :3397, PDF p. 91 | **the self-linking form.** Hypothesis: *"Let $F$ be a front on the domain of Definition `ng:front-domain`, with $c_\downarrow(F)=D(F)$ … and let $S(F)$ be an actual clean ordinary cusp smoothing"*. Conclusion, display `fd:ng-input`: $sl_{\rm Ng}(F):=w(F)-c_\downarrow(F)\le-\max\deg_aP_{S(F)}(a,z)-1$. Closing sentence: *"This is not an application of an ambient-invariant hypothesis to the local diagram construction, nor a maximum over front representatives."* | `new (round~3 …; F-25-107; round~5: ng:smoothing-record cited …, F-25-136)` |
| `ng:consumer-boundary` | `sm-3`:2349–2359 | the remark that `ng:local-front-bound` is *only* a polynomial inequality for one front, that Etnyre's separate local formula does the $sl$ identification, and that the endpoint polynomial comparison is separate and consumes the global HOMFLY premise | remark |

**`fd:ng-bound`'s domain hypothesis.** Every clause of `ng:front-domain` is a
hypothesis on $F$; the lemma is stated so that a consumer must discharge it.
This is the obligation F-25-153 named.

---

## 3. The consumer — `fd:contact`, and the discharge of `fd:ng-bound`'s hypothesis

`fd:contact` (`sm-3`:3402–3421, proof :3423–3496, PDF p. 92) is where L-4
leaves the `ng:` subsection. The relevant proof passage is **`sm-3`:3455–3470**:

> Fix $T$ with the stated finite ordinary generic diagram $D_T$.
> Lemma `fd:transverse-neighborhood` gives the original Legendrian helix $L$
> and a chosen positive pushoff transversely isotopic to $T$. Let $\Phi_s$ be
> the ambient contact isotopy of Theorem `fd:generic-front`; write
> $L_T=\Phi_1\circ L$ and let $F_T$ be its finite generic front, with the exact
> cusp germs `cp:exact-cusp`. … **The front $F_T$ lies on the domain of
> Definition `ng:front-domain`:** Theorem `fd:generic-front` gives finitely many
> semicubical cusps with the germ `cp:exact-cusp`, whose $x''(0)=2A\neq0$,
> transverse double points, no triple point and no cusp on another branch, and
> Legendrianity $z'=yx'$ makes the front tangent vanish wherever $x'=0$, so that
> every such point is one of these cusps and no regular arc has a vertical
> tangency. **Lemma `fd:ng-bound`, applied to $F_T$,** bounds it by
> $-\max\deg_aP_{S(F_T)}-1$.

Clause-by-clause discharge, against `ng:front-domain`'s own list:

| hypothesis of `ng:front-domain` | discharged by | at |
|---|---|---|
| nonempty finite union of parameter circles | $L_T$ is an embedded circle | :3456–3458 |
| finitely many transverse double points, ordinary semicubical cusps, no other singularities | `fd:generic-front`'s conclusion, quoted | :3461–3464 |
| $x''(0)\neq0$ at every cusp | the exact germ `cp:exact-cusp`, $x''(0)=2A\neq0$ | :3462–3463 |
| cusps meet no other strand or singularity | "no triple point and no cusp on another branch" | :3463–3464 |
| no vertical tangency on a regular arc | Legendrianity $z'=yx'$ argument | :3464–3467 |
| smaller-$dz/dx$ branch over | proved in the same proof's first paragraph (smaller $y$ over; *"For a Legendrian front this is also the smaller-slope rule $y=dz/dx$"*) | :3428–3432 |

**Verdict on the hop: the hypothesis is discharged, and the lemma is cited by
label.** The round-3 defect F-25-107 (the bound taken from a bare display
outside every environment) and the round-5 defect F-25-153 (the hypothesis
created by that repair, never discharged) are both **addressed at these bytes**;
the ruler now edges `fd:contact → fd:ng-bound → ng:local-front-bound →
ng:finite-word` (`DAG.md`:292, :300).

`fd:contact`'s own conclusion, display `fd:representative-bound` (:3414–3417),
is $sl(T)\le-\max\deg_aP_T(a,z)-1$ for an individual positive transverse knot
with a finite ordinary generic specified diagram. The step from
$sl_{\rm Ng}(F_T)$ to $sl(T)$ is `fd:linking-calculus` plus the cusp algebra
$tb-r=w-D=sl_{\rm Ng}(F)$ (:3446–3452), which consumes `src:contact` — L-3.

---

## 4. The registry entry — `sm-11-registry.tex`:255–316, PDF p. 191

Structure, and what each part claims:

| part | lines | claim | checked at |
|---|---|---|---|
| title + interface | 255–265 | `ng:finite-word` is *"this entry's whole literature interface"*; Ng pp. 6–8 + Fig. 1 (his Lemma 1, attributed to Rutherford's Lemma 3.3 of the published version) and Rutherford Lemma 3.2 pp. 8–12 arXiv (statement p. 9, proof pp. 10–12) *"supply the finite constructive reduction"* | **accurate** — §1 above |
| internal chain + clearance | 262–266 | the local arguments are printed in `ng:local-front-bound` and predecessors (round 1, from RC `ng:local-front-bound`); *"the theorem and the front lemmas cleared by bench A, Lemma `ng:deletions` held"* | front lemmas: **accurate** (six `proved (refereed: bench A, 2026-09-05T15:51:04Z)` tags); `ng:deletions`: **accurate** (held); **the theorem's clearance is stale** — see `RECOMMENDATION.md` §3 (O-3) |
| index defects | 266–269 | the malformed strings and their typed corrections are disclosed at the block, and the SM2 seat verified the disclosure at the source's bytes (F-25-85) | **re-verified independently**, `T2_DELTA.md` §3 |
| width disclosure | 269–274 | *"wider than either printed source sentence in three disclosed ways"* (seat R6; F-25-83) | **accurate**, §1 above |
| **"What the internal derivation buys" (R-25-13)** | 275–283 | `ng:local-front-bound`, *"resting on the source fact Literature input `ng:finite-word`"*, is a per-front polynomial inequality; it *"removes the maximization over Legendrian representatives and every ambient-invariance premise, and narrows the literature dependence of this entry to the finite Ng–Rutherford word procedure together with the L-1 polynomial interface; it does not remove Ng and Rutherford from the trusted base"* | **R-25-13 satisfied in form and in substance**: "resting on <sourcefact>" + what it buys + the explicit non-removal; and the phrase "T3 available" does not occur (§5) |
| SM1 seam closed | 283–292 | F-25-51's seam is *"structurally absent"*; the bridge is constructed in `fd:transverse-neighborhood` (cleared); the published statement of record for that step is quoted and attributed to `\cite[Section~2.9, Lemma~2.22, equation~(17)]{Etnyre}`; it stays flagged for source cross-check under rule 8 | the *structure* claim is **accurate**; the **locator is wrong** — see `T1_STATEMENT.md` §4 and finding **X-1** |
| roles of the other sources | 292–307 | Ng §1.1 display + Cor. 1 (proved p. 8 from Thm 1) bounds the maximum over Legendrian realizations, Ng's $(a,z)$ = `lit:homfly` verbatim, consumed by no proof; Morton Thm 1 + Cor 1 proves the polynomial half for any diagram in $v=a^{-1}$, consumed by no proof; Bennequin Thm 3 is the Euler-characteristic form, not consumed; Franks–Williams is the braid case Morton subsumes and attributes, unfetched (E-25-2, not blocking) | **every clause accurate**, all four checked at the sources this pass except Bennequin (not re-read; the L-4 seat's reading, cited as theirs) — `T1_STATEMENT.md` §§2–3 |
| provenance withdrawal | 300–304 | SM1's *"audited at the root, Phase 1.99"* is withdrawn; the proof readings on record are seat L-4's and the SM2 seat's, *"the seats' claims"* | **accurate**; F-25-51's R5 satisfied and correctly deflated |
| consumption + closure | 304–311 | consumed by `fd:contact`, hence `thm:floor`, through `fd:ng-bound`; the closure of `thm:floor` *"now contains Theorem `ng:local-front-bound` and Literature input `ng:finite-word` (**33 statements**; declared inputs `lit:homfly`, `lp:lm`, `lp:lm-uniqueness`, `ng:finite-word`, `src:contact`; F-25-107)"* | consumption and input list **accurate**; **the count 33 is stale** — SM6's own `DAG.md`:5 reads **38** — finding **X-2** |
| audit record | 311–316 | seat L-4 (below T2 as SM1 registered it, one published sentence fixing it); seat L-3/L-4 on SM2 (T2 on the printed route, R6/R7/R8 taken, R6 in round 3 inside the block); E-25-5 optional operator fetch | **accurate**; R6, R7, R8 verified present |

---

## 5. "T3 available" — the R-25-13 check

Grep over `sm-*.tex`, `README.md`, `DAG.md`, `DISCREPANCIES.md` of SM6 for the
string `T3`: **four hits, none of them a claim.**

* `sm-11-registry.tex`:10–13 — the preamble states the rule itself: *"no Lean
  formalization or formal T3 certificate is claimed (operator ruling R-25-2),
  and the words ``T3 available'' are not used: an internal derivation resting
  on a declared source fact is described as such, with what it buys (ruling
  R-25-13)."*
* `sm-11-registry.tex`:142 — L-2, disclaiming: *"it is an internal printed
  proof, not a ``T3'' (R-25-13; F-25-62)"*.
* `sm-11-registry.tex`:246 — inside L-3, reporting a seat's verdict (*"no
  ``T3'' for L-3"*).

**The phrase "T3 available" occurs nowhere in frame SM6.** F-25-52 and
F-25-56's registry half are satisfied at the exit frame's bytes.

---

## 6. Tally

| bucket | count |
|---|---|
| literature environments carrying L-4 | **1** (`ng:finite-word`) |
| published statements L-4 puts into a proof | **1** (Ng's Lemma 1 / Rutherford's Lemma 3.2, statement (A), as consolidated) |
| SM statements consuming it, directly or transitively | 3 (`ng:local-front-bound` → `fd:ng-bound` → `fd:contact`), plus `thm:floor` through `cf:thm-carrierfloor`(C) |
| sources named in L-4 and consumed by **no** proof (grep-confirmed) | Morton, Bennequin, Franks–Williams, and Ng's Thm 1 / Cor 1 / $\overline{sl}$ |
| L-4 sources blocked | 1 (Franks–Williams, E-25-2) + 1 optional version (IMRN Rutherford, E-25-5) |
| "T3 available" occurrences | **0** |
