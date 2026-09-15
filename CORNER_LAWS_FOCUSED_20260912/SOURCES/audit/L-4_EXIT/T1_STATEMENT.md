# L-4 EXIT — T1: what stands at each cited locator, against what SM6 writes

T1 = the source's full text on disk, hashed, and **the statement at the cited
locator says exactly what the manuscript uses** — objects, quantifiers,
hypotheses, conclusion, and here also the polynomial normalization. Frame SM6
verified 20/20 first. Stamp 2026-09-06T01:56:55Z. Extractions and renders are
this seat's own (`work/`); where a reading is another seat's it is named as
theirs.

---

## 1. Ng, pp. 6–8 + Figure 1 — the consumed item

**File** `ng_skein_bennequin_author.pdf`, sha256 `5e57702f…d5df920`; identical
in content and pagination to the shared copy `e385326c…9145a3`, which carries
the stamp *arXiv:0709.2141v1 [math.GT] 13 Sep 2007*
(`work/ng_two_copies.diff`).

### 1.1 The statement at the locator, verbatim (p. 6)

> **Lemma 1 (Rutherford [23], Lemma 3.3).** Via skein crossing changes,
> Legendrian isotopy, Legendrian destabilization, and the removal of trivial
> unknots, we can turn $F$ into a front which either has lower $s$, or the same
> $s$ and lower $s'$.

immediately preceded, on the same page, by the definitions the lemma is stated
in — $s(F)$ = the total number of singularities (crossings and cusps),
$s'(F)$ = *"the number of singularities to the right of the rightmost left
cusp of $F$"* — and followed by

> For completeness, we sketch here the proof of the lemma. Consider the portion
> of $F$ immediately to the right of the rightmost left cusp of $F$. By using
> Legendrian Reidemeister moves II and III if necessary, we can assume that
> this portion of $F$ has one of the forms shown on the left hand side of
> [Figure 1].

**Figure 1 is on p. 7**, captioned *"Inductively simplifying fronts. Solid
arrows denote skein crossing changes; dashed arrows denote destabilizations or
deletions of trivial unknots; equalities denote Legendrian isotopies. For each
of the initial fronts (left column), the rightmost left cusp in the front is
the unique left cusp depicted."* **p. 8** closes it: *"In each case, the use of
skein crossing changes, Legendrian isotopy, Legendrian destabilization, and/or
the removal of trivial unknots yields a simpler front (one with lower $s$, or
the same $s$ and lower $s'$). The lemma, and Theorem 2, follows."*

### 1.2 Clause-by-clause against `ng:finite-word` (`sm-3`:2169–2205)

| clause | SM6 | Ng pp. 6–8 | match |
|---|---|---|---|
| the moves allowed | typed commutations + three local front moves; cusp-skein interchange; zigzag deletion / crossed-cusp shortcut / standard-circle deletion | skein crossing changes, Legendrian isotopy, Legendrian destabilization, removal of trivial unknots | **same list, differently named**; the crossed-cusp shortcut is SM6's, disclosed |
| what one application yields | *"Stop at the first strict decrease of $s$ … Before that decrease the selected procedure does not increase $s$"* | *"lower $s$, or the same $s$ and lower $s'$"* | **SM6 is a chain, Ng is a step** — disclosed at :2198–2200 |
| the secondary measure | *"Secondary progress is measured at the boundaries of complete finite blocks … a completed nonterminal block moves a singularity to the left of the selected rightmost left cusp"* | $s'$, *"the number of singularities to the right of the rightmost left cusp"* | **same measure**, SM6 coarser (block boundaries, not every elementary move — SM6 says so) |
| arm-string extension | *"bounded by the active strand count"* | not in Ng (it is Rutherford's, asserted) | **supplied by SM6** — disclosed |
| smoothing branch | *"At each cusp-skein interchange, the compatible smoothing branch has smaller $s$ than the front at that stage"* | p. 6: *"the last two of the resulting fronts have lower $s$ than $F$, … while the first has the same $s$"*; p. 8 in the oriented case: *"we can successively replace it by … and whichever of … inherits an orientation from $F$, to obtain two new fronts"* | **in Ng** |
| the domain | `ng:front-domain` (finite, semicubical cusps, no vertical tangency, $x''(0)\neq0$, cusps clean) | p. 1: fronts are *"oriented closed curves with no vertical tangencies, whose only singularities are transverse double points and semicubical cusps"* | **compatible**; SM6 adds the cusp non-degeneracy and cleanliness it needs |

**T1 on the consumed item: met at the corrected reading SM6 itself prints.**
The block does not claim Ng's sentence; it claims *"the source's finite descent,
not its printed sentence"*, and names the three departures. That is the honest
form, and each departure is verified in `CONSUMPTION_MAP.md` §1.

### 1.3 What Ng's §1.1, Theorem 1 and Corollary 1 say — consumed by no proof of SM6

Registry L-4 (`sm-11`:292–296) describes these as background roles. Checked at
the bytes:

* **p. 2**, definition: *"For a topological link $L$, define the maximal
  Thurston–Bennequin number $\overline{tb}(L)$ (respectively maximal
  self-linking number $\overline{sl}(L)$) to be the maximum tb (respectively
  sl) over all Legendrian realizations of $L$."* The overline is dropped by the
  text layer; **confirmed on the page rendered at 3x** (`work/ng_p2_box.png`)
  in both the definition and the boxed list.
* **p. 2**, the boxed list, fifth line:
  $\overline{sl}(K)\le-\text{max-deg}_a P(K)(a,z)-1$, tagged *"(HOMFLY-PT bound
  [7, 13])"*, with **[7] = Franks–Williams** and **[13] = Morton** (reference
  list, pp. 14–15, read).
* **p. 3**, **Theorem 1**: a template about an abstract $\mathbb Z$-valued
  invariant $i$ of oriented links with conditions (a) and (b); it names **no
  polynomial and no degree**. **Corollary 1** (p. 3): *"The HOMFLY-PT and
  HOMFLY-PT homology bounds on $\overline{sl}$ hold for oriented links."*
* **p. 8**, *Proof of Corollary 1*: *"Define $i(L) = \max\text{-deg}_a
  P(L)(a,z)+1$. By the skein relation and normalization for the HOMFLY-PT
  polynomial, the conditions in Theorem 1 hold, and Theorem 1 then gives the
  HOMFLY-PT bound."*
* **p. 5, §1.2**: *"$P(K)(a,z)$ is the HOMFLY-PT polynomial of $K$, normalized
  so that $P=1$ for the unknot and $aP(L_+)-a^{-1}P(L_-)=zP(L_0)$."*

Against SM6's `lit:homfly` (`sm-3`:916–922): *"takes the value 1 on the
crossing-free circle, and satisfies $aH_{D_+}-a^{-1}H_{D_-}=zH_{D_0}$"*.
**Identical, in the same letters $a$ and $z$, with no conversion and no mirror.**
Registry L-4's *"Ng's $(a,z)$ is that of Literature input `lit:homfly`
verbatim"* is **accurate at the bytes**, verified here and not inherited.

Registry L-4's *"his Corollary 1 proved on p. 8 from his Theorem 1, bounds the
maximum over Legendrian realizations"* is **accurate**.

---

## 2. Rutherford, arXiv v1, Lemma 3.2 — the root

**File** `rutherford_2006.pdf`, sha256 `024dc444…f8c33476`, 17 pp.

### 2.1 The statement, verbatim (p. 9, foot)

> **Lemma 3.2** By repeated evaluation of the skein relation a formula for
> $R_K$ can be found in terms of the $R$ polynomials of Legendrian links with
> less crossings and links whose values are specified by (ii).

The proof (**pp. 10–12**) opens by reducing the lemma to a purely combinatorial
statement, which is the part SM6 imports:

> (A) By substituting into the above relations corresponding to Legendrian
> isotopy and interchanging $l_{m+1}\sigma_m$ and $l_m\sigma_{m+1}$, $W$ may be
> reduced to a word with less crossings or to a word whose $R$ polynomial is
> known by (ii).

**This is the T1-relevant fact and SM6 states it correctly**: the *printed
conclusion* of Lemma 3.2 is about the **ruling polynomial** $R_K$; what SM6
imports is **statement (A)**, the content of the proof. SM6 says so at
:2293–2297 (*"No Rutherford ruling or Kauffman value … is consumed. Literature
input `ng:finite-word` is precisely the local constructive portion of those
proofs."*).

### 2.2 The word setting, at the bytes (p. 9)

The generators $\sigma_m$, $l_m$, $r_m$ with the planar-isotopy relations, the
Type 1/2/3 Legendrian Reidemeister relations, and the skein relations (i)–(iii)
— including **(ii)** $R_{\ldots l_mr_{m\mp1}\ldots}=0$,
$R_{\ldots\sigma_ir_i\ldots}=R_{\ldots l_i\sigma_i\ldots}=0$, which is what the
two terminal branches evaluate. SM6's arm-string notation
$(\sigma_{m-1}\cdots\sigma_{m-N_1})(\sigma_{m+1}\cdots\sigma_{m+N_2})$ at
:2210–2213 is Rutherford's, p. 10, verbatim, as is the decomposition
$W=Xl_mY$ *"where $Y$ is a word in the $\sigma_i$ and $r_i$"*.

**T1 met** for the imported content at the corrected locator, with the caveat
SM6 itself prints: the imported *statement* is the SM's consolidation of the
source's proof, not the source's printed sentence.

---

## 3. Morton — the role clause of registry L-4

**File** `morton_1986.pdf`, sha256 `bc91a638…dd4ee310`, 3 pp. (publisher scan;
OCR mangles the displays, so the skein and Theorem 1 were **rendered at 3x**
and read as images: `work/morton_p1_skein2.png`).

* Header, p. 107: *Math. Proc. Camb. Phil. Soc.* (1986), **99**, 107.
* Skein, rendered: $\dfrac{1}{v}P_{K^+} - vP_{K^-} = zP_{K^0}$ $(*)$.
* **Theorem 1** (p. 107): *"For any diagram $D$ of $K$,
  $\tilde c(D)-(s(D)-1)\le e\le E\le\tilde c(D)+(s(D)-1)$"*, where $[e,E]$ is
  the $v$-range of $P_K$, $\tilde c=c^+-c^-$ and $s$ = number of Seifert circles.
* **Corollary 1** (p. 108), attributed *"[5], [2]"*, the closed-braid case.
* References, p. 109: **"[2] J. FRANKS and R. F. WILLIAMS. Braids and the Jones
  polynomial. (Preprint 1985)."**

Comparing $(*)$ with `lit:homfly`'s $aH_+-a^{-1}H_-=zH_0$ gives $v^{-1}=a$, i.e.
**$v=a^{-1}$, $z=z$, with no mirror and no sign twist**.

Registry L-4's three Morton clauses — *"proves the polynomial half for any
diagram"*, *"in $v=a^{-1}$"*, and *"Franks–Williams is the braid case that
Morton's Theorem 1 subsumes and attributes"* — are each **accurate at Morton's
own bytes**. The full proof reading is the **L-4 seat's** (`L-4/T2_PROOF.md`),
cited as theirs; this seat read the statements, the dictionary and the
reference list only.

**Bennequin** was not re-read here; SM6 consumes it in no proof and the
statement reading on record is the L-4 seat's.

---

## 4. Etnyre — the two clauses in this seat's charge

**File** `etnyre_legendrian_transversal_survey.pdf`, sha256
`34826016…dc4ac8f1`.

### 4.1 Equation (9), §2.6.4, p. 15 — as a *statement* (the L-3 interface's
front-writhe clause, named in this seat's charter)

Verbatim at the locator:

> **2.6.4. Computations of the self-linking number.** To compute $sl(T)$ for a
> transverse knot in the standard contact structure on $\mathbb R^3$ note that
> the vector $v=\frac{\partial}{\partial y}$ is always in $\xi_{std}$ and thus
> can be used to trivialize $\xi_{std}$ independent of a Seifert surface for
> $T$. Now let $T'$ be a copy of $T$ obtained by pushing $T$ along $v$. The
> self-linking number of $T$ is the linking number of $T$ and $T'$. If we
> consider $T$ and $T'$ in the "front projection" we see that
> $$(9)\qquad sl(T)=\mathrm{writhe}(\Pi(L)).$$
> The argument for this formula is exactly like the one for Equation (8).

**Three facts of record, reproduced independently here** (this is the third
independent extraction in the campaign to show them, after the L-3 seat's and
the SM2 seat's): the **misprint $\Pi(L)$ for $\Pi(T)$**; **no stated
hypothesis** on the front; and **no proof at the locator** — the one-line
deferral is to eq. (8), which is the **Lagrangian** formula
$tb(L)=\mathrm{writhe}(\pi(L))$ (p. 14), whose own justification (p. 15) is
*"In the Lagrangian projection think about trying to pull $L'$ straight up."*
The front $tb$ formula, eq. (7) p. 14, carries the $-\frac12\#\text{cusps}$
correction that eq. (8) does not.

SM6's `src:contact` (:3358–3363) prints exactly the right thing about it:
Geiges arXiv Lemma 3.3 p. 46 and the book Prop. 3.5.32 p. 127 are named as the
**printed proofs**, and *"Etnyre's equation (9), Section 2.6.4, **states** it"*.
**T1 met, with the source's defects disclosed; the T2 witness is elsewhere and
is cited.** (The depth verdict on L-3 belongs to the L-3 exit seat.)

### 4.2 Section 2.9, Lemma 2.22, equation (17), p. 19 — and the bridge

Verbatim:

> **Lemma 2.22.** The invariants of Legendrian knots and their transverse push
> offs are related by
> $$(17)\qquad sl(T_\pm(L))=tb(L)\mp r(L).$$

followed by a printed proof (the $t(\cdot,\cdot,\cdot)$ twisting computation).

**This is the invariant relation, not the bridge.** The statement registry L-4
quotes — *"every transverse knot is transversely isotopic to the positive
transverse pushoff of a Legendrian knot"* — is **not** at Lemma 2.22 and not in
eq. (17). It is on the **next page**, still in §2.9, in the Legendrian-push-off
paragraph, **p. 20**:

> A standard application of Moser's technique shows that the transverse knots
> $T$ has a neighborhood $N$ contactomorphic to $S_a$ for some $a$. … Let $T_l$
> be a leaf in the foliation of $T_b$. It is easy to see that $T_l$ is a
> Legendrian knot topologically isotopic to $T$. The Legendrian knot $T_l$ is
> called a Legendrian push off of $T$. **By considering the obvious annulus
> between $T$ and $T_l$ it is easy to see that the positive transverse push off
> of $T_l$ is $T$.**

and, restated after Theorem 2.23 on the same page:

> **Since we know all transverse knots are the transverse push off of some
> Legendrian knot**, the classification of transversal knots is equivalent to
> the classification of Legendrian knots up to negative stabilization.

**Finding X-1 (locator, editorial). Two sites.**
`sm-11-registry.tex`:283–287 (registry L-4) attributes the quoted bridge
statement to `\cite[Section~2.9, Lemma~2.22, equation~(17)]{Etnyre}`; and
`sm-11-registry.tex`:876–878 (the §11 rule-8 flagged list) repeats the pairing:
*"Flagged for source cross-check under rule 8: … Lemma `fd:transverse-neighborhood`'s
construction (**against Etnyre's Lemma 2.22**)"*.
**The section is right and the sub-locator is wrong**:
Lemma 2.22 / eq. (17) is $sl(T_\pm(L))=tb(L)\mp r(L)$. The correct sub-locator
is Etnyre §2.9, **p. 20**, the Legendrian-push-off paragraph (and the sentence
after Theorem 2.23). *Provenance, so no one bench is blamed:* the wording came
from the L-4 seat's repair R1, which paired the bridge with "Lemma 2.22,
eq. (17)" for the **sign** convention, and the author bench transcribed the pair
as one locator. Nothing mathematical turns on it — SM6 **constructs** the bridge
internally (`fd:transverse-neighborhood`, cleared) and cites Etnyre only as the
rule-8 cross-check target — but a rule-8 cross-check pointed at the wrong
sentence cannot be performed as written. **Severity: editorial (locator).**
Repair: one clause; wording in `RECOMMENDATION.md` §3.

*(Note, not a finding: the same `\cite[… Section~2.9, Lemma~2.22,
equation~(17)]{Etnyre}` inside `src:contact` (`sm-3`:3345) and registry L-3
(`sm-11`:175) is **correct** there — it is cited for
$sl(T_+(L))=tb(L)-r(L)$, which is exactly eq. (17). Only L-4's reuse of the
locator for a different sentence, at the two sites above, is wrong.)*

---

## 5. Bibliography hygiene — finding X-3

`sm-refs.bib` (sha256 `17277432…d1246e04`), entry as printed:

```
@article{Ng, author={Ng, Lenhard}, title={A skein approach to {B}ennequin type
  inequalities}, journal={Int. Math. Res. Not. IMRN}, year={2008},
  note={article rnn116}}
```

The three other entries whose locators resolve on a preprint each carry a
version note, and the campaign added two of them in response to filed findings:

* `Etnyre`: *"arXiv:math/0306256; the locators cited in this document were
  verified on arXiv version v2 (22 November 2004), the copy on file, and not on
  the Handbook printing"* (added after **F-25-84**);
* `Rutherford`: *"Retained arXiv:math/0511097v1, 4 November 2005"*;
* `GeigesContact`: *"Retained arXiv:math/0307242v2 …; all cited locators refer
  to this 86-page version"*.

**`Ng` carries none.** Yet every Ng locator in SM6 — `\cite[pp.~6--8 and
Figure~1]{Ng}` at `sm-3`:2172 and `sm-11`:257, and the §1.1/Cor. 1/p. 8
locators in registry L-4's roles paragraph — resolves on the **15-page author
preprint, arXiv:0709.2141v1 (13 Sep 2007)**, whose page numbers are its own and
need not be the IMRN 2008 printing's. The stamp is in the retained file itself.
**Severity: editorial (bibliography), same class as the repaired F-25-84.**
Repair: one `note={}` field.

---

## 6. T1 verdict

| item | locator SM6 prints | T1 |
|---|---|---|
| the consumed finite descent | Ng pp. 6–8 + Fig. 1; Rutherford Lemma 3.2, pp. 8–12 arXiv (registry: statement p. 9, proof pp. 10–12) | **met**, with SM6's own three-way width disclosure, each clause verified |
| Ng §1.1 display / Cor. 1 (background role) | Ng §1.1, Cor. 1 proved p. 8 from Thm 1 | **met** |
| the normalization identity to `lit:homfly` | Ng §1.2, p. 5 | **met, verbatim** |
| Morton's polynomial half (background role) | Morton Thm 1 + Cor 1, $v=a^{-1}$ | **met** |
| Franks–Williams' role | Morton p. 108 attribution | **met at Morton**; the source itself is blocked (E-25-2) |
| the transverse↔Legendrian bridge (rule-8 cross-check target) | Etnyre §2.9, **Lemma 2.22, eq. (17)** | **NOT met at the printed sub-locator** (X-1); met at Etnyre §2.9, p. 20 |
| Etnyre eq. (9) as a *statement* | Etnyre §2.6.4, eq. (9), p. 15 | **met as a statement**, with the misprint and the missing hypothesis disclosed by SM6 |
| bibliography resolution for every Ng locator | `@article{Ng}`, IMRN 2008 | **version note missing** (X-3) |
