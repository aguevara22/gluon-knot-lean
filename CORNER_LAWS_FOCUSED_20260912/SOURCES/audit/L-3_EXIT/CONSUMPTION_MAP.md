# L-3 EXIT — CONSUMPTION MAP on frame SM6

Every statement the **exit frame** consumes from literature input L-3, with the
SM locator and the source locator. Frame SM6, manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`, 20/20
verified. Stamp 2026-09-06T01:56:31Z.

Frame file hashes for the two files that carry every byte below:

```
8785877b7de6bacc9bc620215ca5dc7d5fd366156a89802d6aa6c15279e11129  sm-3-statesum.tex
751fd3e09d1505b448f70c54bdebe56149db2d557bb4575e74409d78d6820077  sm-11-registry.tex
17277432deb730dfd2ae9264038dd36637be5b2eb54ff5cc33eeea34d1246e04  sm-refs.bib
```

Block hashes (sha256 of the exact line range, trailing newline included):

| block | SM6 locator | sha256 |
|---|---|---|
| `def:transverse-front` | sm-3:3326–3337 | `d7b3c69396d666caa0e5e4640d9b0759f19b3e260f981ba01443236fb0bed4e1` |
| `src:contact` (whole `literature` env) | sm-3:3339–3363 | `3245c0777e30c29190f241cef96333264bd87281a848bdb2dfc7f8c9d0387c2c` |
| `rem:sl-convention` | sm-3:3010–3021 | `21997b72ba61cb260af2c1c6e9922ebd5062d454bc0a34b8ed7c1fd9f238b7e1` |
| `fd:linking-calculus` statement | sm-3:2783–2825 | `0afdb6e8e76390ca0642a18f131df6f379d7ef36cfe24bf56244c47ca4a0ebc1` |
| `fd:contact` statement | sm-3:3403–3421 | `420e9b9b78b2bd31c36fcb27d7af9d8228e87ee8305415f6693bd1bf1408e3c4` |
| `fd:contact` proof | sm-3:3425–3496 | `551ed30128bd4ef32ac0cb05228a6a210b3b59570fd670060faeef07c064fa36` |
| registry entry **L-3** (`reg:etnyre`) | sm-11:173–253 | `ae38cae90397773b399cc427a3bd1a3a92131a157e49943367338746735006d7` |

---

## 0. Where L-3 enters the frame, structurally

`src:contact` is the **only** literature environment of L-3 on SM6
(`\label{src:contact}` at sm-3:3339). The frame's own instrument
(`DAG.md`, sha256 `f4f4ecddaef16db062852f1435626076accdeacbbae7b3d31487d71b24b81cce`)
records exactly one consumer edge for it:

```
DAG.md:304   | `fd:contact` | `src:contact` |
```

`fd:contact` in turn lies in the declared closure of `thm:comparison`
(116 statements, inputs `{hyp:R, lit:homfly, lp:lm, lp:lm-uniqueness,
ng:finite-word, src:contact}`) and of `thm:floor` (38 statements, five
literature inputs) — DAG.md:5. So **L-3 reaches the main results through one
theorem, `fd:contact`, and through nothing else.**

Citation inventory across the whole frame (grep on the twelve `.tex` files):
`Geiges` 4, `GeigesContact` 6, `Etnyre` 5, `DeTurckGluckLinking` 2. Of these,
the L-3 consuming sites are sm-3:3342, 3344–3346, 3353–3354, 3358–3359
(inside `src:contact`), sm-3:3013, 3015 (inside `rem:sl-convention`) and
sm-11:174, 186, 198 (registry L-3). sm-3:2372 (`GeigesContact` Thm 2.32 /
Ex. 2.33) and sm-11:237 are *comparison* citations in the provenance
paragraph, not premises.

---

## 1. `src:contact` — the literature block (sm-3:3339–3363)

### 1.1 The convention sentence, sm-3:3340–3343

> Use standard contact space $(\RR^3,\ker(dz-y\,dx))$, with positive
> transverse orientation $z'-yx'>0$ (Etnyre~\cite[Sections~2.1 and~2.4]{Etnyre}
> for the conventions).

| what is consumed | source locator | at the bytes |
|---|---|---|
| $\xi_{\rm std}=\ker(dz-y\,dx)$ on $\RR^3$ | **Etnyre §2.1, p. 4** | **exact.** "$\xi_{std} = \mathrm{span}\{\partial_y,\ \partial_x + y\partial_z\}$ … Clearly $\xi_{std}$ is the kernel of the 1–form $\alpha = dz - y\,dx$". |
| "positive transverse" | **Etnyre §2.4, p. 10** | **present, in words not coordinates.** "if $T$ is transverse to $\xi$ we can orient $T$ so that it always intersects $\xi$ positively. When $T$ is so oriented we call $T$ a positive transverse knot." Etnyre does **not** print the inequality $z'-yx'>0$; the SM writes it out from §2.1 + §2.4. That step is one substitution, $\alpha(T')>0$, and is correct. Recorded as a (correct) SM derivation from the two cited sections, not as a quoted source sentence. |
| the front page is $(x,z)$ | **Etnyre §2.4, p. 10** | **exact.** "Transverse knots are usually studied via the analogy of the front projection: $\Pi:\RR^3\to\RR^2:(x,y,z)\mapsto(x,z)$." |

### 1.2 The display `fd:contact-inputs`, sm-3:3349–3352

> $r=\frac{D-U}{2},\qquad tb=w-\frac{D+U}{2},\qquad sl(T_+(L))=tb(L)-r(L).$

cited at sm-3:3344–3346 to
`\cite[Section~2.6.2, equations~(5) and~(7); Section~2.6.4, equation~(9);
Section~2.9, Lemma~2.22, equation~(17)]{Etnyre}`, "for an oriented Legendrian
front with downward and upward cusp counts $D,U$".

| formula | source locator | at the bytes | depth reached (see `T2_DELTA.md`) |
|---|---|---|---|
| $r=(D-U)/2$ | **Etnyre eq. (5), §2.6.2, p. 14** | **exact.** "$r(L)=\frac12(D-U)$, where $U$ is the number of up cusps in the front projection and $D$ is the number of down cusps." | **T2** (printed argument at the locator, read; one "one may easily check" clause inside it) |
| $tb=w-(D+U)/2$ | **Etnyre eq. (7), §2.6.2, p. 14** — and, for the printed proof, **Geiges book Prop. 3.5.9, p. 117** (cited at sm-3:3353–3354) | **exact at both.** Etnyre: "$tb(L)=\mathrm{writhe}(\Pi(L))-\frac12(\text{number of cusps in }\Pi(L))$". Geiges: "$\mathtt{tb}(K)=\mathrm{writhe}(K_F)-\frac12\#(\mathrm{cusps}(K_F))$" (glyph-verified on the rendered page). | **T2 through Geiges only.** Etnyre eq. (7) reduces to his Remark 2.14, p. 13, which is **stated there with no proof and no reference** — confirmed at the bytes. |
| $sl(T_+(L))=tb(L)-r(L)$ | **Etnyre §2.9, Lemma 2.22, eq. (17), p. 19** | **exact.** "$sl(T_\pm(L)) = tb(L)\mp r(L)$"; the $+$ instance is the SM's line. | **T2** (a full printed proof with a QED box, read) |

The parenthetical that ties $D+U$ to Etnyre's total cusp count is the SM's own
one-line justification, sm-3:3347–3348: "every cusp of an oriented front is
traversed either downward or upward, so the total cusp count in his $tb$
formula is $D+U$." It is not a citation and needs none; it is correct against
eq. (5)'s own $D,U$ partition. (F-25-84's "$\#\text{cusps}=D+U$ silent" item.)

The tb parenthetical, sm-3:3353–3355, verbatim:

> (For the second formula, the Legendrian $tb$, the printed proof used is
> Geiges~\cite[Proposition~3.5.9, p.~117]{Geiges}; Etnyre's equation~(7)
> reduces to his Remark~2.14, which is stated there without proof.)

**Both halves verified at the bytes**: Prop. 3.5.9 is on printed p. 117 with a
printed proof; Remark 2.14 is on p. 13 with none.

### 1.3 The front-writhe clause, sm-3:3356–3361

> For a generic positive transverse front (Definition~\ref{def:transverse-front}),
> self-linking equals its front writhe:
> Geiges~\cite[Section~3.1, Lemma~3.3, p.~46]{GeigesContact} (printed proof)
> and Geiges~\cite[Proposition~3.5.32, p.~127]{Geiges}; Etnyre's equation~(9),
> Section~2.6.4, states it.

| locator | at the bytes | depth |
|---|---|---|
| **Geiges survey §3.1, Lemma 3.3, p. 46** | **exact.** "**Lemma 3.3.** The self-linking number $l(\gamma)$ of a transverse knot is equal to the writhe $w(\gamma)$ of its front projection." Printed proof follows. §3.1 opens on p. 45; the lemma and its proof are on p. 46. | **T2**, with one reduction to an off-disk book (Saveliev [98]) that the *book* citation closes on disk — see `T2_DELTA.md` §3 |
| **Geiges book Prop. 3.5.32, p. 127** | **exact.** "**Proposition 3.5.32** The self-linking number $\mathtt{sl}(K)$ of a transverse knot $K$ in $(\RR^3,\xi_{st})$ is equal to the writhe of its front projection." Printed proof follows on the same page. | **T2**; every reduction followed on disk |
| **Etnyre eq. (9), §2.6.4, p. 15** | **statement present, with two defects, glyph-verified**: the display reads `sl(T) = writhe(Π(L))` — `Π(L)` where the knot is `T`; and its whole justification is one sentence, "The argument for this formula is exactly like the one for Equation (8)", eq. (8) being the **Lagrangian** formula. No hypothesis on the front is stated. | **T1 with defects.** SM6's wording — "*states* it" — is the correct verb and does not overclaim. |

The SM's ordering (Geiges with printed proof first, Etnyre demoted to "states
it") is the L-3 seat's condition **C3**, taken.

### 1.4 The block's closing sentence and status line

sm-3:3361–3362: "These are the local front and pushoff source formulas only."
sm-3:3363 `\status{lit: Etnyre and Geiges local front and pushoff formulas;
Registry~\ref{reg:etnyre}; round~3: page-precise locators, the cusp count $D+U$
and the front class named, F-25-82, F-25-83, F-25-84}`.

Observation, recorded not filed: the status line names round 3 only; the round-2
Geiges citations (F-25-80) that carry two of the three formulas are not named in
it. Cosmetic; the citations themselves are in the block text.

---

## 2. `def:transverse-front` (sm-3:3326–3337)

The class over which the front-writhe formula is stated. Consumed by
`src:contact` (DAG.md:152) and by `fd:contact` (DAG.md:154).

What it fixes: the $(x,z)$-plane diagram of a smooth oriented embedded knot $T$
with $z'-yx'>0$, whose $xz$ projection is **an immersion of the parameter
circle with finitely many transverse double points and no triple point**, the
over strand being **the branch of smaller $y$**; it records that the front has
no cusp, and that every vertical tangent points upward **as a consequence**
($x'=0\Rightarrow z'>0$), not a hypothesis.

**Match against what the cited proofs need.** Geiges's Prop. 3.5.32 quantifies
over transverse knots in $(\RR^3,\xi_{st})$ and its proof applies
Prop. 3.4.14, which is stated *"given by a link diagram"* — and a diagram is
defined at Remark 3.4.13, p. 112, as the image under a projection for which the
curves are "immersed except for transverse double points". **SM6's definition is
at least as strong as that**, so the instantiation is licensed. The
upward-tangency remark reproduces Geiges book p. 100's first displayed
consequence of transversality ("if $y'=0$, then $z'>0$", his letters) and is
correctly labelled a consequence.

Verified arithmetic in the definition: $\alpha(T')=z'-yx'>0$ with $x'=0$ gives
$z'>0$. Correct.

---

## 3. `fd:linking-calculus` (statement sm-3:2783–2825) and `rem:sl-convention` (sm-3:3010–3021)

### 3.1 What `fd:linking-calculus` supplies

It is an **internal** lemma (status: *transcribed (unrefereed): RC
d2d_contact_constructions (C030)*, held by bench A) and consumes **no**
literature input — DAG.md:145 lists its literature column as "—". It defines
the normalized Gauss pairing \eqref{fd:gauss-linking}, proves the mixed-crossing
formula for a direction *generic for the pair*, and defines

$$sl(T_s)=\ell(T_s,T_s+\epsilon\partial_y) \tag{fd:framed-linking}$$

with invariance in $s$ and independence of $\epsilon$.

One comparative sentence remains inside the statement, sm-3:2803–2804: "Thus it
has exactly the linking normalization used in the source's front calculations."
It carries no citation. It is a claim about the *normalization* (that
$\ell$ is the ordinary linking number, i.e. one half the signed mixed-crossing
sum), which the lemma proves for itself; it is not the self-linking
identification. Recorded as an observation (`RECOMMENDATION.md` O4), not a
source-depth item.

### 3.2 `rem:sl-convention` — the identification, verbatim

> In~\eqref{fd:framed-linking} the global nonzero contact section $\partial_y$
> is the section in Etnyre's standard-space self-linking convention
> (Etnyre~\cite[Sections~2.6.3--2.6.4, p.~15]{Etnyre}; independence of the
> chosen nowhere-zero section of the contact structure:
> Geiges~\cite[Definition~3.2 and the following paragraph,
> p.~45]{GeigesContact}, whose $\partial_X$ is $-\partial_y$ under the
> coordinate change $(X,Y,Z)=(-y,x,z)$); no surface-dependent choice or
> extension is being made. This identifies the number of
> Lemma~\ref{fd:linking-calculus} with the literature's self-linking number;
> the lemma itself proves only the invariance and the normalization stated
> there (F-25-81).

| clause | source locator | at the bytes |
|---|---|---|
| $\partial_y$ **is** Etnyre's section | **Etnyre §2.6.4, p. 15** | **exact, word for word.** "note that the vector $v=\frac{\partial}{\partial y}$ is always in $\xi_{std}$ and thus can be used to trivialize $\xi_{std}$ independent of a Seifert surface for $T$. Now let $T'$ be a copy of $T$ obtained by pushing $T$ along $v$. The self-linking number of $T$ is the linking number of $T$ and $T'$." |
| the *definition* being matched | **Etnyre §2.6.3, p. 15** | **exact.** "we can find a nonzero vector field $v$ over $\Sigma$ in $\xi$. Let $T'$ be a copy of $T$ obtained by pushing $T$ slightly in the direction of $v$. The self-linking number $sl(T)$ of $T$ is the linking of $T'$ with $T$." |
| "no surface-dependent choice or extension is being made" | same | **correct**: §2.6.4's whole point is that $\partial_y$ trivializes $\xi_{std}$ *independent of a Seifert surface*. |
| independence of the nowhere-zero section | **Geiges survey Def. 3.2 + the following paragraph, p. 45** | **exact, and the argument is printed.** Def. 3.2: "The self-linking number $l(\gamma)$ of the transverse knot $\gamma$ is the linking number of $\gamma$ and $\gamma'$." Following paragraph: "in place of $\partial_x$ we could have chosen any nowhere zero vector field $X$ in $\xi_0$ … the difference … is the degree of the map $\gamma\to S^1$ … But the map $\gamma\to S^1$ factors through $\RR^3$, so the induced homomorphism on homology is the zero homomorphism." SM6's "printed degree argument" (registry) is the right description. |
| "$\partial_X$ is $-\partial_y$ under $(X,Y,Z)=(-y,x,z)$" | the transport | **TRUE, re-derived here.** $X=-y\Rightarrow y=-X\Rightarrow \partial_X=(\partial y/\partial X)\partial_y=-\partial_y$. Also $\Phi^*(dZ+X\,dY)=dz+(-y)dx=dz-y\,dx$ and $\det\Phi=+1$ (expanded: rows $(0,-1,0),(1,0,0),(0,0,1)$). Independently confirms bench A's 2026-09-05T18:36:57Z reading. |

**A note the remark does not print:** the survey at p. 45 writes Geiges's own
coordinates in **lower case** ($\xi_0=\ker(dz+x\,dy)$, pushoff along
$\partial_x$). The capitals $(X,Y,Z)$ are SM6's renaming of Geiges's letters,
established 637 lines earlier at sm-3:2373–2375 ("His form $dZ+X\,dY$ pulls back
to $dz-y\,dx$ under $(X,Y,Z)=(-y,x,z)$; this coordinate change has determinant
$+1$") and in registry L-3. The remark itself does not point there. Editorial;
`RECOMMENDATION.md` O2.

### 3.3 Where the identification is *used* — and where it is cited

`\ref{rem:sl-convention}` occurs **five** times in the frame: sm-3:2823 (a
`\status` line), sm-11:193, 223, 548, 872 (registry text and a table). **It is
referenced by no proof and by no statement body.** In particular the proof of
`fd:contact` — the sole consumer of `src:contact`, and the place where the
source's front-writhe identity is turned into \eqref{fd:front-writhe} in the
SM's own $sl$ — does not cite it. Filed as **O1**, the one finding of this pass.

---

## 4. `fd:contact` (statement sm-3:3403–3421; proof sm-3:3425–3496)

The single consumer. What it takes from L-3, step by step:

| step in the proof | SM6 locator | L-3 content used |
|---|---|---|
| the sign dictionary: $\nu=-\partial_y$, $\det_{xyz}(\partial_x,\partial_z,\nu)=1$, and $\det\begin{psmallmatrix}a&b&0\\0&0&-1\\c&d&0\end{psmallmatrix}=ad-bc=\det_{xz}$ | sm-3:3430–3437 | **none** — this is the SM's own computation. Both determinants re-checked here and correct. |
| "Summing the source transverse-front writhe formula proves \eqref{fd:front-writhe}" | sm-3:3438–3439 | **the front-writhe identity**, §1.3 above (Geiges survey Lemma 3.3 p. 46 / book Prop. 3.5.32 p. 127; Etnyre eq. (9)). This is the import. |
| "Absence of downward tangencies alone is not a converse transverse-lift theorem: the crossing-height inequalities will be checked separately in the carrier-floor proof." | sm-3:3439–3441 | **negative claim about the source's scope**, restored to RC's wording in round 5 (F-25-152). **Corroborated at the bytes:** Geiges book p. 100 gives the lift criterion as *two* conditions — "any curve in the $(y,z)$–plane without the forbidden crossing **or** downward vertical tangencies admits a lift" — and explicitly "leaves it to the reader". The forward promise lands: the crossing-order construction is printed at sm-3:4468–4485. |
| "Substitute the first two formulas of \eqref{fd:contact-inputs} into the third: $tb-r=w-\frac{D+U}{2}-\frac{D-U}{2}=w-D=sl_{\rm Ng}(F)$" | sm-3:3443–3450 | **the three source formulas**, §1.2 above, **now cited by label** (`\eqref{fd:contact-inputs}`, i.e. into `src:contact`). Arithmetic re-checked: $-\frac{D+U}{2}-\frac{D-U}{2}=-D$. Correct. This is the R-25-13 "what it buys" content: the port supplies the cusp bookkeeping, not the writhe identity. |
| $F_T$ lies on the domain of `ng:front-domain`; `fd:ng-bound` applied to $F_T$ | sm-3:3462–3470 | **none from L-3** (that is L-4). The F-25-153 discharge is present and cites the lemma by label. |

---

## 5. Registry entry **L-3** (`reg:etnyre`, sm-11:173–253)

Every locator in the entry was resolved at the source bytes.

| the entry says | verified |
|---|---|
| Etnyre §§2.1, 2.4 (conventions), 2.6.2 (eqs (5),(7)), 2.6.4 (eq (9)), 2.9 (Lemma 2.22, eq (17)) | **all five resolve** at pp. 4, 10, 14, 15, 19 respectively |
| "his equation (7) writes half the total cusp count, which is $D+U$" | **correct** (eq. (7) reads "number of cusps in $\Pi(L)$") |
| "equation (5) and Lemma 2.22 carry printed proofs" | **correct**, with one calibration: eq. (5)'s is a printed *inline argument* containing "One may easily check…"; Lemma 2.22's is a full proof environment closed by □ |
| "equation (7) reduces to his Remark 2.14, stated there without proof" | **correct**, Remark 2.14 read at p. 13 |
| "equation (9) carries no proof at its locator (its one-line deferral is to the Lagrangian equation (8)) and misprints $\Pi(L)$ for $\Pi(T)$" | **correct on both counts, glyph-verified** on the rendered page |
| tb formula at `[Proposition 3.5.9, p. 117]{Geiges}`, chain "Proposition 3.4.14, Definitions 3.5.1 and 3.5.4, Example 3.5.8, pp. 111–117 … **pending the seat's confirmation**" | **CONFIRMED by this seat.** Prop. 3.5.9 p. 117 (statement + printed proof); Prop. 3.4.14 statement p. 113, proof completed p. 114; Def. 3.5.1 p. 114; Def. 3.5.4 p. 115; Ex. 3.5.8 p. 116. The span "pp. 111–117" contains all five (Def. 3.4.10, the linking number, is on p. 111). |
| front-writhe at `[Section 3.1, Lemma 3.3, p. 46]{GeigesContact}` "(printed proof; one reduction, linking as a signed undercrossing count, to a book not on disk)" | **correct.** The reduction is to "[98, p. 37]" = **Saveliev, *Lectures on the Topology of 3–Manifolds*, de Gruyter 1999**, verified in the survey's bibliography p. 85; not on disk. See `T2_DELTA.md` §3 for why it is redundant rather than open. |
| and at `[Proposition 3.5.32, p. 127]{Geiges}` "(seat L-3: proof read, its reduction to Proposition 3.4.14 followed to a complete proof)" | **correct**, and re-read here independently |
| section-independence "at Remark~\ref{rem:sl-convention} (the identification sentence moved there from Lemma~\ref{fd:linking-calculus} in round 3, F-25-81)" | **correct on SM6** — this is F-25-144's repair; the entry no longer names `fd:linking-calculus` as the site, and the sentence 27 lines later (sm-11:222–224) agrees with it |
| "the book's Definition 3.5.28, Remark 3.5.29(2) and Corollary 3.5.31 are the same definition as Etnyre's" | **correct.** Def. 3.5.28 p. 125, Rems 3.5.29(2) p. 126, Cor. 3.5.31 p. 127, all read; Etnyre §2.6.3 p. 15 defines the same object. (Geiges writes $\mathrm{lk}(K,K')$, Etnyre $\mathrm{lk}(T',T)$; symmetric by Geiges Cor. 3.4.12, p. 112.) |
| convention transport ($\det\Phi=+1$; $\Phi^*(dZ+X\,dY)=dz-y\,dx$; front page unchanged; larger $X$ over $=$ smaller $y$ over; $\partial_X=-\partial_y$) | **all five re-derived and correct** |
| "the Etnyre locators were verified on arXiv:math/0306256v2, not on the Handbook printing (note in the bibliography)" | **correct**; the `Etnyre` bib entry (sm-refs.bib:9) carries exactly that note, and the on-disk banner reads `arXiv:math/0306256v2 … 22 Nov 2004` |
| "the Geiges survey is the retained arXiv:math/0307242v2" | **correct**; bib entry `GeigesContact` (sm-refs.bib:33–40) says "Retained arXiv:math/0307242v2, 24 January 2004; all cited locators refer to this 86-page version" — banner and page count both match |
| "Geiges's Theorem 2.27 located at its statement p. 21 and proof pp. 22–25" (F-25-84) | **correct** in the retained survey |
| R-25-13 clause: "Internal derivation available, resting on the source fact Literature input~\ref{src:contact} … the RC `fd:contact` port buys the crossing-sign dictionary and the $tb-r=w-D$ cusp bookkeeping, **not** the front-writhe identity, which it imports; no replacement of this entry exists in this phase" | **compliant and accurate.** It is exactly what the proof does (§4 above). Frame-wide, "T3" appears in sm-11 only at lines 10–11 (the global disclaimer), 142 and 246 — **never as "T3 available" for L-3.** |
| the §11.6 "replace L-2, L-3, L-4, L-5 by their available T3 proofs" text the SM1 seat objected to (C4) | **gone from SM6** (grep: no match) |
| bib `Geiges` = @book, *An Introduction to Contact Topology*, CUP 2008 | **matches the on-disk title page** (author, title, publisher, year read at PDF pp. 5–6) |
