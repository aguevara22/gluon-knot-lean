# L-5 on the EXIT frame SM6 — T2 DELTA

T2 = T1, **plus** the source's own proof of the used statement read and checked
to establish it, with any gap between what is proved and what the frame uses
named. This file says, clause by clause, **what was read at proof depth and
what was not.**

Arithmetic checks in `work/wenzl_lemma21.py` (exact rational functions in
$\mathbb Q(q)$) and `work/jones97_corner.py` / `work/controls_r4.py`. All of
them verify a **source's own algebra**; none proves anything new (rule 8).

---

## 1. `hd:tableau-source`, clause by clause, at proof depth

### W-1 — the matrices: Lemma 2.1, (2.3), (2.4), and the relation proof

**Read: Wenzl pp. 362, 363, 364 in full, as page images.**

- **Lemma 2.1, p. 362.** The printed proof says "The proofs of (i), (ii),
  (iii) and (vi) are straightforward computations." Only (iv) and (v) are
  printed: (iv) from
  $a_d(q)=\frac{q}{1+q}+\frac{1}{(1+q)(1+q+\dots+q^{d-1})}$ together with
  $a_{-d}=1-a_d$ (by (i)); (v) from the derivative of
  $t\mapsto\sin(t+x\pi)/\sin t$.
  The clauses SM6 needs are **(i)** (idempotence of (2.4)), **(ii)** (used for
  the braid relation), **(iii)+(iv)** ($a_d\ge0$ on real $q>0$, hence a real
  nonnegative square root).
  **(iv) is printed and lands.** **(i), (ii) and (vi) are asserted, not
  printed — so I verified them myself** in exact rational arithmetic
  (`work/wenzl_lemma21.py`): $a_d+a_{-d}=1$ for $|d|\le6$; both printed forms
  of the (ii) identity $q/(1+q)^2=a_ka_m+a_la_{-m}-a_ka_l=a_ka_m+a_la_{-k}-a_ma_l$
  for all $k,m\in\{1,\dots,6\}$, $l=k+m$; $a_da_{-d-1}=q/(1+q)^2$; and (vi) on
  the same range. All hold identically.
- **(2.3)/(2.4) and the relations, pp. 363–364.** $(H3)$: (2.4) is idempotent
  by 2.1(i) — checked. $(H2)$: from $g_ig_j(t)=g_jg_i(t)$ for $|i-j|\ge2$ —
  printed and immediate. $(H1)$: the two three-term expansions are printed in
  full on **p. 364**, their difference is the display $(*)$, the competing
  expression is $(**)$, and Wenzl writes "It follows from Lemma 2.1, (ii) that
  $(*)$ and $(**)$ are equal". **Checked against the 2.1(ii) identity I
  verified above; it lands.**
- **Well-definedness on standard tableaux, p. 364.** "if $q$ is $n$-regular,
  our computation above always makes sense even if some of the tableaux
  occurring there should no longer be standard tableaux. Recall that $V_\lambda$
  is an invariant subspace of $\tilde V_\lambda$ for any value of $q$. … So
  $\pi_\lambda$ is a representation of $H_n(q)$." The invariance of $V_\lambda$
  is proved on **p. 363** from the forbidden-swap sentence, and the
  no-hidden-zero condition is Lemma 2.11(a), forward-referenced on p. 364.
  **Lands.**
- **Hypothesis.** Wenzl's $n$-regularity vs SM6's real $q>0$, $q\ne1$: SM6 is
  strictly stronger. **No gap.**

**W-1: T2.** *One SM-side item named, not a source gap*: "orthonormal" is
SM6's declaration (Wenzl's p. 362 gives a basis). It buys the symmetry of (2.4),
which Wenzl himself uses at Prop. 2.10, p. 371 — a result SM6 excludes. Nothing
downstream needs more than that symmetry.

### W-2 — the branching: (2.5), (2.6)

**Read: Wenzl p. 364.** The bijection $t\mapsto t'$ is printed and immediate
($t'$ = $t$ minus the box containing $n$; p. 362). (2.5) follows because both
sides carry the same tableau basis. (2.6) is justified in one printed sentence
— "A brief look at the definitions of $\pi_\lambda$ and $\pi_{\lambda'}$ shows
that the above equation gives us the decomposition of $V_\lambda$ as an
$H_{n-1}(q)$ module" — whose content I followed: for $i\le n-2$ the entries of
$\pi_\lambda(e_i)$ on $v_t$ depend only on $d_{t,i,i+1}$, which is unchanged by
deleting the box of $n$, so each $T_{\lambda'}$-block carries exactly
$\pi_{\lambda'}$. **Checked; lands**, and it lands *literally on basis blocks*,
which is the strength SM6 uses.

**W-2: T2**, with SM6's $=$/"literal" wording and its own $n\ge2$ restriction
recorded in `T1_STATEMENT.md` §2.

### W-3 — Lemma 2.11(a)

**Read: printed proof, Wenzl p. 372, with Fig. 1.** Printed in full: "As
$d_{t,j,i}=-d_{t,i,j}$, we can assume $i<j$. If $d_{t,i,j}=0$, the box
containing $j$ has to be both to the right of and below the box containing $i$.
But if $t$ is standard, there have to be at least 2 boxes in $t$ which contain
numbers between $i$ and $j$ (see Fig. 1)."

Followed: $d_{t,i,j}=0$ puts the two boxes on one diagonal; standardness with
$i<j$ forces $j$'s box strictly south-east of $i$'s, say $(r_i+k,c_i+k)$,
$k\ge1$. The Young shape then contains $(r_i,c_j)$ and $(r_j,c_i)$ — Fig. 1's
two starred boxes — and each carries an entry strictly between $i$ and $j$
(one is in $i$'s row to its right and in $j$'s column above it; the other
symmetrically). Hence $j-i\ge3$, contradicting $|i-j|\le2$. **Checked; lands.**

**W-3: T2.** *One compression named*: that the two starred boxes lie in the
diagram at all is left to Fig. 1; it is one line from the Young-shape
condition. Not a gap in the statement.

**Redundancy, worth recording.** SM6 **re-derives this fact inline** in
`hd:complete`'s proof (sm-7:765–767: "boxes on the same diagonal force two
intermediate boxes, hence their entries differ by at least three"). The import
is therefore belt-and-braces; it is the published route and should stay.

### W-4 — Lemma 2.11(b)

**Read: printed proof, Wenzl p. 372.** Three cases, with $s$ the least index
where $\lambda_s\ne\tilde\lambda_s$ and w.l.o.g. $\lambda_s<\tilde\lambda_s$:

1. **$s\ne1$:** take $\lambda$ minus the last box of row $s-1$.
   *Removability* is unprinted, one line: $\lambda_{s-1}=\tilde\lambda_{s-1}\ge\tilde\lambda_s>\lambda_s$,
   so $\lambda_{s-1}>\lambda_s$ and the box is removable.
   *Why $\mu\not\subseteq\tilde\lambda$* is unprinted, one line:
   $\mu_i=\tilde\lambda_i$ for $i<s-1$, $\mu_{s-1}=\tilde\lambda_{s-1}-1$,
   $\mu_s=\lambda_s\le\tilde\lambda_s-1$, so
   $\sum_{i\le s}\mu_i\le\sum_{i\le s}\tilde\lambda_i-2$; since
   $|\mu|=|\tilde\lambda|-1$, some $i>s$ has $\mu_i>\tilde\lambda_i$.
   **Checked.**
2. **$s=1$, $\tilde\lambda$ has more than one row:** remove a box of
   $\tilde\lambda$ from a row other than the first; its first row is still
   $\tilde\lambda_1>\lambda_1$, so it is not contained in $\lambda$.
   **Printed and immediate.**
3. **$s=1$, $\tilde\lambda$ one row:** Wenzl writes "Otherwise $\tilde\lambda=[n]$,
   $n\ge3$ and $\lambda=[n-1,1]$. In this case we take the subdiagram
   $[n-2,1]$ of $\lambda$." *Verified:* $[n]$'s only $(n-1)$-box subdiagram is
   $[n-1]$; $[n-2,1]$ has two rows, so it is not that one; $n\ge3$ makes the
   removal valid. *Compression:* "$\lambda=[n-1,1]$" is **not forced** by the
   case hypotheses — e.g. $n=4$, $\tilde\lambda=[4]$, $\lambda=[2,2]$. The
   omitted subcase is immediate: if $\lambda$ has $\ge2$ rows and
   $\lambda\ne[\lambda_1,1]$ then **every** $(n-1)$-subdiagram of $\lambda$ has
   $\ge2$ rows, hence is not $[n-1]$. **Checked.**

**W-4: T2, with three one-line compressions in the printed proof named** (case
1's removability, case 1's counting, case 3's omitted subcase). None touches
the statement; all three are elementary and I closed each above. (The SM2 seat
named the same three, and codex's `sm2_source_clause_review_v1` named the
case-3 one; I reached them from the page image independently.)

**W-4 is the genuinely load-bearing unproved import.** SM6 uses it twice —
`hd:hooks`'s proof, sm-7:1174 ("The predecessor-set distinction in Literature
input `hd:tableau-source` … identify the label uniquely"), and `hd:complete`'s
proof, sm-7:812–814 ("Different shapes of size $n\ge3$ have different
predecessor sets by the selected finite diagram fact") — and **re-proves it
nowhere**. W-1 (relations), W-2 (branching, partly) and W-3 are each shadowed by
an internal derivation; W-4 is not.

### W-5 — the exclusion clause, checked at proof depth on both sides

| Wenzl result, read at the printed page | what it asserts | SM6's own counterpart, with its own proof | imported? |
|---|---|---|---|
| **(2.1)/(2.2), p. 361** — $H_n(q)$ spanned by $\beta_1\cdots\beta_n$, and by $ae_{n-1}b$ or $c$ | spanning | `hd:span` (sm-7:678–712): $\dim H_n\le n!$ and the tower span, from the four printed $u_j$ identities | **no** |
| **Theorem 2.2, p. 365** — $\pi_\lambda$ irreducible; $\pi_\lambda\cong\pi_\mu\iff\lambda=\mu$; $\pi_n$ faithful; $H_n(q)\cong\mathbf CS_n$ | the whole completeness package | `hd:complete` (sm-7:714–827): $DU-UD=I$; $\sum_{|\lambda|=n}f_\lambda^2=n!$ "No hook-length dimension formula was used"; minimal-projection argument; comaximal kernels + Chinese remainder; the $q=1$ surjection onto $\mathbf C[S_n]$ | **no** — I read the proof and it cites no Wenzl theorem, only `hd:span` and the imported matrices |
| **Prop. 2.10, p. 371** — faithful $C^*$ representation for real positive $q$; proof: (2.4)'s blocks are self-adjoint iff $a_d,a_{-d}\ge0$ | $C^*$ structure | subsumed in `hd:complete`'s continuity paragraph (sm-7:754–764): $\mathsf a_1=1$, $\mathsf a_{-1}=0$, $\mathsf a_d+\mathsf a_{-d}=1$, $\mathsf a_d(1)=\frac{d+1}{2d}$, "All generator matrices are therefore real symmetric and continuous throughout $q>0$" | **no** |
| **(3.5)/(3.6), p. 376; Theorem 3.6(a), p. 378** — the Markov-trace weight vector $w_\lambda=s_\lambda(\eta,q)$, *via (3.6)* | the trace weights | `hd:trace` (sm-7:1017–1096), which proves existence, compatibility, the Markov equation and **uniqueness** from `hd:tower-span`, and prints the correct numerator `hd:correct-numerator` | **no** |

**The separation is real, and I verified it on the SM side too**, not only by
reading Wenzl. In particular `hd:complete`'s printed proof (sm-7:728–827)
re-derives, inside the document, the two ingredients of Wenzl's relation
verification: the "no hidden zero distance" fact (= 2.11(a)) at sm-7:765–767,
and the 2.1(ii) identity at `hd:axial-sum`/`hd:axial-relation`, sm-7:769–780
— which I re-checked in exact arithmetic and which hold
($1-\mathsf a_k-\mathsf a_m=-\frac{(1-q)(1-XY)}{(1+q)(1-X)(1-Y)}$;
$\mathsf a_k\mathsf a_m+\mathsf a_\ell(1-\mathsf a_k-\mathsf a_m)=\frac{q}{(1+q)^2}$;
common numerator $(1-qX)(1-qY)-(1-q)(1-qXY)=q(1-X)(1-Y)$).

**Verdict for §1: `hd:tableau-source` is at T2 on all four clauses.**

---

## 2. What was NOT read at proof depth, and why

| item | depth reached | why that is the right depth |
|---|---|---|
| **Jones, Thm 9.7 (p. 359)** and its derivation chain (Lemmas 9.3, 9.4, Cor. 9.5, Remark 3.7, (5.5), Fig. 5.6) | **T1 exact at the printed statement**; the derivation chain **not re-read this pass** | On SM6, Jones is a **cross-check, not a premise** — `hd:jones-torus` derives the formula internally from `hd:trace`, `hd:torus-trace` and the tableau input, and `DAG.md` lists no Jones leaf. T1 is the required depth for a cross-check (R-25-13 reasoning). The SM1 L-5 seat additionally carried Thm 9.7 to T2 through Jones's chain (`phase25/evidence/source_audit/L-5/T2_PROOF.md`, `30d624aa…`); **that is recorded here as that seat's reading, not re-established.** |
| **Jones, Def. 6.1, Prop. 6.2 (p. 348); Fig. 5.3, (5.4), (5.5) (p. 346)** | **T1 exact**; Prop. 6.2's own proof **not read** | same reason. Note the campaign explicitly declines Prop. 6.2's global existence/uniqueness route: RC `torus_dictionary.tex:42` — "Jones's global existence and invariance argument is not used." |
| **Gorsky, Thm 3.1 / Cor. 3.3 / Cor. 3.4 (p. 11)**; the Appendix proof of Thm 3.1 (p. 17) | Cor. 3.3 and Cor. 3.4 read **at the printed page** (T1); the Appendix **not re-read** | comparison source on SM6, no longer a premise (round-1 rewrite). The Appendix index-slip half of F-25-72 is **carried from the SM1/SM2 seats**, named as carried. The sign slip in Cor. 3.4 I confirmed myself at p. 11. |
| **BEM (3.35)** | **T1 at the printed page, in both editions** (arXiv v1 and Ann. Henri Poincaré p. 1888); **no proof exists at the locator to read** | BEM state it after "performing various simple manipulations". SM6 lists it as a cross-check only, which is exactly the right label, **and SM6's route does not pass through it** (§4 below). |
| **DGR §2.3, §2.5** | **T1**; nothing to prove (they are convention declarations) | correct depth |
| **Wenzl 1985 thesis** | **located, hashed, printed p. 32 read at the page image**; no clause graded | consumed by nothing on SM6 |
| **Wenzl Thm 2.2 (p. 365), Prop. 2.10 (p. 371), Thm 3.6 (p. 378)** | statements read; **proofs not read** beyond what §1 W-5 needed | deliberately **not imported**; reading their proofs is not required to certify a non-import, only to certify that the SM has its own |
| **SM6 `sm-6-comparison.tex`** (the F-25-145 clause about hypothesis (f)) | **not read** | outside the L-5 byte set; recorded as unchecked here |

---

## 3. What the internal L-5 closure buys, deflated

Source-side, SM6's premise set for the torus coefficient is **one finite,
elementary, published input**: four statements of Wenzl §2, each at T2, plus
one clause (W-1b, orthonormality) that is a declaration rather than a
quotation. Everything else on the route — spanning, the complete irreducible
family and $\sum f_\lambda^2=n!$, the Markov trace and its uniqueness, the
weight product, the finite Jones torus formula, the terminal coefficient — is
printed inside the document.

What that does **not** buy, and must not be reported as bought:

- the tableau matrices, the literal branching and the two finite diagram facts
  remain **external premises**;
- of those four, **W-4 alone is nowhere shadowed by an internal derivation**;
- the entry still stands on **L-1** through `lp:core`, `lp:lm`,
  `rp:record-polynomial` and `lp:split-circle` (sm-7:398–406) and on the global
  premise `lit:homfly` through `lp:core`. L-5's own external premise is at T2;
  **the L-1 dependence travels with L-1's row**, exactly as SM6 states
  (sm-11:369–376);
- and the whole section is tagged **transcribed (unrefereed)** at
  `hsm:notation`, `hd:jones-torus`, `hsm:terminal` and `lit:torus`. Proof-side
  refereeing is bench A's lane, not this seat's; nothing here clears it.

---

## 4. One route difference that removes a source-side weakness

RC's `an:bem-catalan` reaches the same coefficient **through the mirror and the
BEM row** (`d7_anchors.tex:207–228`), i.e. through **BEM (3.35)**, which BEM
state without proof. SM6 explicitly declines that route: `lit:torus`'s proof
takes the coefficient from `hsm:terminal` on the positive closure
(sm-7:1626–1647), and `hsm:terminal`'s proof states "No mirror of the knot or
change of writhe is made" (sm-7:1518).

**Deflated statement of the gain:** SM6's route removes a dependence on an
unproved-at-the-locator generating function and replaces it with the Wenzl
tableau input plus internal argument. It does **not** make the route
source-free, and it does not raise anything above T2.
