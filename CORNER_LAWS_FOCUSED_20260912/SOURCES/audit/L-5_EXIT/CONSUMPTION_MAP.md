# L-5 on the EXIT frame SM6 — CONSUMPTION MAP

Every statement frame SM6 consumes from literature input L-5, with **the SM
locator** and **the source locator**. Frame pin and source hashes:
`ACCESS_AUDIT.md`. Line numbers are SM6 bytes
(`sm-7-anchors.tex` `b6cac973…`, `sm-11-registry.tex` `751fd3e0…`,
`sm-refs.bib` `17277432…`, `DAG.md` `f4f4ecdd…`).

## 0. What L-5 actually supplies on SM6

One published premise: the `literature` environment
**`hd:tableau-source`** (sm-7:640–674). Everything else the L-5 route needs is
proved inside the document or belongs to L-1.

The instrument agrees. `DAG.md` lists exactly three consumers of
`hd:tableau-source` — `hd:complete`, `hd:trace`, `hd:hooks` (DAG.md:309–311) —
and this is the registry's own list (sm-11:358–362). At the bytes the edges
are:

| site | form | inside |
|---|---|---|
| sm-7:718 | `\ref{hd:tableau-source}` | the **statement** of `hd:complete` (sm-7:714) |
| sm-7:761 | `\eqref{hd:matrix}` | the **proof** of `hd:complete` |
| sm-7:1044 | `\eqref{hd:branching-blocks}` | the **proof** of `hd:trace` (sm-7:1018) |
| sm-7:1174 | `\ref{hd:tableau-source}` | the **proof** of `hd:hooks` (sm-7:1100) |

Downstream the chain is `hd:complete`/`hd:trace`/`hd:hooks` →
`hd:jones-torus` (sm-7:1428) → `hsm:terminal` (sm-7:1494) →
`lit:torus` (sm-7:1618) and `thm:C-star` (sm-7:1651).

## 1. `hd:tableau-source`, clause by clause

SM locator: `sm-7-anchors.tex:640–674`. Its printed citation:
`\cite[Lemma~2.1, eqs.~(2.3)--(2.6), their relation and branching proofs, and
Lemma~2.11(a),(b), pp.~361--364,371--372]{Wenzl}` (sm-7:660–661; the same string
at sm-11:325–327).

**Locator span check, at the bytes.** $\mathsf a_d$, $e_i$ and the Hecke
presentation are on printed **p. 361**; Lemma 2.1 statement and proof on
**p. 362**; (2.3), (2.4) and the (H3)/(H2) verifications on **p. 363**; the (H1)
verification and (2.5), (2.6) on **p. 364**; Lemma 2.11(a),(b) statement on
**p. 371**, proof on **p. 372**. **The span "pp. 361–364, 371–372" is correct
and complete for what is imported.** (The two disclosed defects sit at pp. 365
and 376 and Theorem 3.6(a) at p. 378 — outside the span, correctly, since they
are disclosures of what is *not* imported; the running text names p. 365 and
"(3.6)" but not p. 376/378 — see `RECOMMENDATION.md`, observation O3.)

| # | SM clause (SM locator) | source locator | verdict |
|---|---|---|---|
| W-0 | ambient setting: `hd:hecke` (sm-7:618–623) $g_i^2=(q-1)g_i+q$, $g_ig_j=g_jg_i$ ($|i-j|>1$), $g_ig_{i+1}g_i=g_{i+1}g_ig_{i+1}$, "$H_1$ is the scalar field"; `hd:axial` (sm-7:635–639) $\mathsf a_d(q)=\frac{1-q^{d+1}}{(1+q)(1-q^d)}$ ($d\ne0$), $e_i^{\rm W}=\frac{q-g_i}{1+q}$ | Wenzl **p. 361**: $(H1)'$–$(H3)'$ for $H_n(q)$ with generators $1,g_1,\dots,g_{n-1}$; $e_i=(q-g_i)/(q+1)$; $a_d(q)=\frac{1+q+\dots+q^d}{(1+q)(1+q+\dots+q^{d-1})}=\frac{1-q^{d+1}}{(1+q)(1-q^d)}$ for $q\ne1$, $d\in\mathbf Z\setminus\{0\}$ | printed **identically**; `$|i-j|>1$` = Wenzl's `$|i-j|\ge2$` |
| W-1a | the matrices: `hd:matrix` (sm-7:644–649) $\pi_\lambda(e_i^{\rm W})v_T=\mathsf a_dv_T+\sqrt{\mathsf a_d\mathsf a_{-d}}\,v_{s_iT}$, $d=c_T(i)-c_T(i+1)$ | Wenzl **(2.3), p. 363** $\pi_\lambda(e_i)\vec v_t=a_{t,i,i+1}(q)\vec v_t+(a_{t,i,i+1}(q)a_{t,i+1,i}(q))^{1/2}\vec v_{g_i(t)}$, with $d_{t,l,m}=c_l-c_m+r_m-r_l$ and $d_{t,m,l}=-d_{t,l,m}$ on the same page; **(2.4), p. 363** the $2\times2$ block $\begin{psmallmatrix}a_d&(a_da_{-d})^{1/2}\\(a_da_{-d})^{1/2}&a_{-d}\end{psmallmatrix}$; the conclusion "So $\pi_\lambda$ is a representation of $H_n(q)$", **p. 364** | exact. $c_l-r_l$ is the content of $l$'s box, so $d_{t,i,i+1}$ **is** $c_T(i)-c_T(i+1)$ under the SM's $c(i,j)=j-i$ |
| W-1b | "the space $V_\lambda$ with **orthonormal** standard tableau basis" (sm-7:642–643) | Wenzl **p. 362** defines $V_\lambda$ with basis $\{\vec v_t:t\in T_\lambda\}$ — a basis, not declared orthonormal there. Orthonormality is exactly the setting of **Prop. 2.10, p. 371** ("It is enough to check that the matrix blocks given in (2.4) are selfadjoint … if and only if both $a_d\ge0$ and $a_{-d}\ge0$. This is always the case if $q$ is real and positive.") | faithful, but a **declaration by the SM**, not a printed clause at pp. 361–364. It buys only the symmetry of (2.4) — not Prop. 2.10's conclusion, which the SM excludes |
| W-1c | "The square root is nonnegative" (sm-7:649–650) | Wenzl **Lemma 2.1(iv), p. 362**: "If $q\ge1$ … In particular, $a_d(q)\ge0$ for $d\in\mathbf Z\setminus\{0\}$", extended to $0<q<1$ by **2.1(iii), p. 362** $a_d(q)=a_d(q^{-1})$ | exact |
| W-1d | "the second term is zero for a forbidden swap" (sm-7:650–651) | Wenzl **p. 363**, verbatim: "if $t$ is a standard tableau, $g_i(t)$ is not a standard tableau only if $i$ and $i+1$ are in the same row or in the same column. In these cases either $d_{t,i,i+1}=-1$ or $d_{t,i+1,i}=-d_{t,i,i+1}=-1$ which implies $a_{t,i,i+1}(q)a_{t,i+1,i}(q)=0$ for any value of $q$." | exact |
| W-1e | hypothesis "For real $q>0$, $q\ne1$" (sm-7:642) | Wenzl requires $q$ **$n$-regular**: $q\ne0$ and not a $k$-th root of unity for $k=2,\dots,n$ (**p. 363**) | the SM's hypothesis is **strictly stronger** for every $n$ — no gap |
| W-2 | the branching: `hd:branching-blocks` (sm-7:652–657) "Deleting the largest entry gives the **literal** restriction $V_\lambda|_{H_{n-1}}=\bigoplus_{\mu\nearrow\lambda}V_\mu$ $(|\lambda|=n\ge2)$, with one block for each removable box" | Wenzl **p. 364**: "the map $t\mapsto t'$ defines a bijection between $T_\lambda$ and $\bigcup_{\lambda'<\lambda}T_{\lambda'}$. So we obtain in particular **(2.5)** $V_\lambda\cong\bigoplus_{\lambda'<\lambda}V_{\lambda'}$ … **(2.6)** $\pi_\lambda|_{H_{n-1}(q)}\cong\bigoplus_{\lambda'<\lambda}\pi_{\lambda'}$." ($t'$ = $t$ minus the box of $n$; $\lambda'$ = one box removed: **p. 362**) | content exact. **Two wording deltas**, both on the SM side: Wenzl prints $\cong$, the SM prints $=$ and the word "literal" (justified by the printed *basis* bijection, and it is the strength the SM's consumers use); and **$n\ge2$ is the SM's own restriction, not Wenzl's** — see W-2′ |
| W-2′ | the size restriction $n\ge2$ (sm-7:656) | Wenzl never instantiates (2.5)/(2.6) at $n=1$; his $H_n(q)$ has generators $g_1,\dots,g_{n-1}$, so $H_0$ is outside his own definition, as it is outside the SM's ("For $n\ge1$", sm-7:617) | the restriction is **necessary and correct**; it is the F-25-97 repair and is present in SM6's bytes |
| W-3 | "Two distinct entries differing by at most two have nonzero content difference." (sm-7:657–658) | Wenzl **Lemma 2.11(a), p. 371**, verbatim: "Let $t\in T_n$ be a standard tableau and let $1\le i,j\le n$. If $0<|i-j|\le2$, then $d_{t,i,j}\ne0$." | exact ($d_{t,i,j}$ **is** the content difference, fixed p. 363) |
| W-4 | "Distinct partitions of the same size $n\ge3$ have different sets of immediate predecessors." (sm-7:658–659) | Wenzl **Lemma 2.11(b), p. 371**, first sentence: "Let $\lambda$ and $\tilde\lambda$ be 2 distinct Young diagrams with $n$ boxes, $n\ge3$. Then there is for at least one of them a subdiagram with $n-1$ boxes which is not a subdiagram of the other one." | exact. An $(n-1)$-box subdiagram of an $n$-box diagram **is** an immediate predecessor, so "for at least one of them, one the other lacks" is precisely set-inequality. The SM correctly imports the first sentence only and drops the $(k,l)$ half and clause (c) |
| W-5 | the **exclusion** clause "No irreducibility, completeness, trace-weight or root-of-unity theorem is included in this input." (sm-7:662–663) | the four candidates, read at the bytes: **(2.1)/(2.2) p. 361**; **Theorem 2.2 p. 365** (irreducibility, pairwise non-isomorphism, faithfulness, $H_n(q)\cong\mathbf CS_n$); **Prop. 2.10 p. 371**; **(3.5)/(3.6) p. 376 and Theorem 3.6(a) p. 378** | the exclusion is **real, not nominal** — §2 of `T2_DELTA.md` gives the printed SM counterpart of each with its own proof |

### 1a. The disclosure paragraph (sm-7:667–674)

Not consumption; a statement *about* the source. Verified at the printed pages:

| SM sentence (SM locator) | source locator | verdict |
|---|---|---|
| "on a one-row tableau $d=-1$, so $e^{\rm W}=0$ and $g=q$; on a one-column tableau $d=1$, so $e^{\rm W}=1$ and $g=-1$" (sm-7:667–669) | computed from Wenzl's own p. 361 $a_d$ and p. 363 (2.3): $\lambda=[2]$ has contents $0,1$, $d=-1$, $a_{-1}=0$; $\lambda=[1^2]$ has contents $0,-1$, $d=1$, $a_1=1$ | correct |
| "Wenzl's printed p. 365 base-case sentence interchanges those labels and is not used." (sm-7:669–670) | Wenzl **p. 365**, inside the proof of Theorem 2.2: "follows for $n=2$ from $\pi_{[2]}(e_1)=1\ne0=\pi_{[1^2]}(e_1)$" | **confirmed at the printed page**: the labels are interchanged against his own (2.3)+$a_d$. Harmless in the source (only $\ne$ is needed there) |
| "His printed (3.6) is also not a normalized-weight premise: on one box it gives $(q-1)/(1-q)=-1$." (sm-7:670–672) | Wenzl **p. 376**: (3.5) $s_\lambda(a,b,q)=q^{n(\lambda)}\prod\frac{a-bq^{j-i}}{1-q^{h(i,j)}}$ with $a=1-\eta(1+q)$, $b=q-\eta(1+q)$; printed **(3.6)** numerator $(q-q^{j-i})-(1+q)(1-q^{j-i})\eta$ | **confirmed**. Substituting the special choice into (3.5) gives $1-q^{j-i+1}-(1+q)(1-q^{j-i})\eta$: the $\eta$-term agrees, the $\eta$-free term printed is $q-q^{j-i}$ where it must be $1-q^{j-i+1}$. One box: printed $(q-1)/(1-q)=-1$ against (3.5)'s $+1$ |
| "neither that erroneous expression nor the weight assertion of Theorem 3.6(a) is imported after a silent correction" (sm-7:672–674) | Wenzl **Theorem 3.6(a), p. 378**: "tr is a trace with Markov property on $H_\infty(q)$ with $\operatorname{tr}(e_1)=\eta$ **if and only if** $\operatorname{tr}|_{H_n(q)}$ has the weight vector $(w_\lambda)$ with $w_\lambda=s_\lambda(\eta,q)$ (**see (3.6)**)" | **the disclosure is exactly on target**: 3.6(a) routes its weight through the misprinted (3.6). The SM instead prints `hd:correct-numerator` (sm-7:1090–1093) $\mathfrak a-\mathfrak bq^c=1-q^{c+1}-(1+q)(1-q^c)\eta$ — the **correct** (3.5) numerator — and names it "not Wenzl's misprinted (3.6)". Checked: $\mathfrak a=1-q+z_J=1-(1+q)\eta=a$, $\mathfrak b=z_J=q-(1+q)\eta=b$ |
| "the generating-series notation of Wenzl's 1985 thesis \cite{WenzlThesis}, on file and consumed by nothing" (sm-11:332–334) — **this clause is in the registry, not at the input** | thesis printed **pp. 31–32**: $\{\lambda\}(w,z,q)=\frac{\prod_{1\le r<s\le m}(1-q^{d(r,s)})}{\prod_{r=1}^m[\lambda_r+m-r]!}R_\lambda^{wz}$, $d(r,s)=\lambda_r-\lambda_s+s-r$, $[k]!=(1-q)(1-q^2)\cdots(1-q^k)$, $R_\lambda^{wz}$ the array $q^{i-1}z+q^{j-1}w$; and $\{\lambda\}(\eta,q)=\{\lambda\}(\eta(1+q)-q,\,1-\eta(1+q),\,q)$ | "on file and consumed by nothing" is **true** (`WenzlThesis` occurs only at sm-11:333 and sm-refs.bib:57). The rest is **three separate defects** — see `RECOMMENDATION.md` C1–C3 |

## 2. `hsm:notation` (sm-7:364–397) — no L-5 published source is consumed

**Statement.** For each actual nonempty oriented decorated diagram,
$P_J(D;t,x)=P_D(t^{-1},x)$ with $P_D$ the construction of `lp:core`; the skein
`hsm:notation-skein` $t^{-1}P_J(D_+)-tP_J(D_-)=xP_J(D_0)$, $P_J(\bigcirc)=1$;
value $((t^{-1}-t)/x)^{c-1}$ on every ordered based UNDER-first $c$-component
diagram; and an enumerated list of retained invariances (F-25-103's repair).

**Status locator (round 5, F-25-149):** "RC p12:source-evaluation
(torus_dictionary: the definition $P_J(D;t,x)=P_D(t^{-1},x)$, the unknot value
and the UNDER-first initialization) and RC braid_finite for its use"
(sm-7:380).

**This locator is NOT a published source.** RC_v4 is campaign manuscript.
Checked at the RC bytes (`torus_dictionary.tex` `dfd31d82…`):

- `p12:source-evaluation` is at **lines 50–61** and its display
  `p12:same-diagram` does carry $P_{J,D}(t,x)=H^{\rm D}_D(t^{-1},x)=P_D(t^{-1},x)$;
- its proof carries "Its skein is $t^{-1}P_{J,+}-tP_{J,-}=xP_{J,0}$, and every
  UNDER-first $b$-component base has value $((t^{-1}-t)/x)^{b-1}$" (**:85–90**);
- `braid_finite.tex:189` reads "For the Jones notation of
  Lemma~\ref{p12:source-evaluation}, the last …" — i.e. it **defers**, exactly
  as F-25-159's sibling row F-25-149 said.

**So the F-25-149 repair lands: the new locator carries the statement, the old
one did not.**

**What published statement does the notation rest on?** *None as a premise.*
The SM's proof (sm-7:383–397) is a Laurent-ring substitution $a\mapsto t^{-1}$,
$z\mapsto x$ applied to `lp:core`, `lp:split-circle` and `rp:record-polynomial`
— all L-1 objects. `DAG.md:231` lists the parents as exactly
`lp:core`, `lp:split-circle`, `rp:record-polynomial`. The **published** anchor
that makes the renaming worth doing is Jones **Prop. 6.2, p. 348** ("$t=\sqrt\lambda\sqrt q$,
$x=\sqrt q-1/\sqrt q$ … $t^{-1}P_{L_+}-tP_{L_-}=xP_{L_0}$"), which the SM
cross-checks in `rem:torus-conventions` but does **not** cite in `hsm:notation`
and does not import. This is correct and worth saying plainly: **`hsm:notation`
consumes no L-5 literature; it is an L-1-backed change of variables into
Jones's letters.**

## 3. `hsm:terminal` (sm-7:1493–1616)

**Statement (sm-7:1494–1499).** For coprime $2\le n<m$ and $D$ the actual
positive closure of $(\sigma_1\cdots\sigma_{n-1})^m$,
$[a^{-(n-1)(m+1)}z^0]P_D(a,z)=\frac{(-1)^{n-1}}{n}\binom{m-1}{n-1}$.

**F-25-158 repair, at the bytes.** The statement block now contains **only**
hypothesis and conclusion; the directive "Use the normalized positive-braid
formula \eqref{hd:jones-formula} of Theorem \ref{hd:jones-torus} for this
diagram…" is the **first sentence of the proof**, sm-7:1505–1507. The status
line records the move (sm-7:1502). **Repair present.**

**L-5 content consumed:** none directly. Parents (`DAG.md:249`):
`hd:full-twist`, `hd:jones-torus`, `lp:core`. The published L-5 content enters
one level up, through `hd:jones-torus`.

**Cross-check (not a premise).** `hd:jones-torus` (sm-7:1428–1447) prints
$[j]!_q=\prod_{i=1}^j(1-q^i)$, $[0]!_q=1$, and its own display, then says "This
agrees with the formula in Jones's Theorem 9.7". At the source: Jones **Thm 9.7,
p. 359**
$X_K(q,\lambda)=\left(\frac{1-q}{1-q^n}\right)\frac{\lambda^{(n-1)(m-1)/2}}{1-\lambda q}\sum_{\gamma+\beta+1=n,\ \gamma,\beta\ge0}(-1)^\beta q^{\beta m+\gamma(\gamma+1)/2}\frac{\prod_{i=-\gamma}^\beta(q^i-\lambda q)}{[\gamma]![\beta]!}$
— **identical term for term** ($\gamma+\beta+1=n\iff\beta+\gamma=n-1$). The
`hd:closure-trace` normalization is Jones **Def. 6.1, p. 348**
$X_L=\left(-\frac{1-\lambda q}{\sqrt\lambda(1-q)}\right)^{n-1}(\sqrt\lambda)^e\operatorname{tr}(\pi(\alpha))$,
with $e=m(n-1)$ the exponent sum — **identical**. The trace decomposition
`hd:trace-definition` is Jones **(5.5), p. 346** and the weight product
`hd:jones-boxes` (sm-7:1074–1079) is his **Figure 5.3 / (5.4), p. 346**: on
Jones's own worked $Y=(4,2,1)$ the printed $S(q,z)$ factors
$(w-z)(w-qz)(w-q^2z)(w-q^3z)(qw-z)(qw-qz)(q^2w-z)$ match
$\prod_{(i,j)\in\lambda}(q^{i-1}\mathfrak a-q^{j-1}\mathfrak b)$ **box by box**.

## 4. `lit:torus` (sm-7:1618–1648)

**Statement.** For $r\ge2$,
$[a^{2-2r^2}z^0]H_{T(r,2r+1)}(a,z)=(-1)^{r-1}\mathrm{Cat}_r$, in the
normalization of `lit:homfly`.

**F-25-159 repair, at the bytes (sm-7:1624).** New locator: RC `an:bem-catalan`
(`d7_anchors.tex` `571f2830…`), with the route difference stated. Checked:

- `an:bem-catalan` is at **d7_anchors.tex:199–205** and its display
  `an:torus-coefficient` is $[a^{2-2r^2}z^0]P_{T(r,2r+1)}(a,z)=(-1)^{r-1}\mathrm{Cat}_r$
  — **the statement, at the new locator**;
- RC's proof does reach it **by the mirror**: "Lemma p12:torus-diagram gives a
  finite word … from the specified negative torus diagram to the fixed-shadow
  mirror … with both variable changes $(a,z)\mapsto(a^{-1},-z)$" (**:212–215**),
  landing on `an:bem-dictionary` $c=a^{-1},\ z_B=-z$ (**:225–228**) and the BEM
  row `an:bem-row`;
- the old locator RC `hd:section` (`d9b_hecke.tex` `a59ae724…`) **does not carry
  the statement**: its closing paragraph assigns it away — "The campaign mirror
  $c=a^{-1}$, $z_B=-z$ and Catalan extraction remain the separate internal proof
  of Lemma~\ref{an:bem-catalan}" (**:1199–1201**). **F-25-159's finding is
  confirmed and its repair lands.**
- "whose exponent and Catalan steps this proof reprints" is **accurate**: RC
  prints $2-2r^2$ at `an:terminal-degree` (**:251–253**) and the chain
  $\beta_{r-1}=(-1)^{r-1}\frac1r\binom{2r}{r-1}=(-1)^{r-1}\frac{(2r)!}{r!(r+1)!}=(-1)^{r-1}\mathrm{Cat}_r$
  at `an:terminal-coefficient` (**:255–260**); SM6 reprints both at
  `hsm:star-exponent` (sm-7:1630–1633) and `hsm:star-catalan` (sm-7:1635–1641).

**Route difference — the substantive point.** RC's route passes through the BEM
row, i.e. through **BEM (3.35)**, which BEM states after "performing various
simple manipulations" and does **not prove there** (verified at printed p. 1888
of the published Ann. Henri Poincaré version and at the same equation number in
arXiv v1). SM6's route does **not** pass through it: `lit:torus`'s proof takes
the coefficient from `hsm:terminal` on the positive closure. **The SM's
departure from RC's route removes a source-side weakness rather than adding
one** — a positive finding, recorded as such.

**Consumers: none.** `DAG.md` lists no node with `lit:torus` as a parent, and
`\ref{lit:torus}` occurs at sm-11:318, 324, 363 (×2), 373, 845, 919 and
sm-7:1701, 1712 — all registry prose or `rem:torus-conventions`, no proof.

## 5. `thm:C-star` (sm-7:1651–1697)

Consumes L-5 **only** through `hsm:terminal` (sm-7:1670, 1683). Parents in the
DAG: `def:C`, `hsm:terminal`, `lem:corner-values`, `lem:star-generic`,
`lp:core`, `prop:A-star`, `prop:C-reversal`, `prop:star-decomp`,
`rp:record-polynomial`, `sv:star-record` — **`lit:torus` is not among them**,
which is the SM6 registry's claim, verified. The proof reprints the same
exponent and Catalan arithmetic (`sv:scalar-catalan`, sm-7:1679–1685).

## 6. `rem:torus-conventions` (sm-7:1698–1720)

Framed as "the cold source audit of registry entry L-5 … recorded here as its
claims, with attribution". Its three clauses, checked at the printed pages:

| clause | source locator | verdict |
|---|---|---|
| (1) "Jones writes $t=\sqrt{\lambda q}$ and $x=\sqrt q-1/\sqrt q$ (his Proposition 6.2) with the skein $t^{-1}P_+-tP_-=xP_0$, so $a=t^{-1}$ and $z=x$" | Jones **Prop. 6.2, p. 348**, verbatim | correct |
| (1) "his $[k]!$ in equation (9.6) and Theorem 9.7 is $\prod_{i=1}^k(1-q^i)$, not the $q$-integer factorial, which would be off by $(1-q)^{n-1}$" | forced by Jones's own **Check 9.8, p. 359**: at $n=2,m=1$ both printed terms carry $1/(1-q)$, i.e. $[1]!=1-q$. I re-derived both summands and they reproduce the printed expression exactly. The stated discrepancy factor is right: $[k]!=[k]_q!(1-q)^k$, and $\beta+\gamma=n-1$ | correct. **Independently corroborated in a second published source**: Wenzl's 1985 thesis, printed **p. 32**, defines $[k]!=(1-q)(1-q^2)\cdots(1-q^k)$ |
| (2) "Gorsky, Brini–Eynard–Mariño and Dunfield–Gukov–Rasmussen use the mirror: their $a$ (BEM's $c$) is this document's $a^{-1}$ (DGR, Section 2.3), so the corner coefficient of Proposition lit:torus is their *top* coefficient ($k=n-1$, Gorsky's Corollary 3.3, first formula), not their bottom one" | **DGR §2.3** (arXiv v2 p. 7), verbatim: "For us, the standard $T_{a,b}$ has **negative** crossings"; §2.5 adds "For the negative torus knot $T_{2,3}$, the polynomial $P(T_{2,3})$ has all positive exponents of $a$". **BEM p. 1888**: "what we call the $(Q,P)$ torus knot is usually regarded as a $(Q,-P)$ torus knot … apply the mirror transformation … $p_0^{K^*}(c^2)=p_0^K(c^{-2})$". **Gorsky Cor. 3.3, p. 11**, first formula: $P_s^{(n-1)}(T_{n,m})=\frac{(-1)^{n-1}q^{n(n-1)}}{[n]_{q^2}}\binom{m-1}{n-1}_{q^2}$, and at $q=1$, $\frac{(-1)^{n-1}}{n}\binom{m-1}{n-1}$ — with $n=r$, $m=2r+1$ this is $(-1)^{r-1}\mathrm{Cat}_r$, the SM's corner, and it is his **top** index $k=n-1$ | correct on all three |
| (3) "Jones's equation (9.6) prints its summation condition as '$\alpha,\beta\ge0$' where '$\gamma,\beta\ge0$' is required (Theorem 9.7 prints it correctly); the misprint is not copied here" | Jones **p. 359**: (9.6) prints `$\gamma+\beta+1=n$ / $\alpha,\beta\ge0$` (there is no $\alpha$ in the formula); Theorem 9.7 three lines below prints `$\gamma,\beta\ge0$` | correct; SM6 prints $\beta,\gamma\ge0$ (sm-7:1438) |
| tail: "$\min\deg_aH_{T(r,2r+1)}(a,0)$ is exactly $2-2r^2$ … nothing in this document uses the nonvanishing" | attributed to the seat; internally, `thm:C-star` computes $c(K_r)=(-1)^{r-1}\mathrm{Cat}_r\ne0$ outright | consistent with F-25-75's closure (no source obligation remains) |

## 7. Registry entry L-5 (`reg:torus`, sm-11:317–381)

| registry claim | where it is checked | verdict |
|---|---|---|
| "The retained external premise is Literature input `hd:tableau-source`, from Wenzl [Lemma 2.1, eqs. (2.3)–(2.6), their proofs, and Lemma 2.11(a),(b), pp. 361–364, 371–372]" (sm-11:324–329) | §1 above | **true**, and the span is correct |
| "(its branching display restricted to $n\ge2$ in round 3, F-25-97)" (sm-11:329–330) | sm-7:656 | present at the bytes |
| "The printed coefficient calculation is cross-checked with Jones [Definition 6.1, Proposition 6.2 and Theorem 9.7]" (sm-11:330–331) | §3 above | all three locators exact at pp. 348, 348, 359 |
| **Containment** (F-25-108's repair, sm-11:357–367): the supplied object is `hd:tableau-source`, "consumed by Lemma hd:complete, by the hook-label identification in the proof of Lemma hd:hooks and by Theorem hd:trace (the ordering instrument's edges), hence by Theorem hd:jones-torus, Lemma hsm:terminal, Theorem thm:C-star and Proposition lit:torus. Proposition lit:torus itself is consumed by no proof (its reference occurs only in this registry)" | §0 and §4 above; `DAG.md:309–311` and the parent columns | **true at the bytes**, on both halves. (Small wording point: `lit:torus`'s references occur in the registry *and* in `rem:torus-conventions`, sm-7:1701, 1712 — neither is a proof, so the claim's substance holds; see O4) |
| "the triangle values that hypothesis (f) of thm:uniqueness needs are taken in the proof of thm:comparison from lem:corner-values(i) directly (F-25-12, F-25-145)" (sm-11:366–369) | this is F-25-145's repair; the claim is about `thm:comparison`, sm-6 | **not re-verified by this seat** (sm-6 is outside the L-5 byte set I read); recorded as unchecked here, checked by codex B-Q3-L5-COMPARISON and the curator at A4 |
| **Dependence on L-1** (F-25-109 C7, sm-11:369–376): the braid certificates of §`hsm:section` run on `lp:lm`, `lp:core`, `rp:record-polynomial`, `lp:split-circle`, and `lit:torus`'s proof closes through `lp:core`'s $P=H$ | sm-7:398–406 (the `bf:` preamble names exactly those four) and sm-7:1645–1646 (`lit:torus`'s proof: "Theorem~\ref{lp:core} identifies its local $P$ with $H$") | **true at the bytes** |
| the thesis bib entry (F-25-109 C8) | sm-refs.bib:57 `@phdthesis{WenzlThesis, … note={UMI 8603724; the copy on file was consulted for its title pages only}}` | entry **present**; but see C1–C3 in `RECOMMENDATION.md` — the note and the registry's characterization of the thesis are inconsistent |
| "The verified Gorsky and DGR bytes are the final arXiv versions (v3 and v2)" (sm-11:355–356) | stamps on the files (`arXiv:1003.0916v3`, `arXiv:math/0505662v2`) plus the two arXiv abstract pages fetched this pass | **true**, and now confirmed against the live submission histories |
| "the DGR entry of the bibliography now carries its arXiv identifier (F-25-74)" | sm-refs.bib:17 `note={arXiv:math/0505662; the cited section numbering is that of arXiv v2}` | present |
| "Brini–Eynard–Mariño [eq. (3.35)] state the generating function without proof there (a cross-check only …)" (sm-11:348–350) | BEM published **p. 1888** and arXiv v1: "Using the above results, and performing various simple manipulations, we find the following expression" — no proof at the locator; **equation number (3.35) is the same in both editions**, so `\cite[eq.~(3.35)]{BEM}` resolves at the journal edition the bib entry names | **true**; locator resolves |
| Gorsky's defects "accurately" (F-25-72's repair, sm-11:341–347): index slip $P_s^{2k}$ for $P_s^k$ in the Appendix; the genuine **sign** slip in Cor. 3.4, p. 11, outside the Appendix; neither on this document's path | Gorsky **p. 11**: (3.7) gives $P_s^k(T_{n,n+1})=(-1)^kq^{k(k+1)}\cdots$, and the very next line prints "At the limit $q=1$ we have $(-1)^{k-1}P_s^k(T_{n,n+1})=\dots$" — **the sign slip, at p. 11, outside the Appendix, confirmed**. The Appendix index slip was not re-read this pass (Gorsky is a comparison source on SM6, not a premise) | the sign-slip half **confirmed at the bytes**; the Appendix half carried from the SM1/SM2 seats, named as carried |
