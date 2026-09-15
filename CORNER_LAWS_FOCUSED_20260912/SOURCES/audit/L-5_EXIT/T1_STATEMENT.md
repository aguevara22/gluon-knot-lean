# L-5 on the EXIT frame SM6 — T1: statement comparison at the printed page

T1 = the source's full text on disk and hashed, and the statement **at the
cited locator** says exactly what the frame uses — objects, hypotheses,
quantifiers, normalization, conclusion. Every page named below was **rendered
and read as a page image this pass** (routes and hashes: `ACCESS_AUDIT.md`).
Nothing here is read off an OCR layer except where a line says so, and nothing
is inherited as a grade from the SM1 or SM2 L-5 seats.

Wenzl offsets: printed = PDF + 347. Jones: PDF page $n$ = printed $333+n$.

---

## 1. Convention dictionary, fixed once

| campaign symbol | source symbol | where fixed, printed | check |
|---|---|---|---|
| $c(i,j)=j-i$; $d=c_T(i)-c_T(i+1)$ | Wenzl $d_{t,l,m}=c_l-c_m+r_m-r_l$ | Wenzl **p. 363** | $c_l-r_l$ is the content of $l$'s box, so $d_{t,i,i+1}=c_T(i)-c_T(i+1)$ **exactly** |
| $\mathsf a_d(q)=\frac{1-q^{d+1}}{(1+q)(1-q^d)}$ | Wenzl $a_d(q)$, both forms | Wenzl **p. 361** | printed identically |
| $e_i^{\rm W}=\frac{q-g_i}{1+q}$; $g_i=q-(1+q)e_i^{\rm W}$ | Wenzl $e_i=\frac{q-g_i}{q+1}$; $g_i=q-(1+q)e_i$ | Wenzl **p. 361** | identical, both printed there |
| $\mathfrak a=1-q+z_J$, $\mathfrak b=z_J$, $z_J=q-(1+q)\eta$ (`hd:jones-parameters`, sm-7:1035–1039) | Wenzl $a=1-\eta(1+q)$, $b=q-\eta(1+q)$ | Wenzl **p. 376** | $\mathfrak b=b$ on sight; $\mathfrak a=1-q+q-(1+q)\eta=1-(1+q)\eta=a$ |
| $\mathfrak a,\mathfrak b$ | Jones $w,z$ | Jones **p. 346** | Jones $\lambda=(1-q+z)/qz=w/qz$ gives $z=-(1-q)/(1-\lambda q)$ and $w=1-q+z$; SM6's `hd:jones-torus` proof sets $z_J=(q-1)/(1-\lambda_Jq)$ and $\mathfrak a=\lambda_Jqz_J$ — the same two |
| $a=t^{-1}$, $z=x$, $\lambda_J=a^{-2}q^{-1}$ (`hsm:positive-parameters`, sm-7:1516–1520) | Jones $t=\sqrt\lambda\sqrt q$, $x=\sqrt q-1/\sqrt q$ | Jones **Prop. 6.2, p. 348** | $t=a^{-1}\iff\lambda=t^2/q=a^{-2}q^{-1}$ |
| $[j]!_q=\prod_{i=1}^j(1-q^i)$, $[0]!_q=1$ (sm-7:1430–1431) | Jones $[j]!$ in (9.6)/Thm 9.7 | Jones **p. 359**, forced by his own **Check 9.8** | see §3 |
| $h_\lambda$, $n(\lambda)=\sum(i-1)\lambda_i$ | Wenzl $h(i,j)=\lambda_i-i+\lambda_j^*-j+1$, $n(\lambda)=\sum_{i\ge1}(i-1)\lambda_i$ | Wenzl **p. 376** | identical |

One source-side trap re-confirmed and **not on SM6's path**: Jones **p. 348**'s
parenthetical "Another common choice of variables is $l=it^{-1}$, $m=ix$" has
the wrong sign on $m$ against his own Prop. 6.2 three lines above (with $m=ix$,
formula I becomes $t^{-1}P_+-tP_-=-xP_0$). SM6 never routes through the note;
`lp:core` uses $\varphi(m)=-\mathrm iz$, and RC `torus_dictionary.tex:43–45`
says so explicitly.

---

## 2. `hd:tableau-source` against Wenzl 1988

**Locator "pp. 361–364, 371–372", checked at the bytes.** $a_d$ + the Hecke
presentation p. 361 · Lemma 2.1 statement and proof p. 362 · (2.3), (2.4),
(H3), (H2) p. 363 · (H1), (2.5), (2.6) p. 364 · Lemma 2.11(a),(b) statement
p. 371, proof p. 372. **The span is correct and nothing imported falls
outside it.**

### W-1 — the tableau matrices

SM6 (sm-7:642–651):
> For real $q>0$, $q\ne1$, the space $V_\lambda$ with orthonormal standard
> tableau basis has the representation
> $\pi_\lambda(e_i^{\rm W})v_T=\mathsf a_dv_T+\sqrt{\mathsf a_d\mathsf a_{-d}}\,v_{s_iT}$,
> $d=c_T(i)-c_T(i+1)$. The square root is nonnegative; the second term is
> zero for a forbidden swap.

At Wenzl **p. 363**, printed: **(2.3)**
$\pi_\lambda(e_i)\vec v_t=a_{t,i,i+1}(q)\vec v_t+(a_{t,i,i+1}(q)a_{t,i+1,i}(q))^{1/2}\vec v_{g_i(t)}$,
with $d_{t,m,l}=-d_{t,l,m}$ on the same page, hence $a_{t,i+1,i}=a_{-d}$; and
**(2.4)** the symmetric $2\times2$ block
$\left(\begin{smallmatrix}a_d&(a_da_{-d})^{1/2}\\(a_da_{-d})^{1/2}&a_{-d}\end{smallmatrix}\right)$.

- content-difference convention: **identical** (§1);
- forbidden swap: Wenzl **p. 363** verbatim — "if $t$ is a standard tableau,
  $g_i(t)$ is not a standard tableau only if $i$ and $i+1$ are in the same row
  or in the same column. In these cases either $d_{t,i,i+1}=-1$ or
  $d_{t,i+1,i}=-d_{t,i,i+1}=-1$ which implies
  $a_{t,i,i+1}(q)a_{t,i+1,i}(q)=0$ for any value of $q$." **Exactly SM6's
  clause.**
- nonnegative root: Wenzl **Lemma 2.1(iv), p. 362**, "In particular,
  $a_d(q)\ge0$ for $d\in\mathbf Z\setminus\{0\}$" (stated for $q\ge1$),
  extended to all real $q>0$ by **2.1(iii)** $a_d(q)=a_d(q^{-1})$. Wenzl
  **Prop. 2.10, p. 371** re-states the same positivity ("both $a_d\ge0$ and
  $a_{-d}\ge0$ … always the case if $q$ is real and positive").
- hypothesis: Wenzl needs $q$ **$n$-regular** (p. 363); SM6's "real $q>0$,
  $q\ne1$" is **strictly stronger** for every $n$.
- "orthonormal": Wenzl **p. 362** gives $V_\lambda$ a *basis*
  $\{\vec v_t\}$; declaring it orthonormal is the SM's own step, and it makes
  (2.4) symmetric — which is the property Wenzl's Prop. 2.10 uses. **Faithful,
  but a declaration, not a quotation.**

**T1 exact, with the one declaration named.**

### W-2 — the branching

SM6 (sm-7:652–657): the **literal** restriction
$V_\lambda|_{H_{n-1}}=\bigoplus_{\mu\nearrow\lambda}V_\mu$ for $|\lambda|=n\ge2$,
one block per removable box.

Wenzl **p. 364**, printed: "Observe that the map $t\mapsto t'$ defines a
bijection between $T_\lambda$ and $\bigcup_{\lambda'<\lambda}T_{\lambda'}$. So
we obtain in particular **(2.5)** $V_\lambda\cong\bigoplus_{\lambda'<\lambda}V_{\lambda'}$
… A brief look at the definitions of $\pi_\lambda$ and $\pi_{\lambda'}$ shows
that the above equation gives us the decomposition of $V_\lambda$ as an
$H_{n-1}(q)$ module. So we have **(2.6)**
$\pi_\lambda|_{H_{n-1}(q)}\cong\bigoplus_{\lambda'<\lambda}\pi_{\lambda'}$."
($t'$ = $t$ without the box containing $n$, and $\lambda'$ = one box removed:
both defined **p. 362**.)

**T1 with two named deltas, both SM-side and both benign:**

1. Wenzl prints $\cong$; SM6 prints $=$ and calls it "literal". The printed
   *basis* bijection $t\mapsto t'$ does deliver the literal identification on
   basis blocks, which is the strength SM6's consumers use (`hd:complete`
   extracts blocks by central projections; `hd:trace` regroups them by $\mu$).
   Justified, but stronger than the printed symbol.
2. **$n\ge2$ is SM6's restriction, not Wenzl's.** It is *correct and needed*:
   at $n=1$ the display names $H_0$, undefined by SM6 ("For $n\ge1$",
   sm-7:617) and outside Wenzl's own definition (generators $g_1,\dots,g_{n-1}$).
   Wenzl never instantiates (2.5)/(2.6) at $n=1$. **F-25-97's repair is present
   in SM6's bytes at sm-7:656 and it is the right one.**

### W-3 — Lemma 2.11(a)

SM6: "Two distinct entries differing by at most two have nonzero content
difference."

Wenzl **Lemma 2.11(a), p. 371**, verbatim: "Let $t\in T_n$ be a standard
tableau and let $1\le i,j\le n$. If $0<|i-j|\le2$, then $d_{t,i,j}\ne0$."

**T1 verbatim.** (Wenzl forward-references it on **p. 364** — "Note that if $t$
is a standard tableau, $d_{t,i,j}\ne0$ for all $1\le i<j\le n$ with $|i-j|\le2$
by Lemma 2.11" — so the imported fact is exactly the one his relation proof
needs.)

### W-4 — Lemma 2.11(b)

SM6: "Distinct partitions of the same size $n\ge3$ have different sets of
immediate predecessors."

Wenzl **Lemma 2.11(b), p. 371**, verbatim: "Let $\lambda$ and $\tilde\lambda$
be 2 distinct Young diagrams with $n$ boxes, $n\ge3$. Then there is for at
least one of them a subdiagram with $n-1$ boxes which is not a subdiagram of
the other one. The same statement is true if the given diagrams are $(k,l)$
diagrams with $l\ge5$ and if we also require the subdiagram to be a $(k,l)$
diagram."

For $n$-box diagrams an $(n-1)$-box subdiagram is exactly an immediate
predecessor, so "at least one of them has one the other does not" is the
inequality of the two finite predecessor sets. **T1 exact.** SM6 imports the
first sentence only and drops the $(k,l)$ half and clause (c) — consistent with
its own exclusion sentence.

### W-5 — the exclusion clause

SM6: "No irreducibility, completeness, trace-weight or root-of-unity theorem is
included in this input."

I read the four candidates at the printed pages, and each has an SM6
counterpart carrying its own proof (details and the proof reading in
`T2_DELTA.md` §2):

| Wenzl result, printed | SM6 counterpart |
|---|---|
| (2.1)/(2.2), **p. 361** | `hd:span` (sm-7:678–706), $\dim H_n\le n!$ from four $u_j$ identities |
| **Theorem 2.2, p. 365** — irreducible, pairwise non-isomorphic, $\pi_n$ faithful, $H_n(q)\cong\mathbf CS_n$ | `hd:complete` (sm-7:714–800), from $DU-UD=I$, $\sum f_\lambda^2=n!$ and minimal projections |
| **Proposition 2.10, p. 371** — faithful $C^*$ representation for real positive $q$ | subsumed in `hd:complete`'s own continuity/self-adjointness paragraph |
| **(3.5)/(3.6), p. 376** and **Theorem 3.6(a), p. 378** | `hd:weight` / `hd:weight-sums` / `hd:trace`, whose printed numerator is `hd:correct-numerator` |

**The separation is real, not nominal.** Wenzl's Prop. 2.10 is printed *on the
same page*, a few inches above the clause SM6 does import, and SM6 did not take
it.

**Verdict for §2: `hd:tableau-source` is at T1 on every clause.**

---

## 3. The Jones cross-checks

On SM6, Jones is **not a premise** — `hd:jones-torus` is proved internally — so
T1 is the required depth. All four locators are exact.

| SM6 claim | Jones at the locator | verdict |
|---|---|---|
| `hd:jones-formula` (sm-7:1433–1444) "agrees with the formula in Jones's Theorem 9.7" | **Thm 9.7, p. 359**: $X_K(q,\lambda)=\left(\frac{1-q}{1-q^n}\right)\frac{\lambda^{(n-1)(m-1)/2}}{1-\lambda q}\sum_{\gamma+\beta+1=n,\ \gamma,\beta\ge0}(-1)^\beta q^{\beta m+\gamma(\gamma+1)/2}\frac{\prod_{i=-\gamma}^\beta(q^i-\lambda q)}{[\gamma]![\beta]!}$ | **identical term for term** ($\gamma+\beta+1=n\iff\beta+\gamma=n-1$; prefactor, sign, $q$-exponent, product range and denominator all match) |
| "exactly the reduced-braid normalization of Jones's Definition 6.1" (sm-7:1420–1421) | **Def. 6.1, p. 348**: $X_L(q,\lambda)=\left(-\frac{1-\lambda q}{\sqrt\lambda(1-q)}\right)^{n-1}(\sqrt\lambda)^e\operatorname{tr}(\pi(\alpha))$, $e$ = exponent sum | **identical** to SM6's $K^{n-1}s^{m(n-1)}$ with $K=-(1-\lambda_Jq)/(s(1-q))$, $s=\sqrt{\lambda_J}$; the exponent sum of $\delta_n^m$ is $m(n-1)$, printed at sm-7:1465 |
| the variable bridge of `hsm:positive-parameters` and `rem:torus-conventions`(1) | **Prop. 6.2, p. 348**: "$t=\sqrt\lambda\sqrt q$, $x=(\sqrt q-1/\sqrt q)$ then $P_L(t,x)=X_L(q,\lambda)$ … $t^{-1}P_{L_+}-tP_{L_-}=xP_{L_0}$" | **identical** |
| `hd:jones-boxes` (sm-7:1074–1079) "The right-hand factors are Jones's Figure 5.3; the denominator is his unnumbered hook diagram immediately before (5.4), printed p. 346 … the proved product is Jones's (5.4), and `hd:trace-definition` is his (5.5)" | **p. 346**: for $Y=(4,2,1)$, $S(q,z)=(w-z)(w-qz)(w-q^2z)(w-q^3z)(qw-z)(qw-qz)(q^2w-z)$; $Q(q)$ = the hook-length diagram $6,4,2,1/3,1/1$ with each $m$ replaced by $1-q^m$; **(5.4)** $W_Y=S/Q$; **(5.5)** $\operatorname{tr}(x)=\sum_YW_Y(q,z)\operatorname{tr}_Y(x)$ with $\operatorname{tr}_Y$ "the usual trace (sum of the diagonal entries)" | **identical**. Checked box by box on Jones's own worked example against $\prod_{(i,j)\in\lambda}(q^{i-1}\mathfrak a-q^{j-1}\mathfrak b)$; and Jones's $\operatorname{tr}_Y$ is SM6's "ordinary, not dimension-normalized, matrix traces" (sm-7:1024–1025) |
| $[j]!_q=\prod_{i=1}^j(1-q^i)$ (sm-7:1430) and `rem:torus-conventions`(1) | forced by **Check 9.8, p. 359**: at $n=2$, $m=1$ the two printed terms each carry $1/(1-q)$, i.e. $[1]!=1-q$ | **confirmed and re-derived**: instantiating Thm 9.7 at $n=2,m=1$ under this reading reproduces Jones's printed expression summand for summand, including his prefactor $\frac{1}{(1+q)(1-\lambda q)}$. The $q$-integer factorial would give $[1]!=1$ |

**Two printed source defects re-confirmed, neither copied by SM6:**

- **(9.6), p. 359** prints its summation condition as "$\alpha,\beta\ge0$"
  where "$\gamma,\beta\ge0$" is required — there is no $\alpha$ anywhere in the
  formula, and **Theorem 9.7 three lines below prints it correctly**. SM6
  prints $\beta,\gamma\ge0$ (sm-7:1438–1439) and states the misprint in
  `rem:torus-conventions`(3). **Not imported.**
- **p. 348**'s parenthetical $m=ix$ (§1 above). SM6 never uses it.

---

## 4. The disclosed Wenzl defects, verified at the printed pages

**(i) p. 365, the base-case sentence.** Printed, inside the proof of Theorem
2.2: "This is obvious for $n=1$ and follows for $n=2$ from
$\pi_{[2]}(e_1)=1\ne0=\pi_{[1^2]}(e_1)$."

Check from his own p. 361 $a_d$ and p. 363 (2.3):
$\lambda=[2]$ has contents $0,1$, so $d=c_T(1)-c_T(2)=-1$ and
$a_{-1}(q)=\frac{1-q^0}{(1+q)(1-q^{-1})}=0$, giving $\pi_{[2]}(e_1)=0$;
$\lambda=[1^2]$ has contents $0,-1$, so $d=1$ and
$a_1(q)=\frac{1-q^2}{(1+q)(1-q)}=1$, giving $\pi_{[1^2]}(e_1)=1$.
**The labels are interchanged**, harmlessly for Wenzl (he needs only $\ne$).
SM6's disclosure (sm-7:667–670) is **correct and correctly scoped**, and I
reach it independently.

**(ii) p. 376, equation (3.6).** Printed: **(3.5)**
$s_\lambda(a,b,q)=q^{n(\lambda)}\prod_{(i,j)\in\lambda}\frac{a-bq^{j-i}}{1-q^{h(i,j)}}$;
the special choice $a=1-\eta(1+q)$, $b=q-\eta(1+q)$; **(3.6)**
$s_\lambda(\eta,q)=q^{n(\lambda)}\prod_{(i,j)\in\lambda}\frac{(q-q^{j-i})-(1+q)(1-q^{j-i})\eta}{1-q^{h(i,j)}}$.

Substituting the special choice into (3.5) gives numerator
$1-q^{j-i+1}-(1+q)(1-q^{j-i})\eta$: **the $\eta$-term agrees; the $\eta$-free
term printed in (3.6) is $q-q^{j-i}$ where it must be $1-q^{j-i+1}$.** At one
box ($j-i=0$, $h=1$, $n(\lambda)=0$) printed (3.6) gives $(q-1)/(1-q)=-1$ while
(3.5) gives $+1$; at $j-i=1$ the printed $\eta$-free term vanishes identically
while the correct one is $1-q^2$, so it is not a global sign. **SM6's
disclosure (sm-7:670–672) is correct.**

**(iii) Theorem 3.6(a), p. 378** — the sentence SM6's last disclosure clause is
about. Printed: "Let $q$ be not a root of unity and let $\eta\in\mathbf C$.
Then tr is a trace with Markov property on $H_\infty(q)$ with
$\operatorname{tr}(e_1)=\eta$ if and only if $\operatorname{tr}|_{H_n(q)}$ has
the weight vector $(w_\lambda)_{\lambda\in\Lambda_n}$ with
$w_\lambda=s_\lambda(\eta,q)$ **(see (3.6))**."

So 3.6(a) routes its weight vector **through the misprinted (3.6)**: importing
it verbatim would import the misprint, and importing it "corrected" would be
exactly the silent correction SM6 forbids. **SM6's clause "neither that
erroneous expression nor the weight assertion of Theorem 3.6(a) is imported
after a silent correction" is precisely on target.**

**Not imported — checked on the SM side too.** SM6's `hd:correct-numerator`
(sm-7:1090–1093) prints $\mathfrak a-\mathfrak bq^c=1-q^{c+1}-(1+q)(1-q^c)\eta$
and says in the next line "This is the internally proved normalized formula,
not Wenzl's misprinted (3.6)". With $\mathfrak a=1-(1+q)\eta$ and
$\mathfrak b=q-(1+q)\eta$ this is **exactly the (3.5) numerator**. Consistently,
`hd:trace`'s proof prints "The one-box weight is
$(\mathfrak a-\mathfrak b)/(1-q)=1$" (sm-7:1046–1047) — (3.5)'s value, the
opposite of printed (3.6)'s $-1$. **No silently corrected expression is
imported.**

---

## 5. The 1985 thesis — what is actually printed

Read at the page image, thesis printed **p. 32** (PDF p. 38), §3 "Traces for
$H_\infty(q)$":

$$\{\lambda\}(w,z,q)=\frac{\prod_{1\le r<s\le m}\bigl(1-q^{d(r,s)}\bigr)}{\prod_{r=1}^{m}[\lambda_r+m-r]!}\;R_\lambda^{wz},\tag{1}$$

with $d(r,s)=\lambda_r-\lambda_s+s-r$, with

$$[k]!=(1-q)(1-q^2)\cdots(1-q^k),\tag{2}$$

and with $R^{wz}_\lambda$ the product of the first $\lambda_i$ terms of the
$i$-th row of the array whose $(i,j)$ entry is $q^{i-1}z+q^{j-1}w$; and, on the
same page,

$$\{\lambda\}(\eta,q)=\{\lambda\}\bigl(\eta(1+q)-q,\;1-\eta(1+q),\;q\bigr).\tag{3}$$

Two consequences, both new on this frame:

- **(2) is the same non-standard bracket Jones uses.** This is an *independent
  published witness* for `rem:torus-conventions`(1): the convention
  $[k]!=\prod_{i\le k}(1-q^i)$ is printed in Wenzl's thesis p. 32 as well as
  forced by Jones's Check 9.8. A positive finding.
- **(3) makes the thesis's letters the mirror image of Jones's.** Comparing
  with the 1988 paper's special choice ($a=1-\eta(1+q)$, $b=q-\eta(1+q)$): the
  thesis's $z$ is the paper's $a$ = Jones's $w$ = SM6's $\mathfrak a$, and the
  thesis's $w$ is **minus** the paper's $b$ = $-$Jones's $z$ = $-\mathfrak b$.
  So thesis $R^{wz}_\lambda$ box factors $q^{i-1}z+q^{j-1}w$ are exactly
  $q^{i-1}\mathfrak a-q^{j-1}\mathfrak b$ — the same product as Jones's
  Fig. 5.3 and SM6's `hd:jones-boxes`, **in letters $w,z$ swapped relative to
  Jones's $w,z$.**

**This is a different presentation, not a defect.** SM6's registry lists it
among "the sources' normalization defects" (sm-11:331–334). See
`RECOMMENDATION.md` C1–C3.

---

## 6. Positive controls on the printed formula

`work/jones97_corner.py`, `work/controls_r4.py`, exact rational arithmetic.
These **evaluate Jones's printed Theorem 9.7**; they establish nothing new.

Instantiating Thm 9.7 exactly as printed on p. 359, with
$[j]!=\prod_{i=1}^j(1-q^i)$ and the campaign bridge $\lambda=a^{-2}q^{-1}$
($z=0\iff q=1$), the coefficient of $a^{-(r-1)(2r+2)}z^0$ for $T(r,2r+1)$ is

| $r$ | 2 | 3 | 4 | 5 | 6 |
|---|---|---|---|---|---|
| from Jones Thm 9.7 | $-2$ | $5$ | $-14$ | $42$ | $-132$ |
| SM6 `hsm:terminal-value` $\frac{(-1)^{r-1}}{r}\binom{2r}{r-1}$ | $-2$ | $5$ | $-14$ | $42$ | $-132$ |
| $(-1)^{r-1}\mathrm{Cat}_r$ | $-2$ | $5$ | $-14$ | $42$ | $-132$ |

Broken controls, run at $r=4$ (where $\beta$ and $\gamma$ are not
interchangeable — at $r=3$, $n-1$ is even and the sign control cannot fire, so
the $r=3$ run is not evidence):

| deliberate break | value | fires? |
|---|---|---|
| $[j]!$ read as the $q$-integer factorial | $0$ | **yes** |
| sign $(-1)^\gamma$ in place of $(-1)^\beta$ | $+14$ | **yes** |
| exponent $\gamma m+\beta(\beta+1)/2$ | $+14$ | **yes** |
| $\lambda=a^{-2}$ (dropping $q^{-1}$) | $-14$ | **no** — reported as non-discriminating at $q\to1$, not as a firing control |
| prefactor power of $\lambda$ off by one | singular | degenerate; not counted |

Three of five controls fire; the two that do not are reported as such.
