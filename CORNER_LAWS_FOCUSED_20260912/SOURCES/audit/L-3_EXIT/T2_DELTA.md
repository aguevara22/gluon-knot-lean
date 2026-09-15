# L-3 EXIT — T2: what was read at proof depth, and what was not

T2 = T1 **plus** the source's proof of the used statement read and checked to
establish it, every reduction followed to where it lands. Frame SM6.
Stamp 2026-09-06T01:56:31Z.

Rule 8 binds throughout: **no bench proof is printed here as a substitute.**
Where the source asserts, this file says "asserted" and stops.

---

## 0. The scoreboard

| clause SM6 consumes | witness SM6 cites for it | proof read? | depth |
|---|---|---|---|
| $r=(D-U)/2$ | Etnyre eq. (5), p. 14 | **yes**, the printed inline argument | **T2** |
| $tb=w-(D+U)/2$ | **Geiges book Prop. 3.5.9, p. 117** | **yes**, printed proof + its whole chain | **T2** |
| " (secondary) | Etnyre eq. (7), p. 14 | its justification read; it **reduces to Remark 2.14, p. 13, which has no proof** | **below T2** — and SM6 says so in the block |
| $sl(T_+(L))=tb(L)-r(L)$ | Etnyre Lemma 2.22, eq. (17), p. 19 | **yes**, full printed proof (□) | **T2** |
| $sl=$ front writhe | **Geiges book Prop. 3.5.32, p. 127** | **yes**, printed proof, every reduction followed **on disk** | **T2** |
| " (co-witness) | **Geiges survey Lemma 3.3, p. 46** | **yes**, printed proof; one reduction to an off-disk book, closed on disk by the book's Prop. 3.4.14 | **T2** |
| " (tertiary) | Etnyre eq. (9), p. 15 | no proof at the locator; one-line deferral to the **Lagrangian** eq. (8) | **T1 with defects** — and SM6 says so |
| $sl_{\rm SM}=sl_{\rm lit}$ (the $\partial_y$ section is the source's) | Etnyre §§2.6.3–2.6.4, p. 15 + Geiges survey Def. 3.2 & following ¶, p. 45 | **yes** — the independence argument is printed at p. 45 and was read | **T2** |

**Five of five consumed clauses now have a T2 witness at a page SM6 prints.**
On SM2 three of the five did not (the SM2 seat's verdict, F-25-80/81); the
round-2 and round-3 citations are what changed that, and they hold up at the
bytes.

---

## 1. Geiges book, Prop. 3.5.9, p. 117 — the tb formula
### (this is the confirmation registry L-3 records as "pending the seat's confirmation")

**Proof as printed** (read in `work/geiges_book_p108-132.txt` and on the
rendered page `work/geiges_p117_prop3559.png`; the two agree):

> By slight abuse of notation we ignore the distinction between $K$ and $K_F$.
> Fix an orientation for $K$. We compute $\mathtt{tb}(K)$ as in the example,
> i.e. we define a parallel copy $K'$ of $K$, with the induced orientation, by
> pushing (the front projection of) $K$ in the $z$–direction, and then compute
> $\mathtt{tb}(K)$ as linking number $\mathtt{lk}(K,K')$. That linking number,
> in turn, we compute by counting the crossings of $K'$ under $K$ with sign.
> It is easy to see that a self-crossing of $K$ will contribute a crossing of
> $K'$ under $K$ of the same sign, a cusp on the right will give a negative
> crossing of $K'$ under $K$, and a cusp on the left will give a crossing of
> $K'$ over $K$. Since there are as many cusps on the left as cusps on the
> right, the claimed formula follows.

**Every reduction, followed:**

| step | lands at | status |
|---|---|---|
| "$\mathtt{tb}(K)$ as $\mathtt{lk}(K,K')$, $K'$ pushed transverse to $\xi$" | **Def. 3.5.4, p. 115** ("if we choose a vector field along $K$ transverse to $\xi$ and define a parallel knot $K'$ by pushing $K$ along this vector field, then $\mathtt{tb}(K)$ equals $\mathtt{lk}(K,K')$"), resting on **Def. 3.5.1, p. 114** (contact framing) and **Def. 3.5.2, p. 114** (surface framing) | **read, complete** |
| admissibility of pushing in $z$ | **Ex. 3.5.8, p. 116** ("the vector field $\partial_z$ is everywhere transverse to $\xi_{st}=\ker(dz+x\,dy)$") | **read**; and $\alpha_{st}(\partial_z)=1\neq0$ re-checked here |
| "$\mathtt{lk}$ by counting crossings of $K'$ under $K$ with sign" | **Prop. 3.4.14, p. 113**, statement; **proof completes on p. 114** | **statement and proof read; complete.** Proof: a positive undercrossing of $K'$ under $K$ becomes an overcrossing by replacing $K'$ with $K'-\mu$, a negative one by $K'+\mu$; if $n$ is the signed total then $K'-n\mu$ crosses over $K$ everywhere, so $\mathrm{lk}(K,K'-n\mu)=0$ and $\mathrm{lk}(K,K')=n$ |
| "the writhe" | p. 116, definition + Fig. 3.11 signs, and orientation-independence argued | **read** |
| "#left cusps = #right cusps" | not referenced; a front of a closed curve alternates left/right cusps | **asserted** in the proof (see §4) |

**The chain registry L-3 names — "Proposition 3.4.14, Definitions 3.5.1 and
3.5.4, Example 3.5.8, pp. 111–117" — resolves exactly**: p. 111 carries
Def. 3.4.10 (the linking number), p. 113 Prop. 3.4.14, p. 114 Def. 3.5.1,
p. 115 Def. 3.5.4, p. 116 Ex. 3.5.8, p. 117 Prop. 3.5.9. **This seat confirms
the Codex bench's 15:55Z read.** The registry may drop "pending the seat's
confirmation".

**Delta between what Geiges proves and what SM6 uses:** Geiges partitions the
cusps into *left/right*; SM6 into *downward/upward* ($D,U$). These are different
partitions of the same set, but SM6 uses only the **total**, and
$\#\mathrm{cusps}=D+U$ is exactly what its own parenthetical asserts and what
Etnyre's eq. (5)/(7) pairing requires. **No gap.**

## 2. Geiges book, Prop. 3.5.32, p. 127 — the front-writhe identity

**Proof as printed:**

> This argument is completely analogous to that used for proving
> Proposition 3.5.11. We can take $X=\partial_x$ in the definition of
> $\mathtt{sl}(K)$. This means that $K'$ is obtained from $K$ by pushing it
> vertically (with respect to the front projection). Hence, by a small isotopy
> we may assume that the front projection of $K'$ is a parallel curve to the
> front projection of $K$. We then observe that each crossing of the front
> projection of $K$ contributes a crossing of $K'$ underneath $K$ of the
> corresponding sign. By Proposition 3.4.14 this implies
> $\mathtt{sl}(K)=\mathtt{lk}(K,K')=\mathrm{writhe}(K)$, as claimed.

**Reductions, followed:**

| step | lands at | status |
|---|---|---|
| "$X=\partial_x$ in the definition of $\mathtt{sl}(K)$" | **Def. 3.5.28, p. 125** | **read.** $\alpha_{st}(\partial_x)=0$ re-checked, so $\partial_x$ is a nowhere-zero section of $\xi_{st}$ — the definition applies |
| legitimacy of *choosing* $X$ | **Rem. 3.5.29(2), p. 126** | **read; asserted there** ("follows by the argument used in the proof of Lemma 3.5.14"). Lemma 3.5.14, p. 118, and its proof were read and do carry that argument (a trivialisation is determined along the 1–skeleton; $\partial\Sigma$ is a product of commutators, so any two trivialisations have zero relative rotation) |
| dropping $\Sigma$ from the notation | **Cor. 3.5.31, p. 127** ($e(\xi)=0\Rightarrow$ independence of $\Sigma$) | **read**; applies on $\RR^3$ |
| the front of a transverse knot has no cusps | **p. 100**, first consequence of $z'+xy'>0$: "if $y'=0$, then $z'>0$" | **read.** This is what removes the cusp correction Prop. 3.5.9 carries |
| "By Proposition 3.4.14" | **p. 113** | **statement and proof read; complete** (§1) |

**Reading note on "vertically".** Geiges's front projection is
$\gamma_F=(y,z)$ (Def. 3.2.2, p. 96, read), so a push along $\partial_x$ does
not move the front projection at all. "Vertically (with respect to the front
projection)" must be read in the **fibre** sense — along the fibre of the
projection — and that reading is forced by the very next sentence, which needs
a "small isotopy" to turn the coincident projections into a *parallel curve*.
Under any other reading the sentence is false. Recorded as an ambiguity in the
source's wording, not an error, and **independently reproducing the SM1 L-3
seat's reading** (`L-3/T2_PROOF.md` §1).

## 3. Geiges survey, Lemma 3.3, p. 46 — the same identity, second witness

**Proof as printed:**

> Let $\gamma'$ be the push-off of $\gamma$ as described. Observe that each
> crossing of the front projection of $\gamma$ contributes a crossing of
> $\gamma'$ underneath $\gamma$ of the corresponding sign. Since the linking
> number of $\gamma$ and $\gamma'$ is equal to the signed number of times that
> $\gamma'$ crosses underneath $\gamma$ (cf. [98, p. 37]), we find that this
> linking number is equal to the signed number of self-crossings of $\gamma$,
> that is, $l(\gamma)=w(\gamma)$.

**The one external reduction, followed to where it lands.** Reference **[98]**
of the survey is, at the survey's own bibliography (printed p. 85, read):

> [98] N. Saveliev, *Lectures on the Topology of 3–Manifolds*, de Gruyter,
> Berlin (1999).

**Not on disk.** This is *not* an escalation, and it is not a fetchability
dismissal either — the reason is positive: the fact it is cited for ("the
linking number equals the signed number of times $\gamma'$ crosses underneath
$\gamma$") is **proved on disk, completely, at Geiges book Prop. 3.4.14,
p. 113**, which SM6 already carries through its book citation. So **the
front-writhe chain on SM6 has no off-disk dependency**, and registry L-3's
parenthetical "one reduction … to a book not on disk" now describes a
redundancy rather than a residue. (Recorded in `ACCESS_AUDIT.md` §2.)

Also read at p. 45, because `rem:sl-convention` cites it: the **section
independence argument**, printed in full — the difference of the two
self-linking numbers is the degree of a map $\gamma\to S^1$ which factors
through $\RR^3$, hence zero on $H_1$. Complete as printed for $\RR^3$, which is
the setting SM6 uses. **T2.**

## 4. What is asserted rather than computed, named

Three picture-level clauses inside otherwise complete printed proofs. None is a
reduction to unproved material; each is a step *inside* a proof. **No
substitute is printed here.**

1. Geiges book Prop. 3.5.32: *"each crossing of the front projection of $K$
   contributes a crossing of $K'$ underneath $K$ of the corresponding sign"* —
   with the implicit "and nothing else does". The "small isotopy" is not
   specified and no side is chosen for the offset. (Choosing the side is
   harmless: $\pm X$ give the same $\mathtt{sl}$ by Rem. 3.5.29(2).)
2. Geiges book Prop. 3.5.9: *"It is easy to see that a self-crossing … a cusp
   on the right … a cusp on the left …"*, and *"there are as many cusps on the
   left as cusps on the right"*.
3. Etnyre eq. (5): *"One may easily check that the intersection will be
   positive when going down a cusp and negative when going up a cusp."*

The SM1 seat recorded (1) and this seat reaches the same list; (2) and (3) are
added here because SM6 now consumes those two locators, which SM2 either did
not cite or cited without the Geiges witness.

## 5. Etnyre, read at proof depth where SM6 still leans on him

- **eq. (5), p. 14 — T2.** The argument is printed at the locator: trivialize
  $\xi|_L$ by $w=\partial_y$; count signed crossings of the tangent $v$ with
  $\pm w$, which in the front projection occur exactly at cusps; halve. One
  "easily check" clause (§4.3). Read.
- **eq. (7), p. 14 — below T2.** Its argument pushes along $v=\partial_z$,
  which is **transverse to $\xi$ and not inside it**, and is licensed only by
  **Remark 2.14, p. 13**: *"If $v'$ is a nonzero vector field along $L$
  transverse to $\xi$ and $L''$ is obtained from $L$ by pushing $L$ slightly in
  the direction of $v'$ then $tb(L)=\mathrm{lk}(L,L'')$."* — **stated with no
  proof and no reference.** Read at the bytes; confirms the SM2 seat's finding
  and confirms SM6's own parenthetical. **The T2 witness SM6 supplies for this
  clause is Geiges Prop. 3.5.9 (§1), where the corresponding fact is Def. 3.5.4
  itself, i.e. definitional rather than remarked.**
- **Lemma 2.22, eq. (17), p. 19 — T2.** Full printed proof, read: with $\tau$ a
  nonzero section of $\xi|_L$ extending over $\Sigma$, $r(L)=t(v,\tau,\xi|_L)$
  and $tb(L)=t(w,s,\nu)$; then
  $sl(L_+)=t(\tau_+,s,\nu)=t(\tau_+,w_+,\nu)+t(w_+,s,\nu)=t(\tau,w,\xi)+t(w,s,\nu)=-r(L)+tb(L)$,
  the $L_-$ case by $\nu=-\xi$. Closed by □. Two compressions named: the
  twisting-number additivity $t(a,c)=t(a,b)+t(b,c)$ is used without statement,
  and "$\nu=\xi|_{L_+}$" is asserted from the definition of the pushoff. Neither
  is a reduction to unproved material.
- **eq. (9), p. 15 — T1 with defects, unchanged.** The whole justification is
  *"The argument for this formula is exactly like the one for Equation (8)"*,
  and eq. (8) is the **Lagrangian** formula $tb(L)=\mathrm{writhe}(\pi(L))$,
  whose own justification is the informal "think about trying to pull $L'$
  straight up". The deferral crosses the projection gap: in the front
  projection the analogous $tb$ statement is eq. (7), which carries a cusp
  correction eq. (8) does not, and what makes that correction vanish for a
  transverse front is not stated at the locator. Re-read at the bytes; this seat
  reaches the SM1 and SM2 seats' finding independently.

## 6. Available at T2 but not cited — corroborations, not repairs

Recorded because rule 8 wants the campaign as close to the published literature
as possible, and because these would remove the last two clauses that rest on
Etnyre alone if the curator ever wants them to.

- **Geiges book Prop. 3.5.19, p. 121**, statement and **printed proof p. 122
  read**: for an oriented Legendrian knot in $(\RR^3,\xi_{st})$ cooriented by
  $\partial_z$, $\mathrm{rot}(K)=\lambda_--\rho_+=\rho_--\lambda_+=\tfrac12(c_--c_+)$
  with $c_\pm$ the total numbers of cusps oriented up/down. **This is Etnyre
  eq. (5)** with $c_-=D$, $c_+=U$. Caveat before any substitution: the sign of
  $\mathrm{rot}$ depends on the orientation of $\xi$ (Geiges Rem. 3.5.13,
  p. 118), his trivialisation is $e_1=\partial_x$, $e_2=\partial_y-x\partial_z$
  in **his** letters, and Etnyre's is $w=\partial_y$ in his — so the transport
  of the sign needs its own line. Not needed on SM6, since eq. (5) is already
  T2.
- **Geiges book Prop. 3.5.36, pp. 128–129**, statement and **printed proof
  read**: $\mathtt{sl}(K_\pm,\Sigma)=\mathtt{tb}(K)\mp\mathrm{rot}(K,[\Sigma])$
  — the published proof of exactly SM6's third formula. Also Rem. 3.5.37,
  p. 129: Bennequin's opposite naming of $\gamma^\pm$, "This has led to some
  sign errors in the literature" — the pushoff-naming trap, which SM6 and both
  sources handle explicitly.

## 7. T2 delta — verdict

**T2 is reached for every clause of L-3 that SM6 consumes**, through the
citations SM6 prints, at the pages SM6 prints. The two clauses that were below
T2 on SM2 (the Legendrian $tb$; the front-writhe identity) are carried on SM6 by
**Geiges book Prop. 3.5.9 p. 117** and **Geiges book Prop. 3.5.32 p. 127 /
survey Lemma 3.3 p. 46**, all read at proof depth here; the identification
clause is carried by **Etnyre §§2.6.3–2.6.4 p. 15 and Geiges survey Def. 3.2
p. 45**, also read.

**Deflation, explicitly.** "T2 reached" means: the statement is at the cited
locator, and the source's printed proof was read and followed. It does **not**
mean the campaign has an independent proof of any of these, and it does **not**
upgrade Etnyre eq. (9), which stays a "states it" citation. Three picture-level
steps inside the printed proofs are asserted rather than computed (§4); this
seat printed no substitute for any of them.
