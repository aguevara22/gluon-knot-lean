# RIII attachment — the establishing local warrants

This file supplies the statements and proofs denoted by R-LOC-2,
R-PAR/R-PAR-v6, and R-EXTERIOR in the four accompanying core proofs.
R-LOC means R-LOC-2; R-PAR means R-PAR-v6; R-EXTERIOR means R-EXTERIOR-1.
Manuscript labels refer to frozen frame CV. Full availability means that
the availability set defined in R-PAR-v6 below equals the three-element
local crossing set T. These proofs use the stated manuscript interfaces;
they do not assume ax:R. The historical source and review hashes are
recorded in the accompanying evidence pack, not used as printed warrants.

## R-LOC-2 — localization

### Statement

Let $t\mapsto P(t)$ be a simple transversal Reidemeister-III event with zero set
exactly the forced bundle
$Z=\{\mathrm{G3}_{e,f,g},\mathrm{G4}_{e;f,g},\mathrm{G4}_{f;e,g},
\mathrm{G4}_{g;e,f}\}$, $e<f<g$ pairwise remote and concurrent at $t=0$ at a
point interior to all three. Let $T=\{x_{ef},x_{eg},x_{fg}\}$. Then on a
punctured neighbourhood of $t=0$:

1. the crossing set, indexed by carrying edge pairs, is constant;
2. on each of $e,f,g$ the two crossings of $T$ carried by that edge occupy
   adjacent crossing-visits of the traversal circle, and their order along that
   edge is opposite on the two sides;
3. every other pair of crossings keeps its order along every edge;
4. hence $G^{+}=G^{-}\ \triangle\ \binom{T}{2}$: the three internal pairs of $T$
   toggle and no other pair changes.

**Corollary.** The induced graph $G[T]$ maps to its **complement** in $T$
across the wall. Both orbits of that map occur — the extreme orbit
(empty $\leftrightarrow$ complete) and the one-edge $\leftrightarrow$ two-edge
orbit.

### Proof

**(1) The crossing set is constant.** A double point of a pair $(a,b)$ exists
exactly when the relative interiors of $a,b$ meet, and by continuity can appear
or disappear only through an endpoint of one segment lying on the other — a
$\mathrm{G2}$ predicate vanishing with the vertex *on the segment*. That is the
argument `lem:silence`'s proof runs. No $\mathrm{G2}$ member lies in $Z$, so
every relevant $\mathrm{G2}$ is nonzero on a neighbourhood by `lem:guardconst`.

**(2a) The order along each bundle edge reverses — with the $\mathrm{G5}$
factors made explicit (repair 2).** `def:guarded` defines
$$\mathrm{G4}_{e;f,g}=\det(d_f,p_f-p_e)\det(d_g,d_e)-\det(d_g,p_g-p_e)\det(d_f,d_e).$$
Writing $t_f$ for the parameter along $e$ of the crossing $x_{ef}$, the line
intersection gives $t_f=\det(d_f,p_f-p_e)/\det(d_f,d_e)$, and hence the
factorization
$$\mathrm{G4}_{e;f,g}=(t_f-t_g)\,\det(d_f,d_e)\,\det(d_g,d_e)
 =(t_f-t_g)\,\mathrm{G5}_{e,f}\,\mathrm{G5}_{e,g},$$
the last equality up to the sign convention $\mathrm{G5}_{e,f}=\det(d_e,d_f)$,
whose two reversals cancel in the product. Therefore
$$\operatorname{sgn}\mathrm{G4}_{e;f,g}
=\operatorname{sgn}(t_f-t_g)\cdot\operatorname{sgn}\mathrm{G5}_{e,f}
\cdot\operatorname{sgn}\mathrm{G5}_{e,g}.$$
$\mathrm{G5}_{e,f}$ and $\mathrm{G5}_{e,g}$ are **active** ($f$ and $g$ both
cross $e$), hence relevant, and neither lies in $Z$; so by `lem:guardconst` each
is nonzero with constant sign on a neighbourhood of $t=0$. $\mathrm{G4}_{e;f,g}$
lies in $Z$ and changes sign at $t=0$ by transversality. With the two
$\mathrm{G5}$ signs constant, the sign change is carried by $t_f-t_g$ alone:
the order of $x_{ef}$ and $x_{eg}$ along $e$ reverses. Identically on $f$ and
$g$.

**(2b) Adjacency, by a germ argument (repair 1).** I do **not** assume an
intervening crossing persists on both sides. Suppose no punctured neighbourhood
of $0$ is free of intervening crossings. Then there are $t_n\to0$, on one side
say, and crossings $y_n$ lying between $x_{ef}$ and $x_{eg}$ along $e$ at $t_n$.
By (1) the crossing set is finite and constant near $0$, so some fixed crossing
$y=x_{eh}$ recurs for infinitely many $n$; pass to that subsequence. Along it, $y$'s
parameter on $e$ lies between those of $x_{ef}$ and $x_{eg}$, both of which tend
to the parameter of the concurrency point. By continuity $t_y(0)=t_{f}(0)$, so
$\mathrm{G4}\langle e;f,h\rangle$ — the member-valued accessor of
`def:guarded`, active since $f$ and $h$ both cross $e$ — vanishes at
$t=0$. It is not in $Z$, contradicting both simplicity (the zero set at $t=0$ is
exactly $Z$) and `lem:guardconst`. Hence some punctured neighbourhood is free of
them. The traversal sub-arc joining the two visits lies inside the edge $e$, so
it carries no vertex either, and the two visits are adjacent among crossing
visits.

**(3) No other order changes (repair 3).** The cyclic order of crossing visits
on $\Gamma$ is determined by the order of crossings along each edge together
with the fixed cyclic order of the edges and their vertices. For any edge $h$
and any pair of crossings on it other than a bundle pair, the corresponding
$\mathrm{G4}_{h;\cdot,\cdot}$ is active and outside $Z$, hence nonzero of
constant sign on a neighbourhood by `lem:guardconst`; by the factorization in
(2a), with its two $\mathrm{G5}$ factors likewise active, outside $Z$ and
sign-constant, the parameter difference keeps its sign and the order is
unchanged. No vertex moves in the cyclic order. With (1) there are no births or
deaths. So the two Gauss words differ by exactly the three transpositions of
(2a), each adjacent by (2b).

**(4) Localization.** Consider one transposition, of adjacent visits $u$ of
crossing $a$ and $v$ of crossing $b$, $a\neq b$. For any pair $\{c,d\}\neq
\{a,b\}$ the interlacement is unchanged: the transposition moves $u$ past $v$
and nothing else, and if say $u$ is a visit of $c$ then $v$ is a visit of
neither $c$ nor $d$, so $u$'s position relative to the other three points is
unaffected. For $\{a,b\}$ it toggles: with $a$'s visits $u,u'$ and $b$'s $v,v'$,
the pair is interlaced exactly when precisely one of $v,v'$ lies in the arc
$(u,u')$; $u$ and $v$ being adjacent, the arc between them holds no marked
point, so $v$ passes from one side of $u$ to the other while $u',v'$ stay put,
flipping that membership and with it the alternation. Each of the three
transpositions involves a distinct pair of $T$, so each internal pair toggles
exactly once and nothing else moves. $\qquad\blacksquare$

## R-PAR-v6 — parity and availability

### Statement

Let $t\mapsto P(t)$ be a simple transversal Reidemeister-III event with
triangle $T=\{x_{ef},x_{eg},x_{fg}\}$, and let $P$ be either side's polygon,
near the wall. Then:

**(P1) Parity.** Every crossing $y\notin T$ interlaces exactly $0$ or exactly
$2$ of the three crossings of $T$ — never $1$, never $3$. Moreover the
interlaced pair, when nonempty, is one of $\{x_{ef},x_{eg}\}$,
$\{x_{ef},x_{fg}\}$, $\{x_{eg},x_{fg}\}$ — the two crossings sharing one of the
three bundle edges.

**(P2) Trichotomy.** For any set $S'$ of crossings disjoint from $T$, the set
$\mathrm{avail}(S')=\{x\in T: x$ interlaces no member of $S'\}$ has size $3$,
$1$, or $0$ — never $2$. And $\mathrm{avail}(S')$ is the same set on the two
sides of the wall.

### Proof

**Clumps.** By R-LOC (2), on each bundle edge the two triangle visits occupy
adjacent crossing-visits of $\Gamma$. Write the three adjacent pairs as clumps
$C_e=\{$visits of $x_{ef},x_{eg}$ on $e\}$, $C_f$, $C_g$. Each crossing of $T$
has one visit in each of two clumps: $x_{ef}$ in $C_e$ and $C_f$, $x_{eg}$ in
$C_e$ and $C_g$, $x_{fg}$ in $C_f$ and $C_g$.

**(P1).** Let $y\notin T$ with visits $u,v$. These are crossing-visits, and no
crossing-visit lies between the two members of a clump (adjacency), so neither
$u$ nor $v$ lies inside a clump: each clump lies wholly in one of the two arcs
that $u,v$ cut $\Gamma$ into. This is a $2$-colouring
$\chi:\{C_e,C_f,C_g\}\to\{1,2\}$. A crossing of $T$ interlaces $y$ exactly when
its two visits lie in different arcs, i.e. exactly when its two clumps get
different colours. A $2$-colouring of three objects has either $0$ bichromatic
pairs (monochromatic) or exactly $2$ (the odd object pairs bichromatically with
each of the other two, while those two pair monochromatically). Never $1$,
never $3$. When there is an odd clump $C_h$, the interlaced pair is the two
crossings with a visit in $C_h$ — the two crossings sharing the edge $h$.

**(P2).** $\mathrm{avail}(S')=T\setminus\bigcup_{y\in S'}I(y)$ where, by (P1),
each $I(y)$ is empty or one of the three named pairs. A union of such sets is
empty, one pair (size $2$), or — as soon as two *distinct* pairs occur — all of
$T$, since any two of the three pairs cover the three elements. So the union
has size $0$, $2$, or $3$, and its complement has size $3$, $1$, or $0$.
Wall-invariance is R-LOC's conclusion that no $T$-to-outside interlacement
changes, so each $I(y)$ is the same set on both sides. $\qquad\blacksquare$

## R-EXTERIOR-1 — the triangle-disjoint factor

### Statement

Let `P_-` and `P_+` be the generic sides of a simple transversal RIII event,
and let `T` be the three crossings identified by their carrying edge pairs as
in R-LOC-2.  Fix an outside independent set `Q`, disjoint from `T`.  On either
side `sigma`, let `A` be any subset of `T` for which

```text
S = Q union A
```

is independent.  A carrier of `S` is *triangle-disjoint* when it contains none
of the six traversal visits belonging to `T`, including a selected triangle
crossing's smoothing-site visits.  Define

```text
C_{Q,sigma}(A)
  = product over triangle-disjoint carriers L of
      wt_sigma(L) * Omega_{1,sigma}(S,L).
```

Then `C_{Q,sigma}(A)` is independent of `A`, and its common value is the same
for `sigma=-` and `sigma=+`.  Write that single value as `C_Q`; it may be zero.
Consequently every full-availability row factors exactly as

```text
tau_sigma(A) = C_Q * rho_sigma(A),
```

where `rho_sigma(A)` is the product over the triangle-touching carriers.

### Proof

#### 1. Exterior carriers are fiber-stable

Regard oriented smoothing as reconnecting the traversal circle at the two
visits of each selected crossing.  Distinct selected crossings have disjoint
visit half-edges, so their reconnections commute.  Perform all `Q`
reconnections first.  A resulting `Q`-carrier containing no `T` visit uses no
half-edge at which an `A` reconnection acts, and therefore survives every
`A` reconnection arc-for-arc.  Conversely, a triangle-disjoint carrier after
the `A` reconnections uses none of those changed half-edges; undoing the
`A` reconnections leaves the same closed successor cycle in the `Q` row.

Thus keeping the same traversal arcs is a bijection between the
triangle-disjoint carriers of `Q union A` and the `Q`-carriers having no `T`
visit.  Within one fixed polygon it preserves the polygon-vertex corners, the
`Q` smoothing corners, their cyclic order and directions, and hence `wt`,
`rot`, and `R=|rot|`.

#### 2. Exterior residual pieces are fiber-stable

First prove insulation at the base row.  Let `c in U(Q)` have both visits on a
triangle-disjoint `Q`-carrier `L`, and suppose an available `x in T`
interlaces `c`.  Availability says `x` is neither in `Q` nor adjacent to `Q`,
so `x in U(Q)`.  The edge `c~x` puts them in one connected component of
`G[U(Q)]`, hence in one residual piece.  By `lem:carriers(iv)`, every crossing
of that piece has both visits on one unique carrier.  Since `c` lies on `L`,
that carrier is `L`; it then contains both `T` visits of `x`, contradicting
triangle-disjointness.  Therefore no available triangle crossing interlaces an
undominated crossing carried by `L`.

For `S=Q union A`, independence makes each `a in A` available at the base row,
and directly from `def:pieces`,

```text
U(S) = U(Q) minus (A union N(A)).
```

Any member of `U(Q)` carried by `L` is not in `A` because `L` has no triangle
visit, and is not in `N(A)` by insulation.  Hence the vertices of `U` carried
by `L` are identical in the base and `S` rows.  Their induced edges are fixed,
so their connected components are identical.  No component can acquire or
lose an off-carrier member: `lem:carriers(iv)` assigns every base component
to one carrier, and passing to the smaller induced set introduces no edge.
This is the required residual-piece bijection, piece for piece.

#### 3. The exterior factor is fiber-constant

Step 1 fixes every exterior carrier and its `wt` and `R` within a side.  Step 2
fixes the residual pieces assigned to it.  Since the parent polygon and each
piece label set are literally fixed, `def:piecediagram` gives the same piece
diagram, hence the same `P_H` and `w(H)=|H|`.  Therefore `P_{S,L}`,
`w_{S,L}`, the coefficient slot `1-w_{S,L}-R(L)`, and
`Omega_1(S,L)` are fixed.  Their product with `wt(L)`, over the exterior
carriers, is independent of `A`.

Finally, `def:wind` gives `wind(S)=product_L wt(L)`, while `def:X1` multiplies
all carrier `Omega_1` factors.  Partitioning the carriers into disjoint and
touching classes therefore gives `tau_sigma(A)=C_{Q,sigma}*rho_sigma(A)` as an
identity, including when either factor is zero.  No cancellation and no
division by `C_Q` is used.

#### 4. The same exterior factor serves both wall sides

This is the step for which unchanged visit order alone is insufficient.
R-LOC-2 fixes the crossing labels and carrying edge pairs, changes only three
adjacent pairs of `T` visits, and fixes every other visit order and every graph
edge not internal to `T`.  Erasing the six `T` visits therefore gives the same
marked traversal word on both sides.  Smoothing the same outside support `Q`
in that word canonically identifies the `Q`-carriers without a `T` visit and
preserves their corner lists.

At a polygon-vertex corner the turn sign is the sign of its `G1` member; at a
`Q`-smoothing corner it is the sign of the active `G5` member.  A simple RIII
event's zero set contains only its forced `G3/G4` bundle, so these `G1/G5`
members remain nonzero with constant sign by `lem:guardconst`.  Corner counts
and turn signs agree, hence `wt` agrees.

For rotation, match each principal turn of an exterior carrier on the two
punctured sides.  The carrier avoids the triple-point visits, so its incident
directions have common limits at the wall.  Nonvanishing `G1/G5` prevents a
principal turn from meeting the branch boundary at `+-pi`.  The sum of the
principal turns therefore has the same limit from both sides; by
`lem:turnlift(ii)` each side's sum is `2*pi` times the integer `rot(L)`.  Two
integers whose `2*pi` multiples have the same limit are equal, so `rot` and
`R` agree.

Also `U_-(Q)=U_+(Q)`: R-LOC-2 changes no adjacency incident to `Q`.  A residual
piece assigned to an exterior carrier contains no member of `T`, since
`lem:carriers(iv)` would otherwise put that member's visits on the exterior
carrier.  Its vertex set and induced edges are therefore unchanged, because
the only toggled edges are internal to `T`.  Its restricted records have the
same non-`T` cyclic order and crossing pairs.  Every divide crossing is
positive by definition, and the corresponding active `G5` sign is constant,
so the over/under designation agrees as well.  `lem:piececurve` realizes the
two records by connected generic immersed circles; `ax:gausscode` gives the
same oriented link and `ax:homfly` the same polynomial `P_H`.  The label set
also gives the same writhe `w(H)=|H|`.

Thus every exterior `wt`, `R`, piece polynomial, writhe, slot, and `Omega_1`
agrees across the wall.  Hence `C_{Q,-}=C_{Q,+}=C_Q`.
