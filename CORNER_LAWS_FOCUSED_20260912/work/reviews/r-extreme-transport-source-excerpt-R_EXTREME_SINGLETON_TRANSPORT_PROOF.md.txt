# R local complement — extreme singleton transports

Status: **PROVED intermediate lemma**, conditional only on accepted R-LOC,
R-PAR and R-EXTERIOR plus the manuscript's HOMFLY, grouped-carrier, rotation
and carrier-floor interfaces.  This is not yet a sealed R-chain claim pack.

The establishing statements and proofs of R-LOC-2, R-PAR-v6, and
R-EXTERIOR-1 are printed in `R_ATTACHMENT_WARRANTS.md`, sections
"R-LOC-2 — localization", "R-PAR-v6 — parity and availability", and
"R-EXTERIOR-1 — the triangle-disjoint factor". The shorter names R-LOC,
R-PAR, and R-EXTERIOR below denote those same statements.

## Statement and canonical data

Fix a full-availability fiber at a simple RIII wall in the extreme graph orbit,
an outside support `Q`, and the canonical words

```text
H = x y A z x B y z C             (local graph K3),
L = y x A x z B z y C             (local graph empty).       (1)
```

Full availability is part of the statement: every member of
`T={x,y,z}` is nonadjacent to `Q`, so every `Q union {j}` is independent on
both sides.  R-LOC-2 clause 4 identifies the two extreme local graphs in (1):
`H[T]=K3` if and only if `L[T]` is empty.

Here `A,B,C` denote the boundary successor strings after smoothing `Q` first;
closed successor cycles internal to a gap are triangle-disjoint spectators.
Write `T_nu(J)` for the complete X1 term of `Q union J`, with an absent row
read as zero.  Then, separately and without a symmetry assumption,

```text
T_H(x)=T_L(x),       T_H(y)=T_L(y),       T_H(z)=T_L(z).       (2)
```

Let the oriented strand directions be `u1,u2,u3`, with
`x=(u1,u2)`, `y=(u1,u3)`, and `z=(u2,u3)`.  The exact line-order calculation
for the extreme orbit gives

```text
s_x=sgn det(u1,u2)=sigma,
s_y=sgn det(u1,u3)=-sigma,
s_z=sgn det(u2,u3)=sigma.                               (3)
```

Indeed, if `delta` is the three-line-determinant sign and `q_i` records the
order of the other two intersections along `u_i`, the Cramer identities give

```text
(q_1,q_2,q_3)=-delta(s_x s_y,s_x s_z,s_y s_z).
```

The three local graph indicators agree exactly when `q=(-,+,-)` or
`(+,-,+)`, which is equivalent to (3).  This is the algebraic classification,
not a measured census.

On the empty side, the gap side-vectors relative to `(x,y,z)` may be based at
`C` and read as

```text
A=(1,1,0),       B=(0,1,1),       C=(0,0,0).           (4)
```

Thus a chord joining `A-B`, `A-C`, or `B-C` has mask `xz`, `xy`, or `yz`,
respectively.  R-PAR says that after selecting one local crossing every
outside survivor has mask zero or the complementary two-letter mask.  Direct
successor calculation in (1) now gives the following three distinct rows:

```text
j  common  affected  H successor rows        L affected residual word  q  r  survivor mask
x    A       BC      y A z | B y z C         z B z y C y               y  z       yz
y    C       AB      A z x B | z C x         x A x z B z               x  z       xz
z    B       CA      x B y | C x y A         y C y x A x               y  x       xy.       (5)
```

Because full availability and `L[T]` empty make
`S_full=Q union {x,y,z}` an independent L-side support, its three outer
triangle-touching carriers are canonically indexed by the gap strings
`G=A,B,C`; call them `L_G`.  Bind their complete grouped data by

```text
Q_G(a,z)=P_(S_full,L_G),   f_G(a)=[z^0]Q_G(a,z),
w_G=w_(S_full,L_G).                                      (5a)
```

If `L_G` bears no residual piece, the empty-carrier convention gives
`Q_G=f_G=1` and `w_G=0`.  Thus the symbols `f_A,f_B,f_C` and their writhes
below include the piece-free cases and do not denote untyped subloops.

In the `H` column the other two local crossings are dominated and have one
visit on each displayed carrier; deleting their visits leaves the clean rows
shown in the `common/affected` columns.  On `L` they survive as the two positive
self-crossings `q,r` of the affected carrier.  Formula (4) also says that every
two-letter-mask survivor has one visit in each of the two affected gaps.

## 1. Common carrier data and the affected diagrams

The arbitrary-`Q` successor lift acts independently inside `A,B,C`.  R-LOC
keeps the outside survivor set and every outside-to-outside interlacement edge.
After deleting the displayed local visits, (5) therefore identifies the common
carrier and the clean affected carrier across the wall, together with their
residual owners and signed piece records.  `def:record`, `ax:gausscode`, and
`cor:groupedknot`, clauses (A) and (B), give equal grouped polynomials and
writhes on the common carrier and on every triangle-disjoint spectator.

The two local carriers themselves pass continuously through the smoothed RIII
family.  The unselected local crossings are not corners.  Every polygon,
`Q`-smoothing, and selected-local smoothing corner stays guarded; the triple
collision creates no corner.  Hence `lem:turnlift(ii)` preserves the signed
and absolute rotations, while the fixed corner-sign lists preserve the
weights.  The selected smoothing corner on the affected carrier and its mate
on the common carrier are, row by row,

```text
j=x: affected u1 -> u2 has sign  sigma; common has -sigma,
j=y: affected u3 -> u1 has sign -s_y=sigma; common has -sigma,
j=z: affected u2 -> u3 has sign  s_z=sigma; common has -sigma.   (6)
```

Thus the complete selectors match across `H,L`.  R-EXTERIOR supplies one
additional common factor `C_Q` from every triangle-disjoint carrier; it may be
zero and will not be cancelled.

Fix one row of (5).  Let `D_0` be the clean affected grouped knot on `H`, and
let `D_+` be the affected grouped knot on `L`, including `q,r`.  Write their
polynomials `F_0,F_+`, their common absolute carrier rotation `R`, and their
writhes `w_0,w_+`.  The two local crossings of `D_+` are positive.  Switching
`q` makes it negative; the adjacent local port pairs then make `q,r` an empty
opposite-sign oriented RII pair.  Deleting it leaves exactly `D_0`, including
all outside records.  This is visible separately in the three printed words:
the two empty bigon edges are the adjacent `r q` and cyclic `q r` local visits;
the gap strings lie on the two complementary outer arcs and are untouched.
Each constituent subarc between adjacent triangle visits lies in one straight
bundle edge and therefore contains no polygon vertex; the only join between
such subarcs is the already-selected `j`-smoothing connector.  R-LOC's clump
adjacency excludes every outside crossing visit from each constituent subarc.
By the isolated simple-event hypothesis, choose the RIII disc small enough to
contain the whole resulting bigon and no outside strand, crossing, or vertex.
Thus no spectator lies in its lens and smoothing `Q` cannot obstruct the local
oriented RII isotopy.

Consequently

```text
w_+=w_0+2,       R(D_+)=R(D_0)=R,
d_+=d_0-2,       where d_nu=1-w_nu-R.                 (7)
```

With `(D_L,D_H,D_A)=(D_0,D_+, smooth_q(D_+))`, all hypotheses of
`lem:fulltwist` are now typed.  It gives

```text
Omega_+-Omega_0 = [a^(d_0-1) z^(-1)] P(D_A),          (8)
```

where `Omega_nu=[a^(d_nu)z^0]F_nu`.

## 2. The auxiliary components and exact owner map

Let `D_A=smooth_q(D_+)`, as in (8), with the smoothing performed on the
L-side diagram.  Since `S_full` is independent there, its subset
`Q union {j,q}` is a legitimate L-side support.  Smoothing `q` splits `D_+`
into two components.  The rowwise component table is

```text
j=x, q=y, r=z:       C       | z B z,
j=y, q=x, r=z:       A       | z B z,
j=z, q=y, r=x:       C       | x A x.                 (9)
```

Here is the exact owner statement.  Every complementary-mask retained label
has one visit on each component of (9), so it is mixed.  Every mask-zero label
has both visits in one displayed gap, and its restricted cyclic record,
pairing, over/under role and sign are exactly those of the corresponding
full-support outer carrier `L_G`.  Thus the first component has the `L_G`
self-record named on the left.  The second has the `L_G` self-record named
inside `r G r`, together with the one additional self-crossing `r`.

That `r` is a singleton residual piece follows inside the legitimate support
`Q union {j,q}`: any outside survivor adjacent to `r` has the complementary
two-letter mask from (5), hence is also adjacent to selected `q` and is
dominated, whereas mask-zero pieces in `G` remain and are nonadjacent to `r`.
The one-positive-crossing diagram of `{r}` is an unknot, with polynomial one
and writhe one.  Consequently `def:record`, `ax:gausscode`, and
`cor:groupedknot`, clauses (A) and (B), give the exact component data

```text
j=x: polynomials (Q_C,Q_B), component writhes (w_C,w_B+1),
j=y: polynomials (Q_A,Q_B), component writhes (w_A,w_B+1),
j=z: polynomials (Q_C,Q_A), component writhes (w_C,w_A+1).   (9a)
```

In particular the second component polynomial is `Q_G`, despite its diagram
writhe being `w_G+1`.  Taking `z^0` rows gives

```text
(f_1,f_2)=(f_C,f_B), (f_A,f_B), (f_C,f_A)             (10)
```

in the three respective cases.  Since every mixed retained crossing is
positive, if `ell` is the linking number of the two components then exactly
`2 ell` complementary-mask crossings occur.  The knot-parity clause of
`ax:homfly` gives
`[z^0](Q_1 Q_2)=([z^0]Q_1)([z^0]Q_2)=f_1 f_2`.  Then
`lem:homflyrows(ii)` gives

```text
[z^(-1)]P(D_A)=a^(-2 ell)(a-a^(-1)) f_1 f_2.          (11)
```

This uses neither a split-link assertion nor a componentwise factorization of
the mixed crossings: they enter only through `ell`.

## 3. Rotation and floor ledger

If the common singleton selector is zero, the matched selector ledger already
makes both terms in (2) zero.  Assume it is nonzero.  Then the affected
singleton carrier is uniform; by (6), all its corners have sign `sigma`.

The two successive smoothings `q,r` split that carrier into the two clean outer
carriers of (10) and the central triangle.  Their exact local-corner ledger is

```text
j=x: q=y gives C its -sigma corner; r=z gives B its -sigma corner,
j=y: q=x gives A its -sigma corner; r=z gives B its -sigma corner,
j=z: q=y gives C its -sigma corner; r=x gives A its -sigma corner. (12)
```

The other daughter at each step has local corner `+sigma`; after both steps
these are the three central-triangle corners.  Thus each clean outer carrier
has exactly one `-sigma` local corner and all inherited corners have sign
`sigma`.  By `lem:selectorid(A)` it has at least two inherited corners, so it is
exactly one-dissent, never uniform with the wrong sign.  After a possible
global orientation reversal, `lem:uniformrot(ii)` makes both outer signed
rotations have sign `sigma`; the central triangle also has sign `sigma` and
absolute rotation one.

At each oriented smoothing the two new principal turns have opposite signed
sum and every inherited turn is unchanged.  `lem:turnlift(ii)` therefore makes
signed rotation additive.  Writing `R_i` for the two outer absolute rotations,

```text
R_1+R_2+1=R.                                           (13)
```

Let `w_i` be the full-support clean outer grouped writhes from (5a),
`d_i=1-w_i-R_i`, and `D=d_1+d_2`.  The clean affected diagram `D_0` contains
the two outer self-crossing sets and the `2 ell` positive crossings which
become mixed in `D_A`.  Hence

```text
w_0=w_1+w_2+2 ell.                                    (14)
```

Using (13) and (14), with each nontrivial algebraic step displayed,

```text
D = 2-(w_1+w_2)-(R_1+R_2)
  = 2-(w_0-2 ell)-(R-1)
  = 3-w_0-R+2 ell
  = d_0+2+2 ell.                                      (15)
```

For each clean outer carrier bearing pieces, `cor:groupedknot` supplies a
positive knot diagram with no triple point.  Genericity supplies finitely many
transverse crossings, nonzero principal turns of magnitude below `pi`, no
crossing at a corner, and no corner on a nonincident edge.  Together with the
exact one-dissent ledger (12), this discharges every hypothesis of
`thm:carrierfloor`, after a possible orientation reversal.  A piece-free outer
carrier is covered by `thm:carrierfloor(D)`; if a row `f_i` is zero the support
claim is vacuous.  Therefore `f_1 f_2` has no `a`-exponent below `D`.

Substitute (11) into (8).  Extracting the two monomials of `a-a^(-1)` gives

```text
Omega_+-Omega_0
 = [a^(d_0-2+2 ell)] f_1 f_2
   -[a^(d_0+2 ell)] f_1 f_2
 = [a^(D-4)] f_1 f_2-[a^(D-2)] f_1 f_2
 = 0.                                                  (16)
```

The last equality is exactly the floor, not an assumed sharpness statement.

## 4. Complete-term transport and guards

The common carrier read, every triangle-disjoint spectator read, and all
weights are identical across the wall.  Equation (16) identifies the only
remaining affected read.  Multiplying these equalities proves all three
identities (2), including selector-zero, coefficient-zero, empty-carrier,
`ell=0`, and `C_Q=0` cases.  No factor was cancelled or divided out.

This proof uses no permutation of `A,B,C`: the three rows and their choices of
`q,r` are printed separately.  It invokes neither `ax:R`, `thm:main`, nor an
aggregate S7 conclusion.  The only full-twist invocation is the branch-neutral
abstract lemma after its diagrams, RII port relation, writhe shift, rotation
shift, auxiliary components, owners, and coefficient slots have all been
re-established above.
