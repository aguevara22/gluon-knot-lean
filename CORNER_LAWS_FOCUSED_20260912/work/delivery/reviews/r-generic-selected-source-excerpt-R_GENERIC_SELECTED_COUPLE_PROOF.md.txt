# R local complement — generic selected complementary couple

Status: **PROVED intermediate lemma**, conditional on the accepted R-LOC and
R-PAR statements, on `R_GENERIC_ORBIT_ACTUAL_TABLE.md`
("Earliest remaining interface") and
`R_GENERIC_NONSELECTED_SELECTOR_PROOF.md` ("Oriented line-order calculation"
and "Which pair is selected"), and on the
manuscript interfaces cited below, including `lem:turnlift(ii)`,
`thm:carrierfloor(C),(D)`, `lem:homflyrows(ii)`, and the knot-parity clause of
`ax:homfly`.

The establishing statements and proofs of R-LOC-2 and R-PAR-v6 are printed
in `R_ATTACHMENT_WARRANTS.md`, sections "R-LOC-2 — localization" and
"R-PAR-v6 — parity and availability". The shorter names R-LOC and R-PAR
below denote those same statements.

## Statement

Fix a full-availability fiber at a simple RIII wall in the generic graph orbit
and an exterior independent support `Q`. Relabel the three local crossings so
the exact local words are

```text
P = a b A a c B b c C       (edges ab,bc),
E = b a A c a B c b C       (edge ac).
```

Thus `b` is the degree-two vertex of the path, and `ac` is its complementary
independent pair on `P`. If `T_nu(J)` denotes the complete X1 term of
`Q union J` on side `nu`, absent rows being zero, then

```text
T_E(b) = T_P(b) + T_P(ac).                         (GSC)
```

This is exactly the selected `b/ac` complementary-couple identity, with the
opposite coorientation obtained by multiplying the equation by `-1`.

## 1. Canonical sign branch and successor carriers

Accepted `R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`, "Oriented line-order
calculation" and "Which pair is selected", together with
`R_GENERIC_ORBIT_ACTUAL_TABLE.md`, "Earliest remaining interface", says that the
strand-determinant triple is one of the six nonalternating triples and selects
a unique separating-strand pair. Of the two all-equal listings obtained from
the transitive angular order and its reverse, exactly one is even relative to
the displayed block order. Choose that listing, then use the unique cyclic
relabelling sending the selected separating pair to `ac`. This preserves the
cyclic traversal convention used in `R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`,
"Oriented line-order calculation", and reverses no physical
strand orientation. In the displayed `P/E` labels it gives

```text
sgn det(u1,u2) = sgn det(u1,u3)
               = sgn det(u2,u3) = sigma in {+1,-1}.       (1)
```

This is a relabelling of each of the six generic branches, not an assertion
that the fixed `e<f<g` determinant triple is always all-equal.

The successor calculation, with `A,B,C` standing for the unchanged successor
strings after smoothing `Q`, is

```text
P-b  : C | AB,
E-b  : C | AB,
P-ac : C | A | B.                                      (2)
```

On `P-b`, both `a,c` are dominated by `b`; on `E-b`, they survive and form the
connected residual word

```text
a A c a B c                                             (3)
```

on the `AB` carrier. On `P-ac`, `b` is dominated and the `A` and `B` carriers
are separate. These statements follow directly from the two printed words,
the successor rule in `lem:carriers`, and R-LOC.

## 2. Exact selector and rotation ledger

The local smoothing-corner signs in the three rows are

```text
              C carrier       other carrier(s)
P-b, E-b      sigma            AB: -sigma
P-ac          sigma,sigma      A: -sigma, B: -sigma.     (4)
```

All nonlocal corners partition unchanged according to (2). Consequently,
including the mixed cases rather than cancelling a possibly zero weight,

```text
wt(C_ac)       = -sigma wt(C_b),
wt(A) wt(B)    =  sigma wt(AB).                          (5)
```

For example, if `sigma=+1`, the relevant local turns are left turns: adding
one such corner negates `(-1)^c`. If `sigma=-1`, they are right turns and the
all-right weight stays `+1`. If a carrier on one side is mixed, the partition
in (4) makes the corresponding product on the other side mixed as well, so
(5) remains an equality with both sides zero. Every carrier not shown in (4)
is identical. Hence

```text
wind_P(Q union ac) = -wind_P(Q union b),
wind_E(Q union b)  =  wind_P(Q union b).                 (6)
```

The same local angle ledger gives

```text
rot(C_ac)=rot(C_b),       rot(A)+rot(B)=rot(AB).          (7)
```

`lem:turnlift(ii)` is the typed polygonal instrument here: its principal-turn
formula gives (7). The `P-b` and `E-b` carriers form a path in `R_c` through
the RIII family--no crossing is a corner and every smoothing-corner determinant
remains nonzero--so the same clause makes their signed rotations equal; their
corner signs agree along that nonvanishing path.

If the singleton selector in (6) is zero, the pair selector is zero too and
(GSC) follows immediately. Hence below assume it is nonzero. Then the `A` and
`B` carriers are uniform with the same turn sign `-sigma`; by
`lem:uniformrot(i)` their rotations have that common sign. Thus (7) implies

```text
R(A)+R(B)=R(AB).                                        (8)
```

## 3. The grouped full-twist triple

Let `D_H` be the grouped diagram on the `E-b` `AB` carrier and `D_L` the
grouped diagram on the `P-b` `AB` carrier. In (3), choose the positive crossing
`a` and let `D_0` be its oriented smoothing.

Switching `a` makes `a,c` an empty oppositely signed oriented RII pair; deleting
that pair gives `D_L`. Thus `(D_L,D_H,D_0)` satisfies (T1)--(T2) of
`lem:fulltwist`. The `P-b` and `E-b` `AB` carriers have the same rotation, and
`D_H` has exactly the two additional positive residual crossings `a,c`, so

```text
w_H=w_L+2,       d_H=d_L-2.                             (9)
```

The last equality uses the common absolute rotation, not a diagrammatic
guess.

Smoothing `a` in (3) gives two ordered components. The first inherits the `A`
successor string and the second the `B` string. Full availability first forces
every selected member of `Q` to have local mask zero. R-PAR then supplies the
exact survivor dichotomy needed here: after selecting `b`, an outside survivor
meets neither `a` nor `c`, or it meets both `a` and `c`. Reading the full `E`
word displayed in section 1, rather than residual word (3), the gap
side-vectors relative to `(b,a,c)` are

```text
A=(1,1,0),       B=(1,0,1),       C=(0,0,0).            (9a)
```

Thus a mask-zero crossing has both visits in one gap/component and is exactly
a residual crossing of the corresponding `P-ac` carrier. A mask-`ac` crossing
has one visit in `A` and one in `B`; it is dominated by `ac` in the pair row
and is a mixed crossing of `D_0`, entering only its linking number. The local
crossing `c` is mixed as well.

After deleting those mixed crossings from the component records, the retained
visits, cyclic order, over/under designations, and positive crossing signs are
exactly the records on the `P-ac` `A` and `B` carriers. This is the same
record-level argument as `lem:triplebridge(ii)`, now derived from the RIII
words and masks rather than importing that lemma's S7 binder. By
`lem:carrierword`, `def:record`, `ax:gausscode`, and `cor:groupedknot`, the two
component polynomials are the pair-row grouped polynomials `Q_A,Q_B`; the
empty-carrier case is `thm:carrierfloor(D)`.

Put

```text
f_A=[z^0]Q_A,  f_B=[z^0]Q_B,
d_i=1-w_i-R_i, omega_i=[a^d_i]f_i,  D=d_A+d_B.
```

If `ell` is the linking number of the ordered components of `D_0`, counting
crossings gives

```text
w_L=w_A+w_B+2 ell-1.                                   (10)
```

The `-1` removes the local mixed crossing `c`, which contributes to `2 ell`
but is absent from `D_L`; every outside mixed crossing occurs in both counts.
Using (8) in the slot definitions, (10) becomes

```text
D=d_L+2 ell.                                            (11)
```

No assertion that `ell=0` or that `D_0` is split is made.

The `C` carrier in (2) owns the same residual labels in all three rows; its
retained signed cyclic record, grouped writhe, rotation, slot, and read are
the same by the identical successor string and (7). Every other carrier is a
common spectator with the same data. This identifies the complete row factors,
not merely their label sets.

## 4. Exact coefficient extraction

By `lem:fulltwist`, (9), and `lem:homflyrows(ii)`, together with the
knot-parity clause of `ax:homfly`, which gives
`[z^0](Q_A Q_B)=([z^0]Q_A)([z^0]Q_B)=f_A f_B`,

```text
Omega_H-Omega_L
 = [a^(d_L-1) z^(-1)] P_(D_0)
 = [a^(D-2)] f_A f_B - [a^D] f_A f_B.                  (12)
```

The second equality uses (11) and the factor
`a^(-2 ell)(a-a^(-1))`; it does not split the auxiliary link. For each
nonempty `A` or `B` carrier, `cor:groupedknot`, clauses (A) and (B), gives a
knot diagram, and the divide convention makes every retained crossing
positive. Genericity gives finitely many transverse double points, no triple
point, no crossing at a corner, no corner on a nonincident edge, and nonzero
principal turns of magnitude below `pi`. The nonzero-selector assumption and
(4) make each such carrier uniform with turn sign `-sigma`; after a possible
global orientation reversal, `thm:carrierfloor(C)` applies. For a piece-free
carrier, `def:X1`'s empty conventions and `thm:carrierfloor(D)` give the same
floor. Hence no exponent below `d_A` occurs in `f_A`, and none below `d_B`
occurs in `f_B`. Therefore the first coefficient in (12) is zero, while the
coefficient at `D=d_A+d_B` is the product of the two first coefficients:

```text
Omega_H-Omega_L = -omega_A omega_B.                    (13)
```

## 5. The complete row identity

Let `V` be the product of all common spectator reads and let `Omega_C` be the
common read on the `C` carrier. Neither is cancelled or assumed nonzero.
Equations (6) and (13) give

```text
T_E(b)-T_P(b)
 = wind_P(Q union b) V Omega_C (Omega_H-Omega_L)
 = -wind_P(Q union b) V Omega_C omega_A omega_B
 = T_P(ac).
```

This is (GSC). The argument also covered selector zero before coefficient
extraction, and spectator or coefficient zeros remain valid because every
step is multiplicative; no exterior factor was divided out.

## Boundary and circularity guards

This proves only the generic graph-selected `b/ac` couple. It does not
transport the generic empty or endpoint singleton rows and does not address
the extreme empty/full couple. The proof does not invoke `ax:R`, `thm:main`, or
an aggregate S7 conclusion. It uses the algebraic content of `lem:fulltwist`
and the manuscript floor, but it does not cite `lem:triplebridge`,
`prop:fulltwistjump`, or `lem:triplebridge(vii)` across their vertex-on-edge binders; their
record, selector, and ledger steps are re-established above for the RIII
words.
