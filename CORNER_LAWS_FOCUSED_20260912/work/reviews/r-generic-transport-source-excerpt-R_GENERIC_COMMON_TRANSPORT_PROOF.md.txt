# R local complement — generic common-row transports

Status: **PROVED intermediate lemma**, from accepted R-LOC-2, R-PAR-v6, and
`R_GENERIC_ORBIT_ACTUAL_TABLE.md` ("Earliest remaining interface") and
`R_GENERIC_NONSELECTED_SELECTOR_PROOF.md` ("Oriented line-order calculation"
and "Which pair is selected"), plus the manuscript's carrier/record
interfaces. This is not yet a sealed R-chain claim pack. It covers the generic
empty row and the two endpoint singleton rows; the selected singleton/pair
identity is proved separately.

The establishing statements and proofs of R-LOC-2 and R-PAR-v6 are printed
in `R_ATTACHMENT_WARRANTS.md`, sections "R-LOC-2 — localization" and
"R-PAR-v6 — parity and availability". The shorter names R-LOC and R-PAR
below denote those same statements.

## Statement and canonical branch

Fix a full-availability fiber at a simple RIII wall in the generic graph orbit
and an exterior independent support `Q`. Relabel the local crossings so

```text
P = a b A a c B b c C       (edges ab,bc),
E = b a A c a B c b C       (edge ac).
```

Write the three determinant signs in the crossing order
`a=(u1,u2)`, `b=(u1,u3)`, `c=(u2,u3)`. Following
`R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`, "Which pair is selected",
call a pair sharing a strand `u` separating when the other two oriented
directions lie on opposite sides of `u`. The "Oriented line-order calculation"
and "Which pair is selected" sections of that proof, with the classification
recap in `R_GENERIC_ORBIT_ACTUAL_TABLE.md`, "Earliest remaining interface",
prove that in the
generic orbit there is exactly one such pair, that it is the graph-selected
pair, and that the generic sign triples are precisely the six nonalternating
triples. In the displayed graph the selected pair is `ac`, so its shared
strand `u2` separates `u1,u3`, giving equality of the `a` and `c` determinant
signs. If the `b` sign were opposite, the triple would be one of the two
alternating triples that `R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`,
"Oriented line-order calculation", and `R_GENERIC_ORBIT_ACTUAL_TABLE.md`,
"Earliest remaining interface", identify with the extreme orbit. Hence
the generic branch here has

```text
sgn det(u1,u2) = sgn det(u1,u3)
               = sgn det(u2,u3) = sigma.               (1)
```

Every generic branch can be put in this form by relabelling the strands in
their transitive angular order. The same relabelling carries the crossings and
the exterior gap strings `A,B,C`; no symmetry of those strings is used.

Write `T_nu(J)` for the complete X1 term of `Q union J` on side `nu`. Then

```text
T_P(empty)=T_E(empty),
T_P(a)=T_E(a),
T_P(c)=T_E(c).                                         (2)
```

## The arbitrary-Q successor lift

Full availability makes every selected member of `Q` nonadjacent to each of
`a,b,c`. In the connected six-visit local word, the two visits of such a label
therefore have the same side-vector relative to all three local chords and lie
in one macro-gap `A`, `B`, or `C`. Smoothing `Q` acts independently inside
those gaps. Replace each printed gap by its fixed boundary-to-boundary
successor paths after those internal smoothings, together with any internal
closed successor cycles. The local skeletons then lift canonically:

```text
empty row : ABC -> ABC,
endpoint a: BC  -> BC,      A -> A,
endpoint c: AC  -> AC,      B -> B.                     (2a)
```

Every internal closed cycle is a spectator. R-LOC also keeps the outside
survivor label set and all outside-to-outside graph edges fixed. Together with
`lem:carrierword`, (2a) transports the carrier cycles and their cyclic orders.
In the endpoint rows, the undominated-graph isomorphisms proved below and
`lem:carriers(iv)` then transport residual components and owners. In the empty
row no residual-component bijection is asserted: `cor:groupedknot`, clauses
(A) and (B), deliberately bypasses the changing component partition.

## 1. Empty-row transport

Smooth `Q` first. Because `Q` is fully available, all three local crossings
remain undominated. On the path side they form a connected residual subgraph,
so `lem:carriers(iv)` puts all six local visits on one distinguished carrier.
The successor lift (2a) gives that carrier and every other Q-carrier canonical
mates on the two sides, with the same outside successor strings. Only the order
of the six local crossing visits on the distinguished carrier changes by the
printed RIII words.

The distinguished carriers on both sides bear the three undominated local
crossings. For every other matched carrier, R-LOC-2 conclusion (4) and the
successor lift preserve its outside undominated label set, so the two carriers
are either both piece-free or both nonempty. In the nonempty case, take the
union of all residual pieces the carrier owns. By `cor:groupedknot`, clauses
(A) and (B), the product of their piece polynomials is the HOMFLY polynomial
of the one knot diagram obtained by retaining every self-crossing with the
divide convention. In the piece-free case, use `def:X1`'s empty conventions,
as recorded in `thm:carrierfloor(D)`: `P_{S,L}=1` and `w_{S,L}=0` on both
sides. Thus no `cor:groupedknot` clause is applied with `k=0`. The residual
component partition may change when the three local graph edges toggle, but
the nonempty grouped diagram uses the full self-crossing set and does not
depend on that partition.

On the distinguished carrier, (1) makes the divide over-order of the three
local strands transitive: for `sigma=+1`, `u1` is over `u2,u3` and `u2` is over
`u3`; for `sigma=-1` the order reverses. Call the path- and edge-side grouped
diagrams `D_P,D_E`. Apply the corresponding ordinary oriented Reidemeister III
move to `D_P`, obtaining `D'`; `ax:homfly` gives `P(D')=P(D_P)`. R-LOC-2
conclusions (1) and (3), the successor lift (2a), and the printed local words
give an orientation-preserving `def:record` isomorphism from `D'` to `D_E`:
cyclic order, crossing pairings, over/under positions, and signs agree. Both
are connected generic one-circle diagrams by `cor:groupedknot(B)`, so
`ax:gausscode` identifies their oriented links. Hence their grouped
polynomials agree. Their grouped writhes also agree, being the numbers of
retained positive crossings in the same label set.

No local crossing is a corner of the empty local support. By (2a), every
matched Q-carrier has the same cyclic corner list. Throughout the RIII family
its edge directions stay nonzero and every polygon-vertex and Q-smoothing
corner determinant remains guarded; the G3 collision creates no corner.
Thus each matched carrier is a path in one corresponding `R_k`, and
`lem:turnlift(ii)` preserves its signed and absolute rotation. Constant corner
counts and signs preserve its weight by `def:wind`. Spectator carriers need
not be geometrically fixed: their unchanged signed self-crossing records and
label sets preserve their grouped polynomials and writhes. Hence all matched
slots, coefficient reads, and weights agree. Reading `def:X1` proves the first
equality of (2), including all selector- or coefficient-zero cases.

## 2. Endpoint `a`

The exact successor and local-residual rows are

```text
P-a : BC | A,   residual local crossing c with word c B c C;
E-a : BC | A,   residual local crossing b with word b B b C.       (3)
```

R-PAR sharpens the outside masks after selecting `a`: every outside survivor
meets neither `b,c` or meets both. Consequently `b` and `c` are twins relative
to every outside vertex that survives `Q union {a}`. R-LOC-2 conclusion (4),
`G^+ = G^- triangle binom(T,2)`, says that the wall changes only local-to-local
edges. Hence the outside survivor set, every outside-to-outside edge, and every
outside-to-local incidence used here are unchanged. The map fixing every
outside label and sending `c` to `b` is therefore an isomorphism of the two
undominated induced graphs and carries residual components bijectively.

The same map preserves the signed cyclic records. The arbitrary-Q lift of
equation (3) preserves cyclic order on the matched `BC` and `A` carriers;
pairing and all outside visits are fixed. The two visits of the relocated
crossing are explicit: P-`c` is first visited on `u2` and second on `u3`, while
E-`b` is first visited on `u1` and second on `u3`. The divide designation is
therefore preserved because

```text
sgn det(u2,u3)=sgn det(u1,u3)=sigma,                   (4)
```

so the same first/second visit is over after replacing the `u2` branch by the
`u1` branch; both crossing signs are positive. Thus `def:record` and `ax:gausscode`
identify every corresponding piece diagram and its polynomial. Component
cardinalities agree, so grouped writhes agree; the successor cycles in (3)
give the same owners under the relabelling.

Both local carriers move geometrically. On `BC` the smoothing corner is typed
`u1 -> u2`; on `A` it is `u2 -> u1`; the remote strand is `u3`. Each matched
carrier is a continuous path in its corresponding `R_k`: every edge direction
stays nonzero, every polygon-vertex and Q-smoothing turn remains guarded, the
displayed local smoothing turn is nonzero by (1), and passing the remote
strand creates no corner. Corner counts and turn signs are constant along the
path. Therefore `lem:turnlift(ii)` gives equal signed and absolute rotations,
and `def:wind` gives equal carrier weights and full selectors. Together with
the record and writhe transport above, the slots and coefficient reads agree.
Reading `def:X1` proves `T_P(a)=T_E(a)` without dividing by any factor.

## 3. Endpoint `c`

The symmetric printed rows are

```text
P-c : AC | B,   residual local crossing a with word a A a C;
E-c : AC | B,   residual local crossing b with word b A b C.       (5)
```

Here R-PAR says `a,b` are twins relative to every outside survivor. R-LOC-2
conclusion (4) says that only local-to-local edges toggle, so the outside
survivor set, all outside-to-outside edges, and the outside incidences with
`a,b` are unchanged. Thus fixing every outside label and sending `a` to `b`
is an isomorphism of the undominated induced graphs; the corresponding record
relabelling is `a -> b`. P-`a` is first visited on `u1` and second on `u2`, while E-`b` is
first visited on `u1` and second on `u3`. The divide designation is preserved
by

```text
sgn det(u1,u2)=sgn det(u1,u3)=sigma.                  (6)
```

The arbitrary-Q lift of (5) transports the `AC` and `B` successor carriers and
their owners. Both carriers again move: the `AC` smoothing corner is
`u2 -> u3`, the `B` corner is `u3 -> u2`, and the remote strand is `u1`.
The same guarded-`R_k` path argument and `lem:turnlift(ii)` transport their
rotations, while the constant corner lists transport their weights. Repeating
the residual-component, signed-record, grouped-writhe, slot, and coefficient
argument of the preceding section proves `T_P(c)=T_E(c)`.

## Boundary and binder guard

The endpoint argument is a direct carrier-level proof from the RIII words; it
does not cite `lem:slidingcartesian(A)`, `lem:slidingcoeff(A)`, or
`lem:slidingcoeff` across their `conv:s7standing` binder. It reproduces only
their avoiding-sector mechanism after proving the required opposite-side
signs (4),(6). No use is made of `ax:R`, `thm:main`, aggregate S7, an exterior
division, or a symmetry of the gap strings.

Together with the proved vanishing of the two generic nonselected pair rows,
(2) closes the empty/full and both endpoint singleton/pair complementary
couples. The generic graph-selected `b/ac` couple remains the separate
full-twist calculation in `R_GENERIC_SELECTED_COUPLE_PROOF.md`.
