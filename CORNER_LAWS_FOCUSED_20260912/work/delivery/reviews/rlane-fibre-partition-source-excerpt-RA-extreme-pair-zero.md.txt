# R local complement — every extreme one-sided pair row is zero

Status: **PROVED intermediate lemma**, from accepted R-LOC/R-PAR and the
manuscript's `thm:s7universal(D)(i)`.  This is not yet an R-chain claim pack and does
not prove the common singleton transports or the selected `empty/full` couple.

## Statement

Fix the two nearby generic chamber-side representatives of a simple RIII wall
in the extreme graph orbit `K3 <-> empty`, and fix a full-availability fiber.
Each local pair support is absent on the `K3` side and present on the
empty-graph side.  Its complete X1 term on the latter generic polygon is zero,
for arbitrary outside support and exterior geometry.

## Proof

Let `T={x,y,z}` be the three local crossings, let `Q` be the outside
independent support defining the full-availability fiber, and take a pair
`J={x,y}`; the other two choices are identical after relabeling.  Put
`S=Q union J` on the empty-graph side.

The support `S` is independent.  Indeed, `J` is independent because the local
graph is empty, and full availability says every member of `T` is nonadjacent
to every member of `Q`.

The remaining crossing `z` is undominated by `S`: it is nonadjacent to `x,y`
because the local graph is empty, and nonadjacent to `Q` by full availability.
Thus `z` belongs to the residual graph of `S`.

It is a singleton component there.  Suppose an outside residual crossing `c`
were adjacent to `z`.  Accepted R-PAR(P1) is quantified over **every crossing
`c` outside `T`**, not only over members of `Q`: it says that
`|N(c) intersect T|` is zero or two.  Since `c` is adjacent to `z`, it must
therefore be adjacent to at least one of `x,y`.  But `x,y` lie in the support
`S`, so `c` would be dominated and could not be residual.  This contradiction
proves that `z` has no residual neighbour.  There are no other local residual
crossings, because `x,y` are in the support.  Hence `{z}` is a singleton
residual piece.

If `wind(S)=0`, the X1 term is zero by definition.  Otherwise every carrier of
`S` is uniform.  Let `A` be the carrier owning `{z}`.  The hypotheses of
`thm:s7universal(D)(i)` now hold, so

```text
Omega1(S,A)=0.
```

The complete X1 term is a product containing that factor and is therefore
zero.  The proof is exhaustive: selector-dead rows take the first branch;
selector-live rows take the singleton-coefficient branch.  It assumes no
nonzero exterior scalar and performs no division.

## Boundary of the result

This proves all three one-sided pair rows in the extreme orbit vanish.  It does
not compare the three singleton rows, which occur on both sides, and it does
not prove the selected `empty/full` complementary-couple identity.
