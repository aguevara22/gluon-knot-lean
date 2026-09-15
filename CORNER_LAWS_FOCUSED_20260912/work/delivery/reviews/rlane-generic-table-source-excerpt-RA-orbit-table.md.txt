# R local complement — exact generic-orbit table and first missing datum

Status: **proved at unsigned graph, mask, residual-word, and successor-cycle
level**.  The signed upgrade for the two nonselected pair rows is proved
separately in `R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`; the common endpoint
transports and selected local-complement identity are not proved here.

Use the three unchanged exterior gaps `A,B,C` between the RIII strand blocks:

```text
P = a b A a c B b c C       (edges ab, bc; centre b)
E = b a A c a B c b C       (edge ac; b isolated)
```

The graph-selected generic complement couple in these labels is therefore
`b/ac`.  The abstract `c/ab` notation in the proof-obligation note is the same
mechanism after permuting labels.

## Successor cycles

```text
P empty : (123456)[ABC]
P a     : (1456)[BC](23)[A]
P b     : (126)[C](345)[AB]
P c     : (1234)[AC](56)[B]
P ac    : (14)[C](23)[A](56)[B]

E empty : (123456)[ABC]
E a     : (1256)[BC](34)[A]
E b     : (1)[C](23456)[AB]
E c     : (1236)[AC](45)[B]
E ab    : (1)[C](256)[B](34)[A]
E bc    : (1)[C](236)[A](45)[B]
```

The supports `ab,bc,T` are absent on P; `ac,T` are absent on E.

## Local undominated table

```text
P: empty -> abc; a -> c; b -> empty; c -> a; ac -> empty
E: empty -> abc; a -> b; b -> ac (connected); c -> b;
   ab -> empty; bc -> empty
```

Full availability plus R-PAR sharpens the exterior masks: after `a`, survivors
have mask `0` or `bc`, so `b,c` are twins; after `c`, mask `0` or `ab`, so
`a,b` are twins; after `b`, mask `0` or `ac`, so `a,c` are twins; after any
present pair only mask-zero outsiders survive.

The exact generic obligations are consequently:

* transport the empty row;
* transport endpoint row `a` while killing E-only row `bc`;
* transport endpoint row `c` while killing E-only row `ab`;
* prove the selected `b/ac` identity.

For endpoint `a`, the unsigned residual word is `c B c C` on P versus
`b B b C` on E, with the A-carrier unchanged.  For endpoint `c`, it is
`a A a C` versus `b A b C`, with the B-carrier unchanged.  For the selected
row, P-`b` has no local residual on carriers `C|AB`; E-`b` has residual
`a A c a B c` on `AB`, whose rotation `c a B c a A` is the interlacing
full-twist contact word; and P-`ac` has three local-empty carriers `C|A|B`, the
half-product target.

## Earliest remaining interface

The earlier version of this note proposed fixing all three oriented strand
determinants to one sign.  That shortcut is false.  The exact line-order
calculation instead partitions the wall into six generic nonalternating sign
branches and two extreme alternating branches.  In each generic branch the two
nonselected pair supports have a carrier with two opposite-sign local
smoothing corners, so their selectors vanish; the proof is
`R_GENERIC_NONSELECTED_SELECTOR_PROOF.md`.

The earliest remaining generic interface is therefore narrower: transport the
two common endpoint singleton rows (and the empty row) across the corner change.
That still requires a signed cross-corner carrier ledger identifying the two
smoothed-RIII contacts, active-corner ownership, successor-carrier rotations,
residual owners, and slots.  Existing sliding transport/rotation/coefficient
and one-newborn interfaces each bind one certified simple vertex-on-edge event;
none currently binds both contacts.  After those common-row transports, the
selected `b/ac` full-twist bridge remains.  The unsigned word table alone does
not prove either interface.
