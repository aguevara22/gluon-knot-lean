# Independent scope and counterexample review: lem:shift(iii)

Reviewer: `review_chirotope-independent-20260910` (not the counterexample's author).

**Verdict: a source omission is confirmed. The unrestricted left-turn count conclusion in original `lem:shift(iii)` is false, including on the regular locus. The original full row is not accepted.**

The true shift/reversal identities and the safe restricted uses are distinguished below from that false unrestricted consequence. This review does not substitute a repaired theorem for the frozen source.

## Source scope

The source lemma at `reference/SM/sm-1-polygons.tex:484` has no opening hypothesis declaring P generic or requiring its turns to be nonzero. Its clause (iii) states the actual turn relabelling/negation identities and then concludes `leftTurns(reversal P) = n - leftTurns P`. The proof establishes turn negation but supplies no argument excluding zero turns from the counting step.

I checked the surrounding scope rather than treating a missing hypothesis as routine implicit genericity:

- The object rules in `reference/SM/sm-0-legend.tex:3` define polygons as cyclic orbits of real labelled tuples. Saying that Generic has one fixed meaning is not a blanket assumption that every polygon is generic.
- `def:polygon` in `sm-1-polygons.tex:27` explicitly allows coincident vertices and zero edges at the tuple-definition level. Its formalization remark authorizes labelled tuples with equivariance, not hidden genericity premises.
- `def:regular` at line 374 explicitly permits positive collinear consecutive edges, and says precisely when their principal turns are zero. Thus even an implicit restriction to the natural domain of the rotation clause, Regular P, does not repair the left-count formula.
- The all-turns-nonzero hypothesis of `lem:uniformrot` is inside that closed lemma environment. The subsequent Whitney remarks have their own local hypotheses. None carries a standing nonzero-turn premise through the later subsection boundary into `lem:shift`.
- Clause (ii)'s assertion that the shift and reversal map the generic locus onto itself is a statement about those maps and that set. It is not a hypothesis that every P occurring in all other clauses belongs to the generic locus.
- The abstract of `sm.tex` describes the two main functions as defined on generic polygons. It does not globally restrict the chapter's polygon/regular definitions or every auxiliary theorem to Generic.

INFERENCE ABOUT INTENT: the author may have intended the counting consequence only for generic polygons, especially given the observed downstream uses. That intended restriction is plausible but is not supplied by the printed scope and must not be silently treated as part of the original lemma.

## Exact counterexample

The separate file `work/repairs/ShiftZeroTurn.lean` defines `SM.ScopeInvestigation.zeroTurnFour` with the following vertices at natural residue labels 0,1,2,3. This is the same cyclic polygon as the displayed four-point example with conventional one-based labels; the different cut does not affect either count.

| Residue i | Vertex P(i) | Outgoing edge E(i) | det(E(i-1), E(i)) |
| --- | --- | --- | --- |
| 0 | (0,0) | (1,0) | 1 |
| 1 | (1,0) | (1,0) | 0 |
| 2 | (2,0) | (-2,1) | 1 |
| 3 | (0,1) | (0,-1) | 2 |

Every edge is nonzero. At residues 0,2,3 the nonzero determinant excludes every scalar dependence. At residue 1 the two consecutive edges are equal nonzero vectors, so the multiplier is positive, not negative. The polygon therefore satisfies exactly the actual Regular predicate. Its turn signs in this residue convention are `(1,0,1,1)` and its left-turn count is 3.

The actual source reversal is `P(2-i)`. Its turn signs, using the already proved and source-correct identity, are `(-1,0,-1,-1)` in this same residue convention. Its left-turn count is 0. The printed formula would give `4-3=1`, contradicting the actual count. This is not a convention change: a simultaneous cyclic relabelling merely permutes the displayed signs and leaves both counts unchanged.

The inspected Lean file proves all relevant facts from concrete definitions:

- `zeroTurnFour_turns` evaluates the actual chirotope/determinant turns at all four residues; it does not supply an arbitrary turn tuple.
- `zeroTurnFour_regular` proves actual nonzero edges and excludes every negative real scalar multiplier at every corner through coordinate equalities. It does not assume genericity or regularity as a witness premise.
- `zeroTurnFour_left` evaluates the actual finite filter count as 3.
- `zeroTurnFour_reversed_left` evaluates the actual count after the genuine `reversal` as 0.
- `shift_left_count_fails_on_regular` proves existence of a real labelled regular four-tuple violating the printed count equation.

The finite computations use kernel-checked `decide` and coordinate tactics, not `native_decide`, an external numeric certificate, approximate trigonometry, or a postulated count. The proof is an actual counterexample to the unrestricted conclusion, not merely a failure to prove it.

## Independent verification

I inspected the source, the complete counterexample type and body, and the inherited definitions giving Plane, edges, Regular, turn, leftTurns and reversal their meaning. I independently recomputed the edge vectors, determinant signs and counts with exact rational arithmetic, then independently ran:

```text
lake env lean ../repairs/ShiftZeroTurn.lean
```

from `work/lean`. That independent run completed with exit code 0. Its `#print axioms SM.ScopeInvestigation.shift_left_count_fails_on_regular` output contained only `propext`, `Classical.choice`, and `Quot.sound`. The only diagnostic was an unnecessary tactic-sequencing style warning, which has no effect on the theorem. The supplied log `work/checks/shift-zero-turn-check.log` agrees with that outcome; its hash is recorded below. All thirteen local inherited files are byte-identical to the previously independently reviewed files. The counterexample is deliberately outside `work/lean`; it is separate repair evidence and is not an accepted replacement source row.

## Precise repair boundary and downstream compatibility

The unconditional turn-negation identity is true. Reversal exchanges left and right turns and preserves zero turns under a bijection of indices. Accordingly, the general counting identity is:

```text
leftTurns(reversal P) + leftTurns(P) + numberOfZeroTurns(P) = n.
```

This sentence describes the mathematically correct repair target; a Lean proof of that general formula is not claimed by this review. The printed equation follows under the minimal extra condition that every turn is nonzero. Generic is sufficient by G1, but stronger than necessary. A legitimate repair should either add that explicit condition only to the count conclusion, or state the general zero-aware identity and derive the count conclusion on the intended nonzero-turn domain. The unrestricted chirotope/turn identities can retain their existing domains; rotation identities retain the regular domain.

I found two direct source references to `lem:shift` in the focused SM files and checked their domains:

1. `reference/SM/sm-4-knotlaws.tex:1144`, in `prop:C-reversal`, uses the left-count formula. The section expressly fixes C on generic polygons at lines 3-4. Generic therefore supplies the needed nonzero-turn condition for this application.
2. `reference/SM/sm-5-transport.tex:61`, in `lem:star-generic`, invokes clauses (ii)-(iv) for the reversed star. The preceding argument establishes the original star's genericity, and its turns are explicitly all left. Its relevant reversal/count consequences are therefore within the nonzero-turn domain.

These are domain-compatibility checks of the observed direct consumers, not acceptance of their entire mathematical proofs or a claim that no further indirect consumer exists. They show that an explicit repair is usable by those consumers after their hypotheses are proved; they do not retroactively add a premise to the frozen lemma.

The original `lem:shift` map row remains `pending` with no mapped declaration. No original proof/checklist count should be incremented for either this counterexample or a separately proved restricted consequence. A generic or nonzero-turn version must be labelled as an explicit repair, not receive a faithful review as if it proved the original unrestricted count. This review does not certify the full original `lem:shift`, accept a source substitution, modify frozen sources, or decide a scope/checker amendment. No Lean or declaration-map file was authored or edited by this reviewer.

## Hash bindings

Counterexample and inspected local dependencies:

```json
{
  "work/repairs/ShiftZeroTurn.lean": "3db5b53e42a7efffcd9b2e9a196b25ab2f2f0744b7d715c0901f8bb7a008b583",
  "work/lean/SM/Chirotope.lean": "e0225bc712162273f43269ed764ac4849ae8fcd8798245a367d4262858fbf575",
  "work/lean/SM/EuclideanPlane.lean": "30a5956221225bc9811a792b5a67c6c5967fb6dda0b4cb14be997051b32b7a4f",
  "work/lean/SM/G1Consequences.lean": "61debba77e41a48207c8d01bdeb113ee05048ec5f1f8a5868588fcf4601a4763",
  "work/lean/SM/Generic.lean": "d66da53bd155faf33a26116324dfe2211e01ac75a8b9f2ccbf028630ee1e6417",
  "work/lean/SM/Polygon.lean": "d0b5d37591c252d66e1a3f060cea1e3d58625fedd6c5491cf4c1cf6d2b8c149d",
  "work/lean/SM/PrincipalAngles.lean": "d618c6e2b040d5f5dbaf4b0bc7ef46a565dfb439756587d6f1c83e5c8955672a",
  "work/lean/SM/RegularDefinition.lean": "1abcbd05624a34d5df1963ebef27e1497296f1986b39dd5a635561fed4ce86e1",
  "work/lean/SM/RegularLocus.lean": "ad97d04e3eda38ba6f46d435ee9873344808d0d811ce28c410cd91e35b963acf",
  "work/lean/SM/RegularPairs.lean": "7d09c9ecbb9b2515808d606a060256ee83b744ce42f946c5d9ff9f97ade80a06",
  "work/lean/SM/Reversal.lean": "be95b73303a842c7eefbd41aa0422541e05e97e0a4f4f71f7f06cb070707747b",
  "work/lean/SM/RotationNumber.lean": "8d6dc7680484539bf4243b6256155f900061ad34740b29b4f0d0eae6dbd1c0df",
  "work/lean/SM/RotationReversal.lean": "9c66a51229506b886ffc7fa4f9901c483dcb21025009d88a047e05c1ebdadd1b",
  "work/lean/SM/Segment.lean": "40fcfef972866bf0d762b08240941b3f7cd189259692d330709702ad1c9a7465"
}
```

Frozen source/context files inspected for the scope and consumer assessment:

```json
{
  "reference/SM/sm.tex": "5415c1639a48ecd1b5d77aa930ea88b36968522a3f7d2b0c6e577b133f6eec96",
  "reference/SM/sm-0-legend.tex": "af1c46934354df09a24a119f12ba32bcb94a64bbc87a8fa24905fd8c61454215",
  "reference/SM/sm-1-polygons.tex": "8bc30167c9cde79c3eb4b9cf52052f81f040ec91490f49517b9f1b7ad0333a00",
  "reference/SM/sm-4-knotlaws.tex": "146ce4e08fa66c72f11a6c0834144fe3dfe14981d8f567819d6951eb54c81efd",
  "reference/SM/sm-5-transport.tex": "f0663d69053c7e27fe820af6eee8cf24e59f16998da3dfff1f21172047519584"
}
```

Supplied compilation log SHA256:

```json
{
  "work/checks/shift-zero-turn-check.log": "a276be29131095d0084556132824d75329a45f840daf6bdc66c0ed17a298d051"
}
```
