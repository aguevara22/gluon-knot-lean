# Finite line-order gap lemmas: technical review

Root did not author FiniteLineGaps; author is review_contraction_candidates.
Same-model nonauthor review only, not stronger fidelity or source acceptance.
Compared all3 declarations with the full source pf:line-gap at795 onward.
No defect found in their scoped abstract assertions.

second_max_bound is a direct order consequence: injectivity makes each value
other than the chosen maximum strictly lower; a value above the predecessor
would lie strictly in the excluded edge segment. It requires no finite type
or normalized coordinates beyond its explicit maximum bound.

The positive lemma assumes all increasing gaps are leaf gaps for contradiction.
A finite maximum cannot be the initial endpoint because the final endpoint is
larger. Its predecessor gives an increasing leaf edge, and hence the second-max
bound. The maximum cannot occur at index1: the final endpoint, distinct from
that maximum because k>=2, would then be no greater than the initial endpoint.
There is therefore a preceding gap; its endpoint is below the second maximum
by injectivity, making it an increasing leaf too. The two actual adjacent gap
indices contradict the supplied consecutive-leaf exclusion. All endpoint index
arithmetic is explicit, including k=2.

The negative lemma assumes all decreasing gaps are leaf gaps. Since the first
gap is not a leaf, it must increase (equality is excluded by injectivity).
Closing-segment exclusion and k>=2 put its next point strictly above the final
endpoint. Consequently a maximum is not final. Its outgoing gap decreases,
so it is a leaf, and its next coordinate is second-highest. The last-gap
nonleaf premise rules out that outgoing gap ending at the final endpoint.
The next point is below the second maximum by injectivity, so the next gap
also decreases and is a leaf, contradicting consecutive-leaf exclusion.
This is a complete finite-list proof; the closing direction is encoded by the
explicit ordered endpoints and hclose, not asserted for arbitrary intervals.

These are helper theorems with explicit leaf/segment assumptions. They become
pf:line-gap only after all assumptions are derived for actual weak polygons,
actual selected boundary positions, the physical root edge and the exact
source ratios. No source row is accepted from these abstractions alone.

Root first15599 exited0. All3 traces use only propext, Classical.choice,
Quot.sound; exact first-draft body/prototype are unchanged. Passing evidence
is frozen. Stronger statement/definition fidelity remains pending.

work/checks/FiniteLineGaps.body.lean SHA-256: 9d7d3e76bb2e142b2e675922d663fa116ab03ba6e3908fd8ec809e8b980ed2bd
work/checks/FiniteLineGaps.prototype.lean SHA-256: dedfd61f7f96d846568dfca3ea6d5c7d81dc438aefce7bf012eb5535f5e081bf
work/checks/FiniteLineGaps-first-kernel.log SHA-256: 96fa794a01edb7cf7b5ce7d076fc0bd7a31c7e49cfa7ef6710f5a4daf172c74e
