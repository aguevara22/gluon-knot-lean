# Weak center implies silent event: technical review

Reviewer root did not author WeakCenterSilent; author is review_contraction_candidates.
This is independent same-model technical evidence, not the stronger statement/
definition-fidelity approval requested by the user. No source row is accepted.

Compared all five declarations with source thm:A-continuation at
sm-2-amplitude.tex:656–692 and the frozen WeakGeneric, incident, G2, FlatAt,
CuspAt, VertexEdgeAt, TripleAt, mem_concurrences and WallKind definitions.
No defect found in this scope.

WeakGeneric explicitly supplies nonzero turns, exclusion of all nonincident
closed-segment vertex contacts, and G2. The flat and cusp singleton turn
supports force the named central turn to zero via the proved support lemma,
contradicting nonzero turns. No neighboring-side choice is used.

For a vertex contact, incident M a means a=M-1 or a=M. The first implies
M=a+1 and the second M=a, both excluded by the actual ContactSeparated fields.
The given open-interior line parameter lies in the closed segment because
its strict bounds imply the corresponding non-strict bounds. Weak vertex
exclusion then gives the contradiction. No remoteness premise is added.

For a triple event, membership of the actual named support in the singleton
concurrence set yields cardinality three and an actual common interior point.
The cardinality result gives all three pairwise inequalities in G2's exact
order. Its common point is read at all three labels, contradicting the G2
component of WeakGeneric. This does not confuse line concurrence with actual
interior concurrence or assume point-triple G1 at the weak center.

The main theorem exhausts every actual Simple/WallKind constructor, including
cusp. The surviving E/C witnesses are precisely the definition of Silent.
It retains hn>=3 and supplies no caller exclusions, regularity, unique-kind,
wall-side or generic-center assumption. Its use in full continuation still
requires constructing the path and deriving WeakGeneric at its actual events.

Root first15307 exited0; all five printed traces use only propext,
Classical.choice and Quot.sound. All three bound receipt hashes match.
Strong fidelity approval and canonical integration remain pending.

work/checks/WeakCenterSilent.body.lean SHA-256: 71fb7d0b8cea85738641274219121ed0c5f29c78f852df43f2c586b159d2c561
work/checks/WeakCenterSilent.prototype.lean SHA-256: 778a9d216004cc2677f23cb1d53ed0c396d94cafab0de17dfd5a7559ec8f3c96
work/checks/WeakCenterSilent-first-kernel.log SHA-256: 5c8646f1e38bb7876890e0d1edec3aa2621bdbff26cbeacffd5cdd2d9d8bcdca
