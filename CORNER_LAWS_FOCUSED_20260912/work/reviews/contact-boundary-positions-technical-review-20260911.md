# Contact boundary positions: technical review

Reviewer root is not the author; author and repairer is
review_contraction_candidates. Same-model technical review only: stronger
statement/definition-fidelity approval and source thm:A-S7 acceptance remain
pending. Read all fourteen declarations and compared the cuts with the source
induced-root definition and vertex-edge proof at sm-2-amplitude.tex:380–393,
520–590, plus canonical boundaryIndex, ContactSeparated and contactDistance.
No mathematical defect found within this scope.

Write d=(a-M).val and u=(g-M).val. ContactSeparated and n>=3 imply
2<=d<=n-3; all residue representatives also satisfy u<n. Since the boundary
label at k is g+k+1, the proposed positions read exactly as follows:
- Base g=a: (0,n-d-1,n-1) reads (a+1,M,a). Gaps are n-d-1,d,
  both at least two, and the span is the full boundary interval.
- First arc u<d: (d-u-1,d-u,n-u-1) reads (a,a+1,M). Gaps are
  1,n-d-1. A full span would force d=1, excluded by the source bounds.
  The erased strict interior has size n-d-1, leaving d+1 vertices.
- Second arc d<u: (n-u-1,n-u+d-1,n-u+d) reads (M,a,a+1). Gaps
  are d,1. A full span would force n-d=2, excluded by the source bounds.
  The erased strict interior has size d, leaving n-d vertices.

Each natural subtraction is justified before conversion to ZMod; d and u
cast back to a-M and g-M. Thus linear representatives, strict order and labels
are proved rather than guessed from a picture. The endpoint cases u=0 and
u=n-1 remain in the domain. Contracted-size equalities assert size only, not
full tuple equality or coefficient/root invariance. Parent n>=3 is retained;
no additional minimum n or neighboring-side predicate is assumed.

Second root54811 exited0 with all14 traces using only propext,
Classical.choice and Quot.sound or subsets. First2538 failed at one `change`
which conflated Nat-cast zero and ring zero. Exact first body/prototype/log
are preserved. Root verified that the repaired body differs only in that
subproof (explicit Nat-cast zero followed by simp); all definitions and
statement text are byte-for-byte unchanged. Receipt binds the repaired body,
prototype, successful log and frozen CriticalContractionPositions dependency.

Body SHA-256: 61d797a366cb8db5312ac0739037da47361b87eed4ed50e786ee3b72b7c2c4b7
Prototype SHA-256: 559724e9a32101985ef48daf7ab61cee745db0d0c898906f1bb805b7d817ccdb
