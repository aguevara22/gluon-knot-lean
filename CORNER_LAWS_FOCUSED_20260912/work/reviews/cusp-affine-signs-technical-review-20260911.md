# Cusp affine signs: technical review

Reviewer root is not the author; author is review_contraction_candidates agent.
Same-model technical review only, not the stronger fidelity approval requested
by the user. No original row acceptance or canonical integration is asserted.

All four ratios match the source thm:A-S4 table: incoming coordinates(r,1,0)
give(+,+) for r>1 and(+,-) for r<0; outgoing coordinates(1,0,r) give(-,+) for
r>1 and(+,+) for r<0. Every numerator and denominator sign follows explicitly
from the strict exterior inequality. Thus division is only by a proved nonzero
real denominator; no sign-of-zero convention decides a source branch.

The affine theorem constructs r from the dot-product quotient using the proved
scalar_of_det_zero theorem. CuspAt supplies source size>=4 and singleton critical
turn support; existing injectivity then separates predecessor and successor,
so B-A is nonzero. The actual zero turn implies the zero determinant, with its
order corrected using antisymmetry. The derived M=A+r(B-A), together with the
actual source exterior predicate, excludes r in the entire closed interval[0,1].
Both endpoint coordinate equations are proved. No affine coordinate, CuspCase,
nonzero denominator, or betweenness is added as a hypothesis. No mathematical
defect found in this scope.

All5 candidates passed root39700 first run exit0. The receipt
work/checks/CuspAffineSigns-prototype-result.json binds the new body, frozen
CollinearGateSigns body, prototype and log. Printed axiom traces are subsets of
propext, Classical.choice and Quot.sound. The full source-to-definition chain
still needs stronger fidelity approval; this review does not supply it.

Body SHA-256: e7ad55db9a7bca0fa2be15ffe982da0dfed607e8b6a8312331c124803b991945
