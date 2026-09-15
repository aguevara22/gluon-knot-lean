# Remaining work after checked incident responses

FlatIncidentAllSizes.body.lean now proves the signed incident response at every
permitted source arity. The boundary, affine/sign, incident tuple and integer
factor candidates are frozen. Do not modify their passing bodies to simplify
the remaining task. The original thm:A-S3 row remains pending.

1. Implement the complete nonincident tuple identity described in
   nonincident-flat-tuple-identification-20260911.md. Prove erasure count one,
   contractedSize equal to the child arity, and actual label equality for every
   child vertex. Use ZMod.ringEquivCongr with the proved size equality, or an
   equivalent explicitly proved transport. A tuple coefficient transport lemma
   across that arity equality must be derived by equality induction. Do not
   infer the full tuple identity from the already proved physical endpoints.
2. Identify its coefficient with the deletion polygon at fusionIndex j g using
   treeCoefficient_shift only after proving the full tuple/root correspondence.
   Apply the arbitrary-affine integer single-triple response with coordinates
   (0,r,1), the two-leaf multiplier and the proper span from the checked boundary
   result. This supplies the nonincident signed germ response on the full source
   FlatAt domain.
3. Combine nonincident and incident responses for every root. Their equations
   must retain the fixed sign, positive common neighborhood for independent
   side points, integer coefficients, and center-valued actual deletion root.
4. Convert time-side subtraction to the source right-minus-left subtraction.
   The source right side has turn -1 and left side +1. The checked response
   gives minus(turnPlus)+turnMinus = 2*d with d in {-1,1}. Prove the resulting
   two possible turn pairs explicitly; do not identify time sign with turn sign.
   For arbitrary source right/left points, use generic-side turn constancy and
   the germ sign-change premise to justify their opposite time-side placement.
   Then orient the coefficient subtraction and assemble thm:A-S3.

Lean note from the incident implementation: casts between definitionally equal
but unreduced size expressions can fail at the rewrite tactic's implicit
transparency. Normalize the type explicitly or use a justified more transparent
rewrite. Tuple replacement also changes its dependent G1 proof: use the proved
treeCoefficient_congr_tuple helper or equality induction, rather than an
ill-typed rewrite motive. These are implementation issues, not reasons to add
an axiom or alter the source domain.

Keep stronger fidelity review and canonical acceptance distinct from candidate
proof construction. No author input or external message is needed.
