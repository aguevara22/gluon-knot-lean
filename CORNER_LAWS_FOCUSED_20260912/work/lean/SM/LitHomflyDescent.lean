-- Written 13:49Z 2026-09-15 by the pod executor on the author's decision of 2026-09-15 (work/AUTHOR_NOTES.md, D-GAP2): the printed descent sentence of lit:homfly declared as its own axiom about the existing SM.homfly, registered in lean/axiom-policy.json under "literature" as a second declaration of lit:homfly (not a sixth interface).
import SM.ContactPathOfDescent

/-! # lit:homfly, the descent sentence, declared spatially (second declaration of lit:homfly)

Registry text (blueprint/AXIOM_REGISTRY.md lines 10-17 = reference/SM/sm-3-statesum.tex 916-923), the
printed literature input lit:homfly: "There is a map D ↦ H_D(a,z) ∈ ℤ[a^{±1},z^{±1}] on oriented link
diagrams that is invariant under the three Reidemeister moves and planar isotopy, takes the value 1 on the
crossing-free circle, and satisfies aH_{D₊} − a⁻¹H_{D₋} = zH_{D₀} for every skein triple. Its value depends
only on the oriented link presented by D."

The accepted `SM.lit_homfly` (SM/LinkInterfaces.lean) declares the first sentence, with the last sentence
read over `LinkEquiv` (design D2).  On the author's decision of 2026-09-15 (GAP-2, additive form) the last
sentence — "Its value depends only on the oriented link presented by D" (sm-3:920-921) — is declared here
as its own axiom about the SAME map `SM.homfly`, read on the spatial vocabulary of rows 89-91:
`SM.AmbientIsotopyDescent` (SM/ContactPathOfDescent.lean), i.e. along a jointly smooth family of oriented
spatial embeddings whose two ends have ordinary regular generic xz projections, the values of `homfly` on
any polygonal readings of the two end diagrams agree.  The oriented link presented by a diagram is the
spatial link the diagram projects; the two ends of a smooth isotopy of spatial embeddings present the same
oriented link.

Nothing about `SM.lit_homfly` or `HomflyClauses` is modified.  Disclosed readings (work/AUTHOR_NOTES.md,
D-GAP2, FR-LHD-1..4): the clause is stated on a smooth family of embeddings, so it bundles the
isotopy-extension step that the printed proof of cp:finite-contact-path performs by hand (sm-3:3276-3312)
with the literature premise (FR-CP-7); the family is indexed by all of ℝ (FR-CP-4/5); the end diagrams are
read polygonally through `HeightMarking` (FR-1); both ends are required to have regular generic
projections.  Policy: lean/axiom-policy.json, "literature", second declaration of lit:homfly
(`SM.lit_homfly_descent`), authorised by the author. -/

namespace SM

/-- **lit:homfly, the descent sentence** (AXIOM_REGISTRY.md:14-15, sm-3:920-921; policy name
`SM.lit_homfly_descent`, second declaration of lit:homfly): "Its value depends only on the oriented link
presented by D" — for the map `homfly` of `lit_homfly`, along every jointly smooth family of oriented
spatial embeddings with ordinary regular generic end projections, on any polygonal readings of the two
ends (`AmbientIsotopyDescent`, SM/ContactPathOfDescent.lean). -/
axiom lit_homfly_descent : AmbientIsotopyDescent

end SM
