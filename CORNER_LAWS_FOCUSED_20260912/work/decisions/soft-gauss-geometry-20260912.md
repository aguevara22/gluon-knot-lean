# Common-interval soft Gauss geometry

Author: /root/review_contraction_candidates, the same currently available model as root. This is a two-declaration implementation draft, not an independent self-review, stronger-model statement-fidelity approval, source acceptance, or a claim that the whole soft-family lemma has been assembled. No Lean kernel/build/audit was run by this agent. Root owns testing and independent review. Only new work/checks files and this note were written.

`softNewbornVisits_next` applies the now-checked `gauss_next_of_no_visit_between` to the actual newborn incoming and return visits. Their distinctness is already proved from their distinct enlarged edge labels. `softNewbornVisits_no_between` supplies the empty oriented traversal arc from the explicit pointwise inherited bounds. This helper does not assume a successor or arbitrary cyclic adjacency; the complete sorted actual visit cycle determines the successor. The finite-order converse includes two-visit cycles and the last/first seam, so no nonempty parent crossing set or extra n bound is introduced.

`soft_small_gauss_geometry` takes the minimum of the positive radius from `soft_small_gauss_word_transport` and the positive radius from `soft_newborn_small_empty_arc`. It obtains actual child Generic, crossing persistence and full support classification from both established interval theorems. Their witness types are propositions. Lean proof irrelevance therefore aligns the hQ/hp/hclass proofs used in the maps and visits; no two numerical choices, crossing correspondences, or geometric objects are identified by an unproved equality.

On that one interval, the theorem returns the full non-loop Gauss-word equality via the actual inherited crossing map. For every proof of the exact loop-sector conjunction, it returns both strict newborn visit interiors; the two exact successor labels through the intervening soft edge; actual endpoint evaluations P j and P j + epsilon*q; exclusion of every actual child visit from the oriented incoming-to-return arc; the literal equality `nextGaussVisit incoming = return`; and intrinsic Cycle deletion equalities for visits and crossing letters. The filter predicates use inequality to the actual newborn crossing, so both newborn visits/letter occurrences are removed. Repeated letters are handled by the already-checked unrestricted Cycle.filter_map theorem.

All data are derived for arbitrary j, n>=3, parent Generic and actual SoftAdmissible. The radius precedes epsilon, and the loop proof is quantified after epsilon. The child at epsilon=0 is never assumed Generic. The non-loop clause is the complement of the exact loop conjunction; separate sign-sector classification is inherited from the earlier geometric work and is not restated here.

The exported successor labels and strict interiors identify the physical edge path containing M and M_epsilon. This wrapper does not add a separate `traversalBetween` assertion for those two zero-parameter vertex positions. If that exact predicate is required by the eventual all-clause source statement, the direct vertex-position consequence remains an additional obligation. This body also does not package the previously proved chamber, turn, all inherited point/parameter limits, or determinant-sign clauses. It is a bounded Gauss geometry/deletion assembly.

## Exact initial bindings

- `work/checks/SoftGaussGeometry.body.lean` and matching first-draft body: `c399d2b1d9a8d979be4395d058a95b545779697dd3d5dc6b66aa26df3ff94ac4`.
- `work/checks/SoftGaussGeometry.prototype.lean` and matching first-draft prototype: `7ad8abcee7e31dc6aad315ff50111599b99a4303e3a01366d45c4033481e41b4`.
- Ordered manifest `work/checks/SoftGaussGeometry-body-dependencies.json`: `db1423b2375c42a4976af36c3aafa15b6a23e7bf69e6e4d06eb2a26c060d0cb6`.
- Full draft/source/receipt bindings `work/checks/SoftGaussGeometry-draft-dependency-bindings.json`: `824decd19fb3fc4f120fddf156a49d30f06b2d1ad54ec3dc88ba43b25f8a3917`.

The prototype unions the actual ordered full-body embeddings from the frozen SoftGaussDeletion, SoftNewbornVisits and GaussNextFromEmptyArc passing prototypes, deduplicates them, and adds this body. Every source-receipt file hash was checked, and all 26 full bodies occur once in the new prototype. Only the two new declarations are printed. This inspection is not a kernel-pass claim.
