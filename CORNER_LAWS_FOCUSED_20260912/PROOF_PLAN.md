# Proof steps

1. **Definitions and inputs.** Implement the selected SM polygon/generic/germ/wall
   definitions, tree amplitude prerequisites, independent supports, carriers,
   records, local polynomials, C and soft insertion. Preserve the cyclic quotient
   and child domains. Admit only `lit:homfly`, `lp:lm`, `lp:lm-uniqueness`,
   `ng:finite-word`, `src:contact` with their exact statements. Treat `hyp:R`
   and `CV:ax:R` as propositions whose truth is to be proved.
2. **Corner machinery.** Follow the selected Chapter 3 dependencies through the
   local polynomial construction, named-record invariance, front/contact bound,
   carrier floor, grouped products and singleton-zero lemma. Reuse proved SM
   constructions in CV via explicit equivalences wherever possible.
3. **Direct C laws.** Prove `prop:C-chamber`, `prop:C-silent`, `thm:C-S3`,
   `thm:C-S7`, `thm:C-S5`, `thm:C-soft`. Review every branch: both bigon graph
   types, sliding, both orientations and every soft sector, including dead
   selectors. Do not divide by an exterior factor that could be zero.
4. **Full cusp route.** Prove only the selected amplitude, transport, anchors,
   root-independence and uniqueness chain. Prove `thm:comparison` with an explicit
   R parameter, then `cor:C-inherits`. Its proof checks all substituted arguments
   are generic, including a threaded cusp's deletion. A proof of empty-cusp zero
   alone does not cover the requested cusp law.
5. **R.** Translate the selected CV prerequisites from proved SM results and
   the five permitted interfaces. Prove the eight supplied RA arguments and
   missing full-domain assembly in OPEN_WORK.md. No CV `thm:main`, `ax:lawful`,
   owner normalization, assumed R or downstream SM comparison may prove R.
   `CV:selector_A` requires only the minimum-three-corners clause;
   `CV:singleton_D_i` requires only the stated degree gap and zero conclusion.
6. **Bridge and final assembly.** Formalize B1 (SM germs lie in the required CV
   domain), B2 (exact forced zero set), B3 (transversality), B4 (matching scalar
   side values). Apply the proved CV R theorem to obtain SM R. Instantiate
   `cor:C-inherits`, combine with direct soft and empty-cusp results, and prove
   `SM.corner_laws_and_soft` with no R parameter.
7. **Review and deliver.** Populate all selected rows and helper/R/bridge rows,
   review source fidelity independently, run the axiom checker, then the complete
   focused stage-1 check. Report the actual conjunction proved and all remaining
   issues; package the implementation and evidence.

`blueprint/ORDER.md` gives an initial dependency order. Steps 3–4 can use a
transparent R parameter while step 5 develops independently. Refine helper
dependencies in work/; checkpoint and report percentage after each work unit.
No standalone Catalan/torus evaluation, decay, KK relation, census or finite
certificate is commissioned. A lemma that is needed by the retained proof chain
is still required even if it originally appeared in another chapter.
