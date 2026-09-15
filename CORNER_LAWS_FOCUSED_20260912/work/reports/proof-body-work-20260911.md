# Bounded proof work, 11 September 2026

This work constructs and checks existing candidate proofs. It does not approve
the final corner/soft specification or substitute this model's judgment for the
pending independent statement-fidelity review.

Five candidate declarations now pass the pinned Lean kernel:

- NonunaryContraction: one definition and three theorems; root session 70905
  exited 0 on the second attempt. Its four axiom traces contain only permitted
  foundational axioms.
- ContractionPropagation: one theorem; root session 96039 exited 0 on the second
  attempt. Its axiom trace is exactly propext, Classical.choice and Quot.sound.

The propagation statement concerns the actual inverse-coordinate difference
when two triple arrays agree away from one critical triple. For every contracted
interval containing the distinguished leaf, it identifies that difference on
the expanded interval with the actual critical-span difference multiplied by
the contracted inverse coordinate. The response law itself is not a premise.

The proof uses the following steps, all inside the checked candidate:

1. At the distinguished leaf, expansion is the critical span and the contracted
   inverse coordinate is one. The claimed identity follows by multiplication
   by one.
2. Otherwise, interval expansion is injective, so the expanded parent is not
   the critical span. Far coefficients are therefore unchanged on this parent.
3. Nonsurviving compositions have unchanged child products. Thus their
   contribution to the difference is zero; their original values are not
   assumed zero or omitted from the original sums.
4. The nonunary expansion map preserves part count, is injective, and has exactly
   the surviving compositions as its range. Its sum theorem reindexes the
   complete difference sum using the zero contributions established in step 3.
5. Each nonunary composition has strictly shorter expanded children. Lean
   checks this measure for every recursive call. The containing child's
   induction hypothesis, together with unchanged other children, gives the
   complete product response.
6. Expanded coefficients agree with the contracted array's coefficients by
   their definitions. Hence the reindexed nonunary difference sum is the
   critical-span difference times the contracted nonunary sum.
7. The three actual inverse equations have zero right sides on these nonleaf
   intervals. Separating their unary coordinates and taking the checked linear
   combination yields the claimed propagation identity. No division is used.

The first propagation attempt failed because the sum binder did not cover the
whole difference summand. Parenthesizing that summand repairs the proof syntax.
The failed body, prototype and log are retained. The theorem header is byte for
byte identical to the baseline. The nonunary body was unchanged in this turn;
its previously prepared subtype-projection repair now has a successful receipt.

Verification found all 427 baseline files unchanged, including all 327 canonical
SM modules and the accepted map, axiom policy, pins and checker. No whole-library
audit was rerun; the prior canonical audit remains checkpoint 070.

Independent source/type review for these five candidates is pending. Kernel
success establishes the stated formal results under their recorded assumptions;
it does not certify their identification with the paper's final claims. Accepted
original progress remains 19/132 (14.39%); main targets remain 0/8.

Evidence: ../checks/NonunaryContraction-prototype-result.json,
../checks/ContractionPropagation-prototype-result.json,
../checks/proof-body-only-verification-20260911.json, and
../checkpoints/goal-turn-074.json.
