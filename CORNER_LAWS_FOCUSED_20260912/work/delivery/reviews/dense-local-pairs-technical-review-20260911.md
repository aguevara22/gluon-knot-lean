# Dense local pairs: technical review

2026-09-11. Reviewer: another agent of the same currently available model, independently reviewing the two root-authored topology helpers. This is a proof/type review, **not the stronger-model statement-fidelity approval requested by the user** and not acceptance of the source continuation theorem. No Lean/kernel/build, proof edit, canonical edit or acceptance-map change was performed.

**Finding:** no defect found in `dense_local_pairs_extend` or `dense_local_pairs_constant`. Their explicit local-pair and density hypotheses are essential obligations for a later geometric application; neither helper derives them for a wall path or a visible chamber.

`dense_local_pairs_extend` works on an arbitrary topological domain X and a dense subset S, with a function from the subtype S into an arbitrary type Y. It requires, at **every** point of X, an open neighbourhood containing that point on which all values of f at S-points agree. This includes points outside S. No topology, discreteness or separation axiom on Y is assumed: Mathlib's `IsLocallyConstant` means all set preimages are open and is equivalent to actual constant neighbourhoods.

For each x the selected open neighbourhood is nonempty because it contains x; density therefore supplies a point a(x) of S in it. Defining F(x) as f(a(x)) introduces no arbitrary default value. The pairwise hypothesis proves that every other S-point in that neighbourhood has this same value.

To prove local constancy, take y in the selected neighbourhood of x. The neighbourhoods of x and y have a nonempty open intersection because both contain y. Density supplies an S-point z in that intersection. Pairwise constancy identifies f(z) with F(y) and with F(x), giving F(y)=F(x). Agreement with f follows by taking the S-point itself in its selected neighbourhood. Thus the construction genuinely proves local constancy rather than assuming compatibility of arbitrary selected samples.

Uniqueness is among all functions satisfying both local constancy and agreement on S. At each x, intersect constant neighbourhoods for a proposed extension G and F, and use a dense-domain point in their intersection. Their agreement with f there forces G(x)=F(x); function extensionality gives equality. No Hausdorff codomain argument, limit operation or continuity extension theorem is silently used. Empty-domain cases are valid: choices are made only for actual x, whose neighbourhood supplies nonemptiness, so neither `Nonempty X` nor `Nonempty Y` is missing.

`dense_local_pairs_constant` adds only `PreconnectedSpace X`. It uses the constructed locally constant F and the proved Mathlib theorem that a locally constant function is constant on a preconnected space. Agreement on S then proves f(a)=f(b) for arbitrary a and b. The result does not require a chosen common codomain value, so preconnectedness without a separate nonemptiness premise is sufficient.

For the later `thm:A-continuation` application, the actual dense domain and the neighbourhood-pair equality must still be proved, including at every relevant nongeneric event. Ambient density of generic tuples alone does not imply density of their preimage under an arbitrary continuous path; an application on path parameters needs its own density argument, for example from the already established finite-event structure. These are application obligations, not flaws in either explicit helper statement. This report does not treat local-pair constancy as the source conclusion or as an available geometric axiom.

Receipt `DenseLocalPairs-prototype-result.json` records first root session **79413**, exit **0**. All **3/3** bound hashes match; the complete body occurs exactly once in the prototype. The log prints both expected declarations with only `propext`, `Classical.choice`, `Quot.sound` in their axiom traces and no `error:`, `sorryAx`, `native_decide` or `Lean.ofReduceBool` marker. The definition and exact neighbourhood/preconnectedness APIs were inspected in the local Mathlib sources.

| Bound file | SHA-256 |
| --- | --- |
| `work/checks/DenseLocalPairs.body.lean` | `11f2384626f702549dd37b874ba665a326f9613c768fcc5dbfe15b3ba1f48cdc` |
| `work/checks/DenseLocalPairs.prototype.lean` | `d0a735db50324c55500e0469ff6f612ca5299470cac2690952548191822e00df` |
| `work/checks/DenseLocalPairs-first-kernel.log` | `d7a6f72be075fc515dca7b44d83b8ef8cae5cb97ec95afdc43f6dace1abe66a9` |
| `work/checks/DenseLocalPairs-prototype-result.json` | `e4bf54d3fea4d4a0ffd1167e8ae8a903cb9a0f57dbdeac216e07a10a765050ed` |
| `work/lean/.lake/packages/mathlib/Mathlib/Topology/LocallyConstant/Basic.lean` | `2723dc5a4177d2b1a6a87be38b28ed024a7ae183ab7b37a2ea76072bef49892f` |
| `work/lean/.lake/packages/mathlib/Mathlib/Topology/Closure.lean` | `608f830e702214c420fdb7efd88386e82f09b9eb04469ffb5b03e10a9f1aa763` |

Passing checks and hashes do not establish source fidelity. Stronger statement-fidelity approval remains pending; acceptance remains **39/192 (20.3%)**, targets **0/8**.
