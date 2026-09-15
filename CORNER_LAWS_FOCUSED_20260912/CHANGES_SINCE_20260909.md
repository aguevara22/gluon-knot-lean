# Realignment note — from the shipped frame SM12 to the frozen frame SM15 (2026-09-12)

The handoff of 2026-09-09 shipped frame SM12 (SM11's mathematics). Since then eight statements it carried unrefereed were read by both auditor benches, repaired, re-read and retagged; the result is frame SM15, frozen 2026-09-12 (manifest self-hash `8659ffeb9bedcbfa8a9e197b648ef6d09cd27afb3e83e6986a9cb2bf5f02932a`, 215 pp). **Replace the bundle's `SM/` folder by `SM15/` from this package and regenerate the blueprint** (`blueprint/` here is already regenerated on SM15). The axiom registry, the R document and the bridge are unchanged. The complete byte-level diff SM12 → SM15 is `DIFF_SM12_to_SM15.txt`.

## 1. Statements whose formal content changed (restate in Lean if already written)

| label | file | change | effect on consumers |
|---|---|---|---|
| `lem:shift` (iii) | sm-1-polygons.tex | ℓ(P̄) = n − ℓ(P) − z(P), z(P) = number of zero turns; ℓ(P̄) = n − ℓ(P) for P ∈ 𝒰_n (the old identity was false off the generic locus) | both consumers apply it on 𝒰_n: unchanged |
| `lem:shift` (iv) | sm-1-polygons.tex | now stated for P ∈ ℛ_n (the regular locus, where rot exists), with σP, P̄ ∈ ℛ_n | consumer (a generic star) unchanged |
| `lem:g1` (iv) | sm-1-polygons.tex | "two **distinct** adjacent edges meet exactly in their common vertex" (the printed adjacency relation is reflexive) | consumers use distinct edges: unchanged |
| `prop:A-chamber` | sm-2-amplitude.tex | "A_g is constant on every **labelled** chamber (the root fixed)"; the proof now cites prop:chambers for chirotope constancy | all seven consumers use the fixed-root scope: unchanged |
| `lem:softvertex` | sm-2-amplitude.tex | hypotheses added: P generic, q admissible, 0 < ε < ε_0 of lem:soft-generic; conclusion "for every such ε" | no consumer |

Wording only, no formal change: `lem:g1` (ii) (the gloss's subject is the edge vector), `lem:chi-basic` (iii) (the left/right naming sentence is conditioned on a nonzero edge; the formula is unchanged).

## 2. Proofs whose text changed (the arguments to follow when proving them)
`lem:crossing-test` (cites lem:g1(i),(iii); prints the affine separation criterion), `lem:shift` ((iii) the reversal bijection sentence; (iv) closure of ℛ_n), `prop:A-chamber` (prop:chambers cited), `lem:softvertex` (lem:soft-generic(i),(iii) cited; the constant-sign argument on the connected interval (0, ε_0)).

## 3. Blast radius in the dependency graph
Statements depending (transitively) on at least one of the four formally changed statements: **45 of 224**, of which 16 are in the closure of `thm:comparison` (the comparison theorem itself is among them; `thm:floor` is not). Every one of them applies the changed clause inside the domain where the old and new forms agree (the generic locus, distinct edges, a fixed root), so **no dependent's statement changes**; a Lean proof of a dependent that invoked the old form needs, at most, the hypothesis discharged at the call site (P generic / edges distinct / root fixed). The list:

`lem:crossing-test`, `prop:chambers`, `lem:silentlocus`, `lem:shift`, `thm:relgp`, `prop:A-chamber`, `thm:A-continuation`, `cor:polyform`, `lem:weak-carriers`, `lem:C-weak-local`, `prop:C-chamber`, `prop:C-silent`, `thm:C-S3`, `thm:C-S5`, `thm:C-soft`, `prop:C-reversal`, `lem:star-generic`, `lem:transport`, `prop:anchors-exist`, `prop:anchor-values`, `thm:root-indep-proof`, `cor:A-lawful`, `cor:weak-root-indep`, `cor:weak-amplitude`, `thm:uniqueness`, `cor:uniqueness-weak`, `thm:comparison`, `cor:C-inherits`, `cor:comparison-weak`, `prop:star-decomp`, `sv:star-record`, `prop:star-torus`, `thm:C-star`, `lem:positive-affine`, `lem:decay-crossings`, `prop:decay`, `rel:block-primes`, `rel:common-path`, `rel:g1-domain`, `rel:block-jumps`, `rel:shuffle-wall`, `rel:distributed-soft`, `rel:shuffle-vanishing`, `thm:uone`, `thm:kk`

## 4. Tags
On SM15 every statement with a printed proof carries `proved (refereed: …)` naming its readers, or `new`; no bare `proved` and no `transcribed (unrefereed)` remain. The eight items of the erratum notice are: `lem:chi-basic`, `lem:g1`, `lem:crossing-test`, `lem:rot`, `lem:shift`, `lem:gates-nonzero`, `prop:A-chamber`, `lem:softvertex` — all now refereed by both benches (the tag text records the stamps).

## 5. Verify this package
`cd SM15 && shasum -a 256 -c FRAMED_MANIFEST_SM15.sha256` → 20 OK; `shasum -a 256 FRAMED_MANIFEST_SM15.sha256` → `8659ffeb9bedcbfa8a9e197b648ef6d09cd27afb3e83e6986a9cb2bf5f02932a`.
