# Plan: thm:root-indep-proof → `SM.root_independence` (scout report, 2026-09-13)

Scout: Claude Code subagent (read-only on the library; `lake env lean` used on /tmp files).
Source: `reference/SM/sm-6-comparison.tex` lines 53–104 (theorem + proof), lines 5–51
(lem:A-small-values); `reference/SM/sm-5-transport.tex` 299–316 (lem:transport), 373–460
(def:anchors, prop:anchors-exist). Library: `work/lean/SM/` (oleans present; toolchain
`leanprover/lean4:v4.34.0-rc2`, Mathlib rev `85e3a25e…`, see `work/lean/lakefile.toml`).

## 0. Executive summary

* **The whole proof has been drafted and compiles** against the current oleans
  (`lake env lean`, 13 s, sorry-free, axioms `propext, Classical.choice, Quot.sound`),
  **conditional on the conclusion of lem:transport exactly as fixed in
  `work/drafts/TransportLemma_statement.lean`**. The complete file is Appendix A (≈500 lines);
  every lemma specification in §3 below is quoted from it, so provers can port it verbatim into
  `work/lean/SM/RootIndependence.lean` (add `import SM.RootIndependence` to
  `work/lean/Supplemental.lean`, next to line 71 `import SM.TreeChamber`).
* Final statement (verified):
  ```lean
  theorem root_independence
      (transport : ∀ {n : ℕ} [NeZero n], 3 ≤ n + 1 → ∀ {r : ℤ} {P Z : LabelledTuple (n + 1)},
        Generic P → Generic Z → rotationNumber P = r → rotationNumber Z = r →
        TransportConclusion r P Z)
      (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n) :
      treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn
  ```
  where `TransportConclusion r P Z` is, verbatim, the conclusion of the draft `SM.transport_lemma`.
  **Integration when lem:transport lands** (verified against a `sorry`-bodied copy of the draft
  statement): `root_independence @transport_lemma n hn P hP g h` typechecks by defeq
  (`TransportConclusion` is a plain `def`). Do not write the lambda
  `fun hn hP hZ hrP hrZ => transport_lemma …` — the explicit binders swallow the implicit
  `{n} {r} {P} {Z}` and fail; use `@transport_lemma`.
* **Only gap**: the proof of lem:transport itself (pending, other agents). Every other fact the
  source proof uses is in the library (§2), plus ten small new lemmas proved in the draft (§3, §4).
  There is no rotation-invariance lemma in the library; the draft adds `det_rotationMap`,
  `chi_rotationMap`, `treeCoefficient_rotationMap` (3 + 3 + 4 lines).

## 1. The source argument, in library terms

`Δ_gh(Q) := A_g(Q) − A_h(Q)`. Strong induction on the arity. `n = 3`: lem:A-small-values (i).
`n = m + 1 ≥ 4`, `P` generic of rotation `r ∈ ℤ` (rotation is an integer for regular tuples,
`rotationNumber_integer`; `(n, r)` is admissible, `generic_rotation_admissible`). Choose the target
`Z` by `anchor_cases_exhaustive`:
(Z) `Admissible (m) r` → `Z` = mixed-sector soft insertion into a generic `m`-gon of rotation `r`
whose soft edge label avoids `g, h`, with `ε` below the lem:soft-rotation bound and the thm:A-soft
bound, so `A_g(Z) = A_h(Z) = 0`;
(L) `MinimalAdmissible (m+1) r ∧ 2 ≤ |r|` → `m + 1 = 2|r| + 1`, `Z = star |r|` (r > 0) or
`starNeg |r|` (r < 0), all roots equal by rotation symmetry / reversal;
(L₀) `(m+1, r) = (4, 0)` → `Z = bowTie`, every root of every shift is `−1`.
lem:transport gives `k` (`k = 0` unless `(4,0)`) and a path `P ⇝ shift k Z` with finitely many
simple wall germs of types F, V, T, E, C, generic deletions/halves. `Δ` is locally constant off the
finite wall set (prop:A-chamber / chi-congruence), has zero jump at each wall (A-S3 + IH at the
deletion; A-S7 + IH at both halves; A-R3E), hence `Δ(P) = Δ(shift k Z) = 0`.

## 2. Library facts consumed (verbatim statements; file:line)

### 2.1 prop:A-chamber and chambers
Row `prop:A-chamber` → `SM.A_chamber`, module `SM.TreeChamber` (`work/lean/SM/TreeChamber.lean:92`):
```lean
theorem A_chamber (hn : 3 ≤ n) :
    (∀ (P Q : LabelledTuple n) (hP : G1 P) (hQ : G1 Q),
      (∀ i j k, chi P i j k = chi Q i j k) →
      ∀ g, TreeDataEqual P Q hP hQ g hn) ∧
    (∀ (P Q : GenericTuple n), Q ∈ labelledChamber P →
      ∀ g, TreeDataEqual P.val Q.val P.property.1 Q.property.1 g hn) ∧
    (∀ (P Q : GenericTuple n), polygonProjection Q ∈ chamber (polygonProjection P) →
      ∃ a : ZMod n, Q ∈ labelledChamber (genericShift a P) ∧
        ∀ g : ZMod n, treeCoefficient Q.val Q.property.1 (g - a) hn =
          treeCoefficient P.val P.property.1 g hn) ∧
    (∀ (P Q : {P : LabelledTuple n // G1 P}) (γ : Path P Q),
      (∀ s t : unitInterval, ∀ i j k, chi (γ s).val i j k = chi (γ t).val i j k) →
      ∀ g (s t : unitInterval),
        TreeDataEqual (γ s).val (γ t).val (γ s).property (γ t).property g hn)
```
(`TreeDataEqual P Q hP hQ g hn`, TreeChamber.lean:81, is a conjunction whose last component is
`treeCoefficient P hP g hn = treeCoefficient Q hQ g hn`.) The engine behind it — and what the
plan uses directly — is the chi-congruence lemma (`TreeCoefficient.lean:123`):
```lean
theorem treeCoefficient_eq_of_chi {P Q : LabelledTuple n} (hP : G1 P) (hQ : G1 Q)
    (hchi : ∀ i j k, chi P i j k = chi Q i j k) (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient P hP g hn = treeCoefficient Q hQ g hn
```
so `treeCoefficient` factors through the chirotope (item 8 answered: yes, already in the library).

Chambers (`Chambers.lean:14–29`): `abbrev GenericTuple (n) := {P : LabelledTuple n // Generic P}`;
`def labelledChamber (P : GenericTuple n) : Set (GenericTuple n) := connectedComponent P`;
`def chamber (P : GenericPolygon n) := connectedComponent P` (GenericPolygon = cyclic quotient).
So chambers are **connected components** (not path components, though
`labelledChambers_open_pathConnected (hn : 3 ≤ n) (P) : IsOpen (labelledChamber P) ∧
IsPathConnected (labelledChamber P)` at Chambers.lean:48 shows they coincide, via
`genericTuple_locallyPathConnected`). Row `def:chamber` → `SM.chamber_definition`
(`CyclicChambers.lean:133`) records `labelledChamber Q = connectedComponent Q` and the cyclic
saturation `polygonProjection ⁻¹' chamber (polygonProjection P) = ⋃ a, labelledChamber (genericShift a P)`.

Lemmas connecting "continuous path with generic values" to constant chi/same chamber:
* `ChamberPaths.lean:9`
  ```lean
  theorem generic_family_chi_constant {F : α → GenericTuple n} (hF : Continuous F)
      (s t : α) (i j k : ZMod n) : chi (F s).val i j k = chi (F t).val i j k
  ```
  (`[TopologicalSpace α] [PreconnectedSpace α]`; proof `PreconnectedSpace.constant … (continuous_generic_chi i j k).comp hF`).
* `Chambers.lean:56` `continuous_generic_chi (i j k) : Continuous (fun P : GenericTuple n => chi P.val i j k)`.
* `TreeChamber.lean:24` `labelled_chamber_chi_constant (P Q : GenericTuple n) (hQ : Q ∈ labelledChamber P) (i j k) : chi P.val i j k = chi Q.val i j k` (via `isPreconnected_connectedComponent.constant`).
* `GenericCurveChamber.lean:10` `generic_curve_local_chamber (hn) (g : WallGerm m) (F : g.Parameter → LabelledTuple n) (hF : Continuous F) (h0 : Generic (F g.zeroParameter)) : ∃ δ, 0 < δ ∧ δ ≤ g.radius ∧ ∀ t, |t.val| < δ → ∃ ht : Generic (F t), ⟨F t, ht⟩ ∈ labelledChamber ⟨F g.zeroParameter, h0⟩ ∧ …`.
* `GermTreeEquality.lean:79` `WallGerm.tree_sides_equal_of_local_zero` — shows the idiom
  `generic_family_chi_constant (w.continuous_sideTuple true) q t i j k` for constancy of `A_g`
  along one germ side.
* Topology: `GenericTopology.lean:115` `generic_persists (hn : 3 ≤ n) (hP : Generic P) : ∀ᶠ Q in 𝓝 P, Generic Q`;
  `:134` `isOpen_Generic (hn) : IsOpen {P | Generic P}`; `:18` `continuous_area (i j k) : Continuous (fun P => det (P j - P i) (P k - P i))`;
  `Generic.lean:55` `g1_area_ne_zero (h : G1 P) (hij) (hjk) (hik) : det (P j - P i) (P k - P i) ≠ 0`.
* Also `TreeCoefficient.lean:141` `treeCoefficient_shift (P) (hP) (g a) (hn) : treeCoefficient (shift a P) (g1_shift_forward a hP) (g - a) hn = treeCoefficient P hP g hn`
  and `IncidentFlatGapTuples.lean:98` `treeCoefficient_congr_tuple (P Q) (hP) (hQ) (he : P = Q) (g) (hk) : treeCoefficient P hP g hk = treeCoefficient Q hQ g hk` (dependent transport of the G1 witness).

**How used.** In the plan, prop:A-chamber is used in its pointwise form: at a generic point of a
continuous family, chi is eventually constant (`continuousAt_sign_of_ne_zero` + `continuous_area`,
finitely many triples via `Filter.eventually_all`), hence `A_g` is eventually constant by
`treeCoefficient_eq_of_chi`. No chamber or path component is needed (see (A) in §3).

### 2.2 thm:A-S3 (flat law), induced roots, deletion
Row `thm:A-S3` → `SM.WallGerm.flat_law_treeCoefficient`, `FlatLawTree.lean:27`:
```lean
theorem flat_law_treeCoefficient (w : WallGerm (n + 1)) (j : ZMod (n + 1)) (hf : w.FlatAt j) :
    (∃! b : Bool, w.FlatRightSide j b ∧ w.FlatLeftSide j (!b)) ∧
    G1 (deleteVertex w.center j) ∧
    ∀ g : ZMod (n + 1), ∀ sRight sLeft : w.Parameter,
      ∀ hRight0 : sRight.val ≠ 0, ∀ hLeft0 : sLeft.val ≠ 0,
      turn (w.curve sRight) j = -1 → turn (w.curve sLeft) j = 1 →
      treeCoefficient (w.curve sRight) (w.generic_punctured sRight hRight0).1 g
          (by have := hf.1; omega) -
        treeCoefficient (w.curve sLeft) (w.generic_punctured sLeft hLeft0).1 g
          (by have := hf.1; omega) =
        treeCoefficient (deleteVertex w.center j) (g1_deleteVertex hf.2.1) (deletionRoot j g)
          (by have := hf.1; omega)
```
Sides: **not** "positive/negative parameter" but `P_right` = the side where `turn (·) j = -1`,
`P_left` = where `turn (·) j = 1`, each evaluated at an arbitrary parameter of that side
(`sRight`, `sLeft : w.Parameter = Set.Ioo (-w.radius) w.radius`, nonzero). Which sign of parameter
is the right side is given by `flat_named_sides` (`NamedWallSides.lean:31`):
`∃! b : Bool, g.FlatRightSide j b ∧ g.FlatLeftSide j (!b)` with
`FlatRightSide j b := ∀ t : g.SideParameter, turn (g.sideTuple b t).val j = -1` (`:11`),
`FlatLeftSide j b := ∀ t, turn (g.sideTuple b t).val j = 1` (`:14`), `b = true` = positive parameters.
`hf.1 : 4 ≤ n + 1` (`FlatAt`, `NamedWallPredicates.lean:14`:
`4 ≤ n ∧ g.pointZeros = {turnSupport j} ∧ g.concurrences = ∅ ∧ StrictBetween (g.center (j-1)) (g.center j) (g.center (j+1)) ∧ g.SignChanges (fun P => (turn P j : ℝ))`).

Induced root `D_j(g)`: `InducedRootsDefinition.lean:25`
`def deletionRoot (j g : ZMod (n + 1)) : ZMod n := fusionIndex j g`, with the printed description
`DeletionRootData` (`:33–49`): incident `g ∈ {j-1, j}` ↦ `-1` (fused edge `[μ_{j-1}, μ_{j+1}]`),
otherwise the unique edge of `P ∖ j` with endpoints `P g, P (g+1)`. Row `def:induced-roots` →
`SM.induced_roots_definition` (`:157`). Deletion: `DeletedTuple.lean:13`
`def deleteVertex (P : LabelledTuple (n + 1)) (j : ZMod (n + 1)) : LabelledTuple n := fun i => P (deletionIndex j i)`.

**How used.** With `s₁ < 0 < s₂` two curve parameters, `flat_named_sides` decides which of
`s₁, s₂` is `sRight`; apply the law to `g` and to `h` with the same `(sRight, sLeft)` and subtract:
`Δ_gh(curve s₂) − Δ_gh(curve s₁) = ±(A_{D_j g}(Q) − A_{D_j h}(Q)) = 0` by the IH at arity `n`
(`Q = deleteVertex w.center j`, generic by the transport conjunct). Lemma (B-F) in §3.

### 2.3 thm:A-S7 (vertex–edge law), halves, half roots
Row `thm:A-S7` → `SM.WallGerm.vertex_edge_law_treeCoefficient`, `VertexEdgeLawTree.lean:27`:
```lean
theorem vertex_edge_law_treeCoefficient (w : WallGerm n) (M a : ZMod n) (hn : 3 ≤ n)
    (hc : w.VertexEdgeAt M a) :
    (w.BigonAt M a ∨ w.SlidingAt M a) ∧
    (w.contactSign M a ≠ 0 ∧
      ∀ s : w.SideParameter, chi (w.sideTuple false s).val a (a + 1) M = w.contactSign M a) ∧
    G1 (firstHalf w.center M a) ∧ G1 (secondHalf w.center M a) ∧
    ∀ g : ZMod n, ∀ s t : w.SideParameter,
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn -
        treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn =
        (w.contactSign M a : ℤ) *
          (treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1)
              (halfRoots M a g).1 (contactHalfSizes_bounds hn hc.1).1.1 *
            treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1)
              (halfRoots M a g).2 (contactHalfSizes_bounds hn hc.1).2.1)
```
Sides: `P_+ = w.sideTuple true t`, `P_- = w.sideTuple false s` (positive / negative parameters,
`SideParameter = Set.Ioo 0 w.radius`, `sideTime true t = ⟨t.val,_⟩`, `sideTime false s = ⟨-s.val,_⟩`,
`WallGerm.lean:34–50`). The sign `s = w.contactSign M a := chi (sideTuple false sideBase).val a (a+1) M`
(`NamedWallSides.lean:58`). Both branches (bigon `BigonAt`, sliding `SlidingAt`) are covered by
the single hypothesis `hc : w.VertexEdgeAt M a` (`NamedWallPredicates.lean:19`:
`ContactSeparated M a ∧ g.pointZeros = {contactSupport M a} ∧ g.concurrences = ∅ ∧ g.center M ∈ edgeInterior g.center a ∧ g.SignChanges (fun P => (chi P a (a+1) M : ℝ))`).
Halves `λ₁ = firstHalf w.center M a : LabelledTuple (firstHalfSize M a)` (vertices `M,…,a`, closing
edge `-1 = [μ_a, μ_M]`), `λ₂ = secondHalf w.center M a : LabelledTuple (secondHalfSize M a)`
(vertices `M, a+1, …, M-1`, opening edge `0 = [μ_M, μ_{a+1}]`); `firstHalfSize M a = contactDistance M a + 1`,
`secondHalfSize M a = n - contactDistance M a` (`ContactHalfSizes.lean:12,14`);
`contactHalfSizes_bounds (hn : 3 ≤ n) (h : ContactSeparated M a) : (3 ≤ firstHalfSize M a ∧ firstHalfSize M a ≤ n - 2) ∧ (3 ≤ secondHalfSize M a ∧ secondHalfSize M a ≤ n - 2)` (`:45`);
`NeZero` instances `firstHalfSize_neZero`, `secondHalfSize_neZero` (`ContactHalfIndices.lean:11,14`).
Root map `H(g) = (h₁, h₂)`: `def halfRoots (M a g : ZMod n) := contactHalfRoots M a g`
(`InducedRootsDefinition.lean:29`), `contactHalfRoots M a g := if g = a then (-1, 0) else if (g - M).val < contactDistance M a then (((g - M).val : ZMod _), 0) else (-1, ((g - a).val : ZMod _))` (`ContactHalfRoots.lean:16`); printed description `HalfRootsData` (`InducedRootsDefinition.lean:52–78`).
The G1 witnesses: `g1_firstHalf (hn) (h : ContactSeparated M a) (hz : pointZeroTriples P = {contactSupport M a}) : G1 (firstHalf P M a)` (`ContactHalfTuples.lean:67`), same for `g1_secondHalf` (`:72`).

**How used.** Subtracting the law for `g` and for `h` at the same `(s, t)`:
`Δ_gh(P_+) − Δ_gh(P_-) = s·(A_{h₁}(λ₁)A_{h₂}(λ₂) − A_{h₁'}(λ₁)A_{h₂'}(λ₂))`; the IH at arities
`firstHalfSize M a`, `secondHalfSize M a` (both `< n+1` by the transport conjunct, `≥ 3` by
`contactHalfSizes_bounds`; halves generic by the transport conjunct) gives `A_{h₁}(λ₁) = A_{h₁'}(λ₁)`
and `A_{h₂}(λ₂) = A_{h₂'}(λ₂)`, so the jump is `0`. Lemma (B-V) in §3.

### 2.4 thm:A-R3E (T, E, C: zero jump for every root)
Row `thm:A-R3E` → `SM.WallGerm.triple_and_silent_laws_treeCoefficient`, `TripleSilentLawsTree.lean:26`:
```lean
theorem triple_and_silent_laws_treeCoefficient (hn : 3 ≤ n) :
    (∀ (w : WallGerm n) (e f k : ZMod n), w.TripleAt e f k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        TreeDataEqual (w.sideTuple true t).val (w.sideTuple false s).val
          (w.sideTuple true t).property.1 (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (M a : ZMod n), w.ExtensionAt M a →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn) ∧
    (∀ (w : WallGerm n) (i j k : ZMod n), w.PureCutAt i j k →
      ∀ (g : ZMod n) (s t : w.SideParameter),
        treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 g hn =
          treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 g hn)
```
(T): take `.2.2` of the `TreeDataEqual`. Used as: `A_g(P_+) = A_g(P_-)` for `g` and for `h`, so
`Δ_gh(P_+) = Δ_gh(P_-)`. Lemma (B-TEC) in §3.

### 2.5 thm:A-S4 (cusp) — not needed
Row `thm:A-S4` → `SM.WallGerm.cusp_law_treeCoefficient` (`CuspLawTree.lean`). The transport
statement lists only `FlatAt / VertexEdgeAt / TripleAt / ExtensionAt / PureCutAt`; thm:relgp's
`RelativeGeneralPositionPath` has `no_cusp : ∀ t (g : WallGerm n), g.center = path t → ∀ j, ¬ g.CuspAt j`
(`RelativeGeneralPosition.lean:58`, from `not_cuspAt_of_regular` since the path is regular). Not used.

### 2.6 thm:A-soft, lem:soft-generic, lem:soft-rotation, def:soft
Row `thm:A-soft` → `SM.SoftDuplication.soft_theorem_treeCoefficient`, `SoftTheoremTree.lean:28`:
```lean
theorem soft_theorem_treeCoefficient (hn : 3 ≤ n) {P : LabelledTuple n}
    (hP : Generic P) (j : ZMod n) (q : Plane) (hq : SoftAdmissible P j q)
    (ε0 : ℝ) (hε0 : 0 < ε0) :
    ∃ ε1 : ℝ, 0 < ε1 ∧ ε1 ≤ ε0 ∧ ∀ ε : ℝ, 0 < ε → ε < ε1 →
      ∃ hQ : Generic (softInsertion P j q ε),
        ∀ a : ZMod (n + 1), a ≠ softOldIndex j j → ∃! g : ZMod n,
          a = softParentEdge j g ∧
          (treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) : ℚ) =
            softAmplitudeMultiplier P j q * (treeCoefficient P hP.1 g hn : ℚ) ∧
          ((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              -(turn P j : ℤ) * treeCoefficient P hP.1 g hn) ∧
          ((softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) = 0) ∧
          ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
            treeCoefficient (softInsertion P j q ε) hQ.1 a (by omega : 3 ≤ n + 1) =
              (turn P j : ℤ) * treeCoefficient P hP.1 g hn)
```
Coverage: **every root `a` of `P_ε` other than the soft edge `softOldIndex j j`** (the return edge
`softNewIndex j = softParentEdge j j` is included, corresponding to `E_j`). One bound `ε1` serves all
roots at once, so the source's "two root-specific bounds" collapse to one call. The mixed-sector
clause `(softAttachmentMinus ≠ softAttachmentPlus) → A_a(P_ε) = 0` is what the target uses.
The `ε0` argument lets one pass any positive number (we pass the lem:soft-rotation bound).

Row `lem:soft-generic` → `SM.soft_family_generic`, `SoftGenericLemma.lean:37` — clause (i)
(lines 54–70): `∃ δ > 0, ∃ B : GenericTuple (n + 1), ∀ ε, 0 < ε → ε < δ → ∃ hQ : Generic (softInsertion P j q ε), … ⟨softInsertion P j q ε, hQ⟩ ∈ labelledChamber B ∧ …`.
Not needed directly: `soft_theorem_treeCoefficient` already returns `hQ : Generic (softInsertion P j q ε)`,
and the rotation comes from:

Row `lem:soft-rotation` → `SM.soft_rotation_law`, `SoftRotationLaw.lean:17`, first conjunct:
```lean
(∃ ε₀ > 0, ∀ ε : ℝ, 0 < ε → ε < ε₀ →
  Generic (softInsertion P j q ε) ∧
  (((softAttachmentMinus P j q = -turn P j ∧ softAttachmentPlus P j q = -turn P j) ∨
      softAttachmentMinus P j q ≠ softAttachmentPlus P j q) →
    rotationNumber (softInsertion P j q ε) = rotationNumber P) ∧
  ((softAttachmentMinus P j q = turn P j ∧ softAttachmentPlus P j q = turn P j) →
    rotationNumber (softInsertion P j q ε) = rotationNumber P - (turn P j : ℝ)))
```
(hypotheses `(hn : 3 ≤ n) (hP : Generic P) (j) (q) (hq : SoftAdmissible P j q)`).
Also `soft_rotation_of_regular_interval` (`SoftRotation.lean:431`) gives the same on any interval on
which the family is regular. def:soft: `softInsertion P j q ε : LabelledTuple (n+1)`, labels
`softOldIndex j k` (old vertex `μ_k`), `softNewIndex j` (new vertex `μ_j + ε q`), soft edge label
`softOldIndex j j`, return edge `softNewIndex j`; `softParentEdge j k := if k = j then softNewIndex j else softOldIndex j k`
(`SoftParentEdges.lean:40`); attachment signs `softAttachmentMinus P j q = -sign (det (edge P (j-1)) q)`,
`softAttachmentPlus P j q = -sign (det q (edge P j))` (`SoftInsertionDefinition.lean:43–50`).

### 2.7 prop:A-reversal
Row → `SM.treeCoefficient_reversal_shift_law`, `ReversalShiftLaw.lean:18`:
```lean
theorem treeCoefficient_reversal_shift_law (hn : 3 ≤ n) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) :
    treeCoefficient (shift 1 P) (g1_shift_forward 1 hP) g hn = treeCoefficient P hP (g + 1) hn ∧
    (∀ i : ZMod n, reversal P i = P (2 - i)) ∧
    treeCoefficient (reversal P) (g1_reversal_forward hP) (1 - g) hn =
      (-1) ^ n * treeCoefficient P hP g hn
```
Components: `treeCoefficient_shift_one` (`TreeReversal.lean:457`) `A_g(σP) = A_{g+1}(P)` with `σ = shift 1`
(`shift k P i = P (i + k)`, `Polygon.lean:22`); `treeCoefficient_reversal` (`:462`)
`A_{1-g}(P̄) = (-1)^n A_g(P)` with `reversal P i = P (2 - i)` (`Reversal.lean:11`). Indices are `ZMod n`.
Also `generic_reversal (P) : Generic (reversal P) ↔ Generic P` (`GenericReversal.lean:64`),
`generic_shift (a) (P) : Generic (shift a P) ↔ Generic P` (`Generic.lean:45`),
`rotationNumber_shift`, `rotationNumber_reversal (h : Regular P) : rotationNumber (reversal P) = -rotationNumber P`.

### 2.8 lem:star-generic (i) and rotation invariance
Row → `SM.star_generic_law`, `StarGenericLaw.lean:21` (for `r ≥ 1`, `N = 2r+1`, `star r : LabelledTuple (2*r+1)`):
```lean
theorem star_generic_law {r : ℕ} (hr : 1 ≤ r) :
    (Nat.gcd r (2 * r + 1) = 1 ∧
    (shift 1 (star r) = (rotationMap (starAngle r)) ∘ star r ∧
      (∀ i, principalTurn (star r) i = starAngle r) ∧
      starAngle r ∈ Set.Ioo 0 Real.pi ∧
      (∀ i, turn (star r) i = 1) ∧
      rotationNumber (star r) = (r : ℝ)) ∧
    (∀ i, euclideanLength (edgePoint (star r) i (1 / 2)) = starRadius r ∧ … ) ∧
    (Generic (star r) ∧ Generic (starNeg r) ∧ (∀ i, turn (starNeg r) i = -1) ∧
      rotationNumber (starNeg r) = -(r : ℝ))) ∧
    (Generic bowTie ∧ … ∧ rotationNumber bowTie = 0 ∧ crossingSet bowTie = {{1, 3}})
```
Projections used: `(star_generic_law hr).1.2.1.1 : shift 1 (star r) = rotationMap (starAngle r) ∘ star r`
(also `shift_one_star_eq_rotation r`, `StarPolygons.lean:195`); `.1.2.1.2.2.2.2 : rotationNumber (star r) = r`;
`.1.2.2.2.1 : Generic (star r)`; `.1.2.2.2.2.1 : Generic (starNeg r)`; `.1.2.2.2.2.2.2 : rotationNumber (starNeg r) = -r`.
`rotationMap θ : Plane →ₗ[ℝ] Plane` with `rotationMap_apply θ v = (cos θ * v.1 - sin θ * v.2, sin θ * v.1 + cos θ * v.2)`
(`StarPolygons.lean:44,51`). `starNeg r := reversal (star r)` (`:35`).
**No invariance lemma exists** (grep for `rotationMap`, `chi_map`, `det_map`, `LinearMap`,
`treeCoefficient_congr`, `chi_congr` in `work/lean/SM` finds only `rotationMap_apply`,
`rotationMap_cos_sin`, `rotationMap_unitPoint`). What is needed and now proved (Appendix A):
`det_rotationMap θ u v : det (rotationMap θ u) (rotationMap θ v) = det u v` (one `linear_combination`
with `Real.cos_sq_add_sin_sq`), `chi_rotationMap θ P i j k : chi (rotationMap θ ∘ P) i j k = chi P i j k`
(`simp only [chi, Function.comp, ← map_sub, det_rotationMap]`), `g1_rotationMap`, and
`treeCoefficient_rotationMap` via `treeCoefficient_eq_of_chi`. `treeCoefficient` factors through chi
already (§2.1), so nothing in `Gates.lean`/`FiniteCompositions.lean` needs touching.

### 2.9 lem:A-small-values, def:star, bow-tie
Row `lem:A-small-values` → `SM.A_small_values_lemma`, `SmallValuesLemma.lean:19`:
```lean
theorem A_small_values_lemma :
    (∀ (P : LabelledTuple 3) (hP : G1 P), ∃ τ : SignType, τ ≠ 0 ∧ (∀ i, turn P i = τ) ∧
      ∀ g : ZMod 3, treeCoefficient P hP g (by norm_num) = -(τ : ℤ)) ∧
    (∀ (k : ℤ) (g : ZMod 4),
      treeCoefficient (shift (k : ZMod 4) bowTie) (g1_shift_forward (k : ZMod 4) bowTie_G1) g
        (by norm_num) = -1)
```
For the `(4,0)` target use the `ZMod`-indexed form `A_small_values_ii (k g : ZMod 4) :
treeCoefficient (shift k bowTie) (g1_shift_forward k bowTie_G1) g (by norm_num) = -1` (`SmallValues.lean:500`).
Row `def:star` → `SM.star_definition` (`StarDefinition.lean:15`): `star r t = unitPoint (2r+1) (r * (t - 1))`,
`starNeg r = reversal (star r)`, `bowTie 1 = (0,0), bowTie 2 = (2,2), bowTie 3 = (0,2), bowTie 4 = (2,0)`
(`bowTie : LabelledTuple 4`, `BowTie.lean:16`; `bowTie_generic : Generic bowTie` `:45`; `bowTie_rotation : rotationNumber bowTie = 0` `:98`).

### 2.10 lem:transport (fixed draft statement) and thm:mycyclic
`work/drafts/TransportLemma_statement.lean` (proof pending):
```lean
theorem transport_lemma {n : ℕ} (hn : 3 ≤ n + 1) {r : ℤ} {P Z : LabelledTuple (n + 1)}
    (hP : Generic P) (hZ : Generic Z) (hrP : rotationNumber P = r) (hrZ : rotationNumber Z = r) :
    ∃ k : ZMod (n + 1), ((((n + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      ∃ path : unitInterval → LabelledTuple (n + 1),
        Continuous path ∧ path 0 = P ∧ path 1 = shift k Z ∧
        (∀ t, Regular (path t)) ∧
        (∃ (N : ℕ) (hN : 0 < N), ∀ j : Fin N, ∃ a b : LabelledTuple (n + 1),
          ∀ t ∈ uniformMeshCell N hN j, path t = a + (t : ℝ) • b) ∧
        {t : unitInterval | ¬ Generic (path t)}.Finite ∧
        (∀ t, ¬ Generic (path t) → ∃ g : WallGerm (n + 1),
          g.center = path t ∧
          (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Icc (0 : ℝ) 1,
            g.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
          g.Simple ∧
          ((∃ j : ZMod (n + 1), g.FlatAt j ∧ Generic (deleteVertex (path t) j)) ∨
           (∃ M a : ZMod (n + 1), g.VertexEdgeAt M a ∧
              Generic (firstHalf (path t) M a) ∧ Generic (secondHalf (path t) M a) ∧
              firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1) ∨
           (∃ e f k : ZMod (n + 1), g.TripleAt e f k) ∨
           (∃ M a : ZMod (n + 1), g.ExtensionAt M a) ∨
           (∃ i j k : ZMod (n + 1), g.PureCutAt i j k)))
```
(Note: the draft has no `[NeZero n]` binder but uses `deleteVertex`, which needs one; Lean will
require it — the `TransportConclusion` in Appendix A carries `[NeZero n]`. `rotationNumber P = r`
elaborates as `rotationNumber P = (r : ℝ)`.)
**Conjuncts consumed by root independence:** `k` and `hk : (n+1, r) ≠ (4,0) → k = 0`;
`Continuous path`; `path 0 = P`; `path 1 = shift k Z`; `{t | ¬ Generic (path t)}.Finite`; and, at
each nongeneric `t`, the germ `g` with `g.center = path t`, the curve identification
`∀ s, ∃ hs, g.curve s = path ⟨t + s, hs⟩`, and the five-way alternative (including the
genericity of the deletion / halves and the size bounds `firstHalfSize M a < n+1`,
`secondHalfSize M a < n+1`). **Not consumed:** `∀ t, Regular (path t)`, the affine-mesh clause,
`g.Simple`. thm:mycyclic (`MycyclicTheorem.lean:21–55`, `SM.mycyclic (ha : Admissible n r) : MycyclicData n r`)
is consumed only inside lem:transport.

### 2.11 Anchors, fibres, soft-edge label
`Anchors.lean`: `SoftAnchorData` (`:40`), `ZeroAnchor m r extends SoftAnchorData m` with
`parent_rotation : rotationNumber parent = (r : ℝ)`, `mixed : softAttachmentMinus … ≠ softAttachmentPlus …` (`:76`);
```lean
theorem anchor_mixed_sector_nonempty (hn : 3 ≤ m) {P : LabelledTuple m} (hP : Generic P)
    (j : ZMod m) :
    ∃ q : Plane, SoftAdmissible P j q ∧
      softAttachmentMinus P j q ≠ softAttachmentPlus P j q          -- Anchors.lean:269
theorem zeroAnchor_of_parent (hn : 3 ≤ m) {r : ℤ} {P : LabelledTuple m} (hP : Generic P)
    (hr : rotationNumber P = (r : ℝ)) (j : ZMod m) :
    ∃ A : ZeroAnchor m r, A.parent = P ∧ A.vertex = j                -- Anchors.lean:298
theorem anchor_cases_exhaustive (n r : ℤ) (ha : Admissible n r) (hn : 4 ≤ n) :
    (Admissible (n - 1) r ∨ (MinimalAdmissible n r ∧ 2 ≤ |r|) ∨ (n, r) = (4, 0)) ∧
    ¬ (Admissible (n - 1) r ∧ (MinimalAdmissible n r ∧ 2 ≤ |r|)) ∧
    ¬ (Admissible (n - 1) r ∧ (n, r) = (4, 0)) ∧
    ¬ ((MinimalAdmissible n r ∧ 2 ≤ |r|) ∧ (n, r) = (4, 0))            -- Anchors.lean:434
```
`FibreExistence.lean:11` `exists_generic_of_admissible {r : ℤ} (ha : Admissible (n : ℤ) r) : ∃ P : LabelledTuple n, Generic P ∧ rotationNumber P = (r : ℝ)`;
`FibreReduction.lean:35` `generic_rotation_admissible (hn : 3 ≤ n) (hP : Generic P) (r : ℤ) (hr : rotationNumber P = (r : ℝ)) : Admissible (n : ℤ) r`;
`RotationNumber.lean:45` `rotationNumber_integer (h : Regular P) : ∃ k : ℤ, rotationNumber P = (k : ℝ)`;
`RegularLocus.lean:38` `generic_regular (hn) (h : Generic P) : Regular P`;
`Admissible.lean:10` `Admissible (n r : ℤ) := 3 ≤ n ∧ 2 * |r| < n ∧ (n, r) ≠ (3, 0)`,
`MinimalAdmissible n r := Admissible n r ∧ ((r ≠ 0 ∧ n = 2 * |r| + 1) ∨ (n, r) = (4, 0))`.
The zero-anchor *structure* is not needed: the plan builds the target directly from
`exists_generic_of_admissible` + `anchor_mixed_sector_nonempty` + `soft_rotation_law` +
`soft_theorem_treeCoefficient` (so `ε` can be chosen below both bounds; the fixed `A.param` of
`zeroAnchor_of_parent` would not allow that).
Soft-edge label: `softOldIndex j j`; `softOldIndex_at_attachment (j) : softOldIndex j j = (((canonicalPosition j).val + 1 : ℕ) : ZMod (n + 1))`
(`SoftInsertionIndices.lean:69`), `canonicalPosition_injective` (`CanonicalTripleSigns.lean:39`),
`softOldIndex_injective (j) : Function.Injective (softOldIndex j)` (`:28`, injective in `k`, not in `j`).
**Injectivity in `j` was missing** — proved in Appendix A as `softOldIndex_diag_injective`
(9 lines: `ZMod.val_natCast`, `Nat.mod_eq_of_lt`, `Fin.ext`), and `exists_softEdge_avoiding (hm : 3 ≤ m) (g h : ZMod (m+1)) : ∃ j : ZMod m, softOldIndex j j ≠ g ∧ softOldIndex j j ≠ h`
(pigeonhole `Finset.card_le_card_of_injOn` against `Finset.card_le_two`).

### 2.12 WallGerm API and side conventions
`WallGerm.lean:13–19`: `structure WallGerm (n) where radius : ℝ; radius_pos : 0 < radius; curve : Set.Ioo (-radius) radius → LabelledTuple n; continuous_curve : Continuous curve; generic_punctured : ∀ t, t.val ≠ 0 → Generic (curve t); nongeneric_center : ¬ Generic (curve ⟨0, _⟩)`.
`abbrev Parameter := Set.Ioo (-g.radius) g.radius`; `abbrev SideParameter := Set.Ioo 0 g.radius`;
`zeroParameter : g.Parameter := ⟨0,_⟩`; `center := g.curve g.zeroParameter`;
`sideTime (positive : Bool) (t : SideParameter) : Parameter := if positive then ⟨t.val,_⟩ else ⟨-t.val,_⟩`;
`sideTuple positive t : GenericTuple n := ⟨g.curve (g.sideTime positive t), g.generic_punctured _ _⟩`;
`sideBase := ⟨radius/2,_⟩`; `sideTime_surjective_punctured`. So **`true` = positive parameters = `P_+`,
`false` = negative = `P_-`** in A-S7 and A-R3E; in A-S3 the sides are named by the sign of `turn (·) j`
(§2.2). Since every parameter `s ≠ 0` is a `sideTime`, the plan works with plain
`s₁ s₂ : w.Parameter`, `s₁.val < 0 < s₂.val`, and the two one-line transports
`WallGerm.sideTuple_true_val (w) (s) (hs : 0 < s.val) : (w.sideTuple true ⟨s.val, hs, s.2.2⟩).val = w.curve s` (rfl) and
`WallGerm.sideTuple_false_val (w) (s) (hs : s.val < 0) : (w.sideTuple false ⟨-s.val, _, _⟩).val = w.curve s`.
Row `def:germ` → `wall_germ_definition` (`GermDefinition.lean:54`), row `def:walls` → `named_walls_definition`
(`NamedWallsDefinition.lean:151`, includes `flat_right`/`flat_left` per point and `contact_sign`).
`Simple g := ∃ kind : WallKind, g.HasWallKind kind` (`WallCenterKinds.lean:56`);
`RegularWallKind` (`RegularWallKinds.lean:8`) splits vertex into bigon/sliding — irrelevant here since
A-S7 takes `VertexEdgeAt`.

## 3. The plan: lemma specifications (all proved in Appendix A)

Conventions: `deltaAt hn g h P : ℤ := if hP : Generic P then A_g(P) − A_h(P) else 0`
(`open Classical`), with `deltaAt_of_generic (hn) (g h) (hP : Generic P) : deltaAt hn g h P = treeCoefficient P hP.1 g hn - treeCoefficient P hP.1 h hn` (`simp [deltaAt, hP]`).
This total function avoids carrying genericity proofs through the topology.

### (A) constancy along a continuous family of generic tuples
```lean
theorem chi_eventually_eq_of_G1 {n} [NeZero n] {X} [TopologicalSpace X] {γ : X → LabelledTuple n}
    (hγ : Continuous γ) {x : X} (hx : G1 (γ x)) :
    ∀ᶠ y in 𝓝 x, ∀ i j k : ZMod n, chi (γ y) i j k = chi (γ x) i j k
-- eventually_all ×3; degenerate triples by simp (chi_repeat_*); otherwise
-- (continuousAt_sign_of_ne_zero (g1_area_ne_zero hx hij hjk hik)).comp
--   (f := fun y => det (γ y j - γ y i) (γ y k - γ y i)) ((continuous_area i j k).comp hγ).continuousAt
-- then hc.eventually_mem ((isOpen_discrete _).mem_nhds rfl).
theorem treeCoefficient_eventually_eq_of_generic (hn : 3 ≤ n) (hγ : Continuous γ) (hx : Generic (γ x)) (g) :
    ∀ᶠ y in 𝓝 x, ∃ hy : Generic (γ y), treeCoefficient (γ y) hy.1 g hn = treeCoefficient (γ x) hx.1 g hn
-- filter_upwards [hγ.continuousAt.eventually (generic_persists hn hx), chi_eventually_eq_of_G1 hγ hx.1];
-- treeCoefficient_eq_of_chi.
theorem deltaAt_eventually_eq (hn) (g h) (hγ) (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, deltaAt hn g h (γ y) = deltaAt hn g h (γ x)
```
Rests on: `generic_persists`, `continuous_area`, `g1_area_ne_zero`, `treeCoefficient_eq_of_chi`
(= the content of prop:A-chamber; `A_chamber` itself is not invoked).

### (B) zero-jump lemmas at each wall type (given the IH at smaller arities)
```lean
-- (B-F) flat, arity n+1, IH at the deletion (arity n)
theorem flat_wall_deltaAt_eq {n} [NeZero n] (hn : 3 ≤ n) (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.FlatAt j) (hQ : Generic (deleteVertex w.center j))
    (IH : ∀ a b : ZMod n, treeCoefficient (deleteVertex w.center j) hQ.1 a hn =
      treeCoefficient (deleteVertex w.center j) hQ.1 b hn)
    (g h : ZMod (n + 1)) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt (by omega) g h (w.curve s₂) = deltaAt (by omega) g h (w.curve s₁)
-- proof: hlaw := (w.flat_law_treeCoefficient j hf).2.2; obtain ⟨b, ⟨hR, hL⟩, -⟩ := w.flat_named_sides hf;
-- cases b; turn values at s₂ (via sideTuple_true_val) and s₁ (via sideTuple_false_val);
-- eg := hlaw g sRight sLeft …, eh := hlaw h …; hIH := IH (deletionRoot j g) (deletionRoot j h); linarith.
-- NB: after `cases b`, coerce `hL : w.FlatLeftSide j !true` with `have hL' : w.FlatLeftSide j false := hL`.

-- (B-V) vertex–edge, arity n, IH at both halves
theorem vertexEdge_wall_deltaAt_eq {n} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a)
    (IH1 : ∀ x y : ZMod (firstHalfSize M a),
      treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) x (contactHalfSizes_bounds hn hc.1).1.1 =
      treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) y (contactHalfSizes_bounds hn hc.1).1.1)
    (IH2 : ∀ x y : ZMod (secondHalfSize M a), … secondHalf … (g1_secondHalf hn hc.1 hc.2.1) … .2.1 …)
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁)
-- proof: hlaw := (w.vertex_edge_law_treeCoefficient M a hn hc).2.2.2.2; t := ⟨s₂.val,…⟩, s := ⟨-s₁.val,…⟩;
-- eg := hlaw g s t; eh := hlaw h s t; rw [IH1 (halfRoots M a g).1 (halfRoots M a h).1, IH2 … .2 …] at eg;
-- four treeCoefficient_congr_tuple transports (sideTuple → curve); deltaAt_of_generic; linarith.

-- (B-TEC) triple / extension / cut: no IH
theorem silent_wall_deltaAt_eq {n} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n)
    (hw : (∃ e f k, w.TripleAt e f k) ∨ (∃ M a, w.ExtensionAt M a) ∨ (∃ i j k, w.PureCutAt i j k))
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁)
-- proof: obtain ⟨T, E, C⟩ := WallGerm.triple_and_silent_laws_treeCoefficient (n := n) hn;
-- key x : A_x(sideTuple true t) = A_x(sideTuple false s) by (T w e f k hT x s t).2.2 / E … / C …; transport; linarith.
```

### (C) telescoping along the path
```lean
theorem eq_of_locallyConstant_off_finite {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [T1Space X] [Nonempty Y]
    (f : X → Y) (S : Set X) (hS : S.Finite)
    (hoff : ∀ x ∉ S, ∀ᶠ y in 𝓝 x, f y = f x)
    (hon : ∀ x ∈ S, ∃ c, ∀ᶠ y in 𝓝[≠] x, f y = c)
    {a b : X} (ha : a ∉ S) (hb : b ∉ S) : f a = f b
-- Mathlib: choose! c hc using hon; F x := if x ∈ S then c x else f x; IsLocallyConstant F via
-- IsLocallyConstant.iff_eventually_eq (at x ∈ S use eventually_nhdsWithin_iff and
-- (hS.subset Set.sdiff_subset).isClosed.isOpen_compl.mem_nhds; at x ∉ S use hS.isClosed);
-- IsLocallyConstant.apply_eq_of_preconnectedSpace. Needs `import Mathlib.Topology.LocallyConstant.Basic`
-- (NOT in the SM import closure). `unitInterval` has `ConnectedSpace`/`PreconnectedSpace` instances.

theorem deltaAt_const_along_path {n} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    (path : unitInterval → LabelledTuple n) (hcont : Continuous path)
    (hfin : {t : unitInterval | ¬ Generic (path t)}.Finite)
    (hwall : ∀ t, ¬ Generic (path t) → ∃ w : WallGerm n,
        (∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1, w.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        ∀ s₁ s₂ : w.Parameter, s₁.val < 0 → 0 < s₂.val →
          deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁))
    (h0 : Generic (path 0)) (h1 : Generic (path 1)) :
    deltaAt hn g h (path 0) = deltaAt hn g h (path 1)
-- hoff from deltaAt_eventually_eq; hon: c := deltaAt … (w.curve ⟨radius/2,_⟩); Metric.eventually_nhds_iff with
-- ε := w.radius, Subtype.dist_eq/Real.dist_eq, s := ⟨u - t, abs_lt.mp _⟩, path u = w.curve s (as in
-- WallGerm.isolates_shifted_path, RelativeGeneralPosition.lean:11), then hjump with a fixed negative parameter.
```
(Sorting the finite set is unnecessary; no `Finset.sort` anywhere.)

### (C') consuming the transport conclusion
```lean
def TransportConclusion {n} [NeZero n] (r : ℤ) (P Z : LabelledTuple (n + 1)) : Prop := <the draft's ∃ k … verbatim>
def RootIndepBelow (N : ℕ) : Prop :=
  ∀ k < N, ∀ [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (hQ : Generic Q) (a b : ZMod k),
    treeCoefficient Q hQ.1 a hk = treeCoefficient Q hQ.1 b hk
theorem deltaAt_eq_target_of_transport {m} [NeZero m] (hm : 3 ≤ m) (IH : RootIndepBelow (m + 1))
    {r : ℤ} {P Z : LabelledTuple (m + 1)} (hP : Generic P) (hZ : Generic Z)
    (htr : TransportConclusion r P Z) (g h : ZMod (m + 1)) :
    ∃ k : ZMod (m + 1), ((((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      deltaAt (by omega) g h P = deltaAt (by omega) g h (shift k Z)
-- destructure htr; rw [← h0, ← h1]; deltaAt_const_along_path; at each wall rcases the five alternatives:
-- F: rewrite hcenter into Generic (deleteVertex w.center j), IH m; V: IH at firstHalfSize/secondHalfSize
-- (bounds hlt1 hlt2 from the conjunct, 3 ≤ from contactHalfSizes_bounds); T/E/C: silent_wall_deltaAt_eq.
```

### (D) target evaluations
```lean
-- (D1) zero anchor (case Z): built directly, not through ZeroAnchor
theorem exists_zero_target {m} [NeZero m] (hm : 3 ≤ m) {r : ℤ} (hZ : Admissible (m : ℤ) r) (g h : ZMod (m + 1)) :
    ∃ Z : LabelledTuple (m + 1), ∃ hZg : Generic Z, rotationNumber Z = (r : ℝ) ∧
      treeCoefficient Z hZg.1 g (by omega) = 0 ∧ treeCoefficient Z hZg.1 h (by omega) = 0
-- exists_generic_of_admissible hZ → P; exists_softEdge_avoiding hm g h → j; anchor_mixed_sector_nonempty → q;
-- soft_rotation_law → ε₀; soft_theorem_treeCoefficient hm hP j q hq ε₀ hε₀ → ε₁ ≤ ε₀; ε := ε₁/2;
-- rotation: (hrot _ _ _).2.1 (Or.inr hmixed); zeros: obtain ⟨g', ⟨-, -, -, hzero, -⟩, -⟩ := hroots g (Ne.symm hjg); hzero hmixed.

-- (D2) stars, |r| ≥ 2 (in fact any r ≥ 1)
theorem star_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g h : ZMod (2 * r + 1)) :
    treeCoefficient (star r) hK g (by omega) = treeCoefficient (star r) hK h (by omega)
-- step: A_{g+1}(K) = A_g(σK) (treeCoefficient_shift_one, reversed) = A_g(R∘K) (treeCoefficient_congr_tuple with
-- (star_generic_law hr).1.2.1.1) = A_g(K) (treeCoefficient_rotationMap); then ∀ k : ℕ, A_{↑k} = A_0 by induction,
-- and g = ((g.val : ℕ) : ZMod _) (ZMod.natCast_zmod_val).
theorem starNeg_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g h : ZMod (2 * r + 1)) :
    treeCoefficient (starNeg r) (g1_reversal_forward hK) g (by omega) =
      treeCoefficient (starNeg r) (g1_reversal_forward hK) h (by omega)
-- treeCoefficient_reversal (star r) hK (1 - g), (1 - h); simp only [sub_sub_cancel]; star_treeCoefficient_const.
-- ((-1)^(2r+1) is a common factor; no need to evaluate it.)

-- (D3) bow-tie
theorem bowTie_deltaAt_zero (g h k : ZMod 4) : deltaAt (by norm_num) g h (shift k bowTie) = 0
-- (generic_shift k bowTie).mpr bowTie_generic; A_small_values_ii k g / k h; simp.
```

### (E) strong induction wrapper and final statement
```lean
abbrev RootIndepAt (n : ℕ) : Prop :=
  ∀ [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n),
    treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn
theorem root_independence_of_transport (transport : ∀ {n} [NeZero n], 3 ≤ n + 1 → ∀ {r : ℤ} {P Z : LabelledTuple (n + 1)},
      Generic P → Generic Z → rotationNumber P = r → rotationNumber Z = r → TransportConclusion r P Z) :
    ∀ n : ℕ, RootIndepAt n
-- induction n using Nat.strong_induction_on; n = 3: A_small_values_lemma.1; else n = m+1, hm : 3 ≤ m,
-- r from rotationNumber_integer (generic_regular hn hP), hadm := generic_rotation_admissible;
-- suffices deltaAt hn g h P = 0 (deltaAt_of_generic, sub_eq_zero);
-- anchor_cases_exhaustive ((m+1 : ℕ) : ℤ) r hadm (by push_cast; omega):
--  (Z) cast ((m+1:ℕ):ℤ) - 1 = m; exists_zero_target; deltaAt_eq_target_of_transport; k = 0 from exclusivity hex2;
--  (L) r ≠ 0; m+1 = 2|r|+1 from hL.2; split sign; obtain r' : ℕ with m = 2 r' ∧ (r' : ℤ) = ±r (Int.toNat_of_nonneg, omega);
--      subst; Z = star r' / starNeg r'; rotation from star_generic_law; k = 0 from hex3; (D2);
--  (4,0) m = 3, r = 0 by congrArg Prod.fst/snd; Z = bowTie, bowTie_rotation; (D3) for the k returned.
theorem root_independence (transport : <same>) (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
    (hP : Generic P) (g h : ZMod n) : treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn
```
The exact `treeCoefficient` signature (checked): `treeCoefficient : {n : ℕ} → [NeZero n] → (P : LabelledTuple n) → G1 P → ZMod n → 3 ≤ n → ℤ`; the theorem passes `hP.1 : G1 P` and `hn : 3 ≤ n`, as requested.

## 4. Gaps

| # | needed fact | status | difficulty |
|---|---|---|---|
| G1 | **lem:transport** (`SM.transport_lemma`, draft statement fixed; proof by other agents from `mycyclic` + `relative_general_position` + `children`) | **open** — the only real gap | hard (assembly of three accepted/implemented results; see `work/drafts/TransportLemma_statement.lean` header) |
| G2 | `[NeZero n]` missing in the draft statement's binders (needed by `deleteVertex`); `TransportConclusion` in Appendix A includes it | trivial fix when the draft is finalised | trivial |
| G3 | rotation invariance `det_rotationMap`, `chi_rotationMap`, `g1_rotationMap`, `treeCoefficient_rotationMap` | proved in Appendix A | easy (done) |
| G4 | `softOldIndex_diag_injective`, `exists_softEdge_avoiding` (soft-edge label avoiding two labels) | proved in Appendix A | easy (done) |
| G5 | `eq_of_locallyConstant_off_finite` (real-analysis telescoping; Mathlib `IsLocallyConstant`, needs the extra import) | proved in Appendix A | easy (done) |
| G6 | pointwise version of prop:A-chamber (`chi_eventually_eq_of_G1`, `treeCoefficient_eventually_eq_of_generic`) | proved in Appendix A | easy (done) |
| G7 | star/bow-tie target evaluations (D2, D3) and the zero-anchor target (D1) | proved in Appendix A | easy (done) |
| G8 | row bookkeeping: `thm:root-indep-proof` row currently `declaration ""`, `status pending`; propose `SM.root_independence` in module `SM.RootIndependence` once unconditional | admin | — |

Nothing in the plan requires changes to accepted modules; nothing uses `A_chamber`'s chamber
clauses, `ZeroAnchor`, `anchors_exist`, `Simple`, the affine-mesh clause or `Regular (path t)`.

## 5. Integration checklist for the prover who lands it

1. Create `work/lean/SM/RootIndependence.lean` = Appendix A (drop the `_DRAFT`/`FINAL_shape` test
   items; keep the header). Imports needed: `Mathlib.Topology.LocallyConstant.Basic`,
   `SM.TreeChamber`, `SM.FlatLawTree`, `SM.VertexEdgeLawTree`, `SM.TripleSilentLawsTree`,
   `SM.SoftTheoremTree`, `SM.SoftRotationLaw`, `SM.ReversalShiftLaw`, `SM.StarGenericLaw`,
   `SM.SmallValuesLemma`, `SM.Anchors`, `SM.FibreExistence`, `SM.RelativeGeneralPosition`
   (for `uniformMeshCell`, `WallGerm` kinds), `SM.Children` (harmless), `SM.GermTreeEquality`
   (only for `treeCoefficient_congr_tuple` via `IncidentFlatGapTuples`; alternatively import
   `SM.IncidentFlatGapTuples` directly). Add `import SM.RootIndependence` to `Supplemental.lean`.
2. When `SM.transport_lemma` exists (module e.g. `SM.TransportLemma`), add
   ```lean
   theorem root_independence_unconditional (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n)
       (hP : Generic P) (g h : ZMod n) : treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn :=
     root_independence @transport_lemma n hn P hP g h
   ```
   (verified shape; do not use an explicit lambda). Optionally rename so the unconditional one is
   `SM.root_independence` for the row.
3. Deprecation-linter cosmetics in the draft (harmless): `Set.diff_subset` → `Set.sdiff_subset`,
   `if_neg/if_pos` → `ite_eq_right/ite_eq_left`, `haveI` → `have` at line ~431.
4. Review notes for the reviewer: the proof uses exactly the printed strategy; the source's "two
   root-specific soft bounds" are one bound in Lean (`soft_theorem_treeCoefficient` covers all
   non-soft roots); "cyclic covariance covers every shift" is not needed because `k = 0` in cases
   (Z) and (L) and `A_small_values_ii` already covers every shift in case (4,0).

## Appendix A — the verified draft (`/tmp/ri_test4.lean`, compiled 2026-09-13 with `lake env lean`, 0 `sorry`, axioms `propext, Classical.choice, Quot.sound`; interface test `/tmp/ri_test6.lean`)

```lean
import Mathlib.Topology.LocallyConstant.Basic
import SM.TreeChamber
import SM.FlatLawTree
import SM.VertexEdgeLawTree
import SM.TripleSilentLawsTree
import SM.SoftTheoremTree
import SM.SoftRotationLaw
import SM.ReversalShiftLaw
import SM.StarGenericLaw
import SM.SmallValuesLemma
import SM.MycyclicTheorem
import SM.RelativeGeneralPosition
import SM.Children
import SM.Anchors
import SM.FibreExistence
import SM.GenericCurveChamber
import SM.GermTreeEquality

open Filter Topology

namespace SM

/-! ### (C0) locally constant off a finite set -/
theorem eq_of_locallyConstant_off_finite {X Y : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] [T1Space X] [Nonempty Y]
    (f : X → Y) (S : Set X) (hS : S.Finite)
    (hoff : ∀ x ∉ S, ∀ᶠ y in 𝓝 x, f y = f x)
    (hon : ∀ x ∈ S, ∃ c, ∀ᶠ y in 𝓝[≠] x, f y = c)
    {a b : X} (ha : a ∉ S) (hb : b ∉ S) : f a = f b := by
  classical
  choose! c hc using hon
  let F : X → Y := fun x => if x ∈ S then c x else f x
  have hF : IsLocallyConstant F := by
    rw [IsLocallyConstant.iff_eventually_eq]
    intro x
    by_cases hx : x ∈ S
    · have h1 : ∀ᶠ y in 𝓝 x, y ≠ x → f y = c x := eventually_nhdsWithin_iff.mp (hc x hx)
      have h2 : ∀ᶠ y in 𝓝 x, y ∉ S \ {x} :=
        (hS.subset Set.diff_subset).isClosed.isOpen_compl.mem_nhds (by simp)
      filter_upwards [h1, h2] with y hy1 hy2
      by_cases hyx : y = x
      · rw [hyx]
      · have hyS : y ∉ S := fun hyS => hy2 ⟨hyS, hyx⟩
        simp only [F, if_neg hyS, if_pos hx]
        exact hy1 hyx
    · have h1 := hoff x hx
      have h2 : ∀ᶠ y in 𝓝 x, y ∉ S := hS.isClosed.isOpen_compl.mem_nhds hx
      filter_upwards [h1, h2] with y hy1 hy2
      simp only [F, if_neg hy2, if_neg hx]
      exact hy1
  have := hF.apply_eq_of_preconnectedSpace a b
  simpa [F, ha, hb] using this

/-! ### (A) eventual constancy of chi and of A_g at a generic point of a continuous family -/
theorem chi_eventually_eq_of_G1 {n : ℕ} [NeZero n] {X : Type*} [TopologicalSpace X]
    {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X} (hx : G1 (γ x)) :
    ∀ᶠ y in 𝓝 x, ∀ i j k : ZMod n, chi (γ y) i j k = chi (γ x) i j k := by
  refine eventually_all.mpr fun i => eventually_all.mpr fun j => eventually_all.mpr fun k => ?_
  by_cases hij : i = j
  · subst hij; simp
  by_cases hjk : j = k
  · subst hjk; simp
  by_cases hik : i = k
  · subst hik; simp
  have hne := g1_area_ne_zero hx hij hjk hik
  have hc : ContinuousAt (fun y => chi (γ y) i j k) x :=
    (continuousAt_sign_of_ne_zero hne).comp
      (f := fun y => det (γ y j - γ y i) (γ y k - γ y i))
      ((continuous_area i j k).comp hγ).continuousAt
  have hopen : IsOpen ({chi (γ x) i j k} : Set SignType) := isOpen_discrete _
  exact (hc.eventually_mem (hopen.mem_nhds rfl)).mono fun y hy => hy

theorem treeCoefficient_eventually_eq_of_generic {n : ℕ} [NeZero n] (hn : 3 ≤ n) {X : Type*}
    [TopologicalSpace X] {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X}
    (hx : Generic (γ x)) (g : ZMod n) :
    ∀ᶠ y in 𝓝 x, ∃ hy : Generic (γ y),
      treeCoefficient (γ y) hy.1 g hn = treeCoefficient (γ x) hx.1 g hn := by
  have h1 : ∀ᶠ y in 𝓝 x, Generic (γ y) := hγ.continuousAt.eventually (generic_persists hn hx)
  filter_upwards [h1, chi_eventually_eq_of_G1 hγ hx.1] with y hy hchi
  exact ⟨hy, treeCoefficient_eq_of_chi hy.1 hx.1 hchi g hn⟩

/-! ### Δ_gh as a total function -/
open Classical in
noncomputable def deltaAt {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    (P : LabelledTuple n) : ℤ :=
  if hP : Generic P then treeCoefficient P hP.1 g hn - treeCoefficient P hP.1 h hn else 0

theorem deltaAt_of_generic {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    {P : LabelledTuple n} (hP : Generic P) :
    deltaAt hn g h P = treeCoefficient P hP.1 g hn - treeCoefficient P hP.1 h hn := by
  simp [deltaAt, hP]

theorem deltaAt_eventually_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n) {X : Type*}
    [TopologicalSpace X] {γ : X → LabelledTuple n} (hγ : Continuous γ) {x : X}
    (hx : Generic (γ x)) :
    ∀ᶠ y in 𝓝 x, deltaAt hn g h (γ y) = deltaAt hn g h (γ x) := by
  filter_upwards [treeCoefficient_eventually_eq_of_generic hn hγ hx g,
    treeCoefficient_eventually_eq_of_generic hn hγ hx h] with y hyg hyh
  obtain ⟨hy, hg⟩ := hyg
  obtain ⟨_, hh⟩ := hyh
  rw [deltaAt_of_generic hn g h hy, deltaAt_of_generic hn g h hx, hg, hh]

/-! ### side-parameter transport helpers -/
theorem WallGerm.sideTuple_true_val {n : ℕ} (w : WallGerm n) (s : w.Parameter) (hs : 0 < s.val) :
    (w.sideTuple true ⟨s.val, hs, s.property.2⟩).val = w.curve s := rfl

theorem WallGerm.sideTuple_false_val {n : ℕ} (w : WallGerm n) (s : w.Parameter) (hs : s.val < 0) :
    (w.sideTuple false ⟨-s.val, by linarith, by linarith [s.property.1]⟩).val = w.curve s := by
  show w.curve (w.sideTime false _) = w.curve s
  congr 1
  apply Subtype.ext
  simp [WallGerm.sideTime]

/-! ### (C) constancy of Δ along a path with finitely many zero-jump walls -/
theorem deltaAt_const_along_path {n : ℕ} [NeZero n] (hn : 3 ≤ n) (g h : ZMod n)
    (path : unitInterval → LabelledTuple n) (hcont : Continuous path)
    (hfin : {t : unitInterval | ¬ Generic (path t)}.Finite)
    (hwall : ∀ t, ¬ Generic (path t) → ∃ w : WallGerm n,
        (∀ s : w.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1,
          w.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        ∀ s₁ s₂ : w.Parameter, s₁.val < 0 → 0 < s₂.val →
          deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁))
    (h0 : Generic (path 0)) (h1 : Generic (path 1)) :
    deltaAt hn g h (path 0) = deltaAt hn g h (path 1) := by
  refine eq_of_locallyConstant_off_finite (fun t => deltaAt hn g h (path t))
    {t : unitInterval | ¬ Generic (path t)} hfin ?_ ?_ (by simpa using h0) (by simpa using h1)
  · intro t ht
    have hgen : Generic (path t) := by simpa using ht
    exact deltaAt_eventually_eq hn g h hcont hgen
  · intro t ht
    obtain ⟨w, hcurve, hjump⟩ := hwall t ht
    let sPlus : w.Parameter := ⟨w.radius / 2, by constructor <;> linarith [w.radius_pos]⟩
    let sMinus : w.Parameter := ⟨-(w.radius / 2), by constructor <;> linarith [w.radius_pos]⟩
    have hPlus : 0 < sPlus.val := by show 0 < w.radius / 2; linarith [w.radius_pos]
    have hMinus : sMinus.val < 0 := by show -(w.radius / 2) < 0; linarith [w.radius_pos]
    refine ⟨deltaAt hn g h (w.curve sPlus), ?_⟩
    rw [eventually_nhdsWithin_iff, Metric.eventually_nhds_iff]
    refine ⟨w.radius, w.radius_pos, fun u hu hne => ?_⟩
    have hd : |(u : ℝ) - (t : ℝ)| < w.radius := by
      rw [Subtype.dist_eq, Real.dist_eq] at hu; exact hu
    let s : w.Parameter := ⟨(u : ℝ) - (t : ℝ), abs_lt.mp hd⟩
    have hs0 : s.val ≠ 0 := sub_ne_zero.mpr (fun he => hne (Subtype.ext he))
    obtain ⟨hs, he⟩ := hcurve s
    have htu : (⟨(t : ℝ) + s.val, hs⟩ : unitInterval) = u := by
      apply Subtype.ext; show (t : ℝ) + ((u : ℝ) - (t : ℝ)) = u; ring
    rw [htu] at he
    show deltaAt hn g h (path u) = deltaAt hn g h (w.curve sPlus)
    rw [← he]
    rcases lt_or_gt_of_ne hs0 with hneg | hpos
    · rw [hjump s sPlus hneg hPlus]
    · rw [hjump sMinus s hMinus hpos, hjump sMinus sPlus hMinus hPlus]

/-! ### (D2) rotation invariance and the star K_r -/
theorem det_rotationMap (θ : ℝ) (u v : Plane) :
    det (rotationMap θ u) (rotationMap θ v) = det u v := by
  simp only [rotationMap_apply, det]
  linear_combination (u.1 * v.2 - u.2 * v.1) * Real.cos_sq_add_sin_sq θ

theorem chi_rotationMap (θ : ℝ) {n : ℕ} (P : LabelledTuple n) (i j k : ZMod n) :
    chi (rotationMap θ ∘ P) i j k = chi P i j k := by
  simp only [chi, Function.comp, ← map_sub, det_rotationMap]

theorem g1_rotationMap {n : ℕ} (θ : ℝ) {P : LabelledTuple n} (hP : G1 P) :
    G1 (rotationMap θ ∘ P) := by
  intro i j k hij hjk hik
  rw [chi_rotationMap]
  exact hP i j k hij hjk hik

theorem treeCoefficient_rotationMap {n : ℕ} [NeZero n] (θ : ℝ) (P : LabelledTuple n) (hP : G1 P)
    (g : ZMod n) (hn : 3 ≤ n) :
    treeCoefficient (rotationMap θ ∘ P) (g1_rotationMap θ hP) g hn = treeCoefficient P hP g hn :=
  treeCoefficient_eq_of_chi _ _ (fun i j k => chi_rotationMap θ P i j k) g hn

theorem star_treeCoefficient_succ {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g : ZMod (2 * r + 1)) :
    treeCoefficient (star r) hK (g + 1) (by omega) = treeCoefficient (star r) hK g (by omega) := by
  have h1 := treeCoefficient_shift_one (star r) hK g (by omega)
  rw [← h1]
  have hrot := (star_generic_law hr).1.2.1.1
  rw [treeCoefficient_congr_tuple _ _ _ (g1_rotationMap (starAngle r) hK) hrot g (by omega),
    treeCoefficient_rotationMap]

theorem star_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r)) (g h : ZMod (2 * r + 1)) :
    treeCoefficient (star r) hK g (by omega) = treeCoefficient (star r) hK h (by omega) := by
  have key : ∀ k : ℕ, treeCoefficient (star r) hK (k : ZMod (2 * r + 1)) (by omega) =
      treeCoefficient (star r) hK 0 (by omega) := by
    intro k
    induction k with
    | zero => simp
    | succ k ih => rw [Nat.cast_succ, star_treeCoefficient_succ hr hK, ih]
  rw [← ZMod.natCast_zmod_val g, ← ZMod.natCast_zmod_val h, key g.val, key h.val]

theorem starNeg_treeCoefficient_const {r : ℕ} (hr : 1 ≤ r) (hK : G1 (star r))
    (g h : ZMod (2 * r + 1)) :
    treeCoefficient (starNeg r) (g1_reversal_forward hK) g (by omega) =
      treeCoefficient (starNeg r) (g1_reversal_forward hK) h (by omega) := by
  have hg := treeCoefficient_reversal (star r) hK (1 - g) (by omega)
  have hh := treeCoefficient_reversal (star r) hK (1 - h) (by omega)
  simp only [sub_sub_cancel] at hg hh
  show treeCoefficient (reversal (star r)) _ g _ = treeCoefficient (reversal (star r)) _ h _
  rw [hg, hh, star_treeCoefficient_const hr hK (1 - g) (1 - h)]

/-! ### (B-F) flat wall: Δ has zero jump given the IH at the deletion -/
theorem flat_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm (n + 1)) (j : ZMod (n + 1))
    (hf : w.FlatAt j) (hQ : Generic (deleteVertex w.center j))
    (IH : ∀ a b : ZMod n, treeCoefficient (deleteVertex w.center j) hQ.1 a hn =
      treeCoefficient (deleteVertex w.center j) hQ.1 b hn)
    (g h : ZMod (n + 1)) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt (by omega) g h (w.curve s₂) = deltaAt (by omega) g h (w.curve s₁) := by
  have hlaw := (w.flat_law_treeCoefficient j hf).2.2
  obtain ⟨b, ⟨hR, hL⟩, -⟩ := w.flat_named_sides hf
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  rw [deltaAt_of_generic _ g h hg2, deltaAt_of_generic _ g h hg1]
  have hIH := IH (deletionRoot j g) (deletionRoot j h)
  cases b with
  | true =>
    have hL' : w.FlatLeftSide j false := hL
    have ht2 : turn (w.curve s₂) j = -1 := by
      have := hR ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.sideTuple_true_val s₂ h₂] at this
    have ht1 : turn (w.curve s₁) j = 1 := by
      have := hL' ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.sideTuple_false_val s₁ h₁] at this
    have eg := hlaw g s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    have eh := hlaw h s₂ s₁ h₂.ne' h₁.ne ht2 ht1
    linarith
  | false =>
    have hL' : w.FlatLeftSide j true := hL
    have ht1 : turn (w.curve s₁) j = -1 := by
      have := hR ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
      rwa [w.sideTuple_false_val s₁ h₁] at this
    have ht2 : turn (w.curve s₂) j = 1 := by
      have := hL' ⟨s₂.val, h₂, s₂.property.2⟩
      rwa [w.sideTuple_true_val s₂ h₂] at this
    have eg := hlaw g s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    have eh := hlaw h s₁ s₂ h₁.ne h₂.ne' ht1 ht2
    linarith

/-! ### (B-V) vertex–edge wall -/
theorem vertexEdge_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n) (M a : ZMod n)
    (hc : w.VertexEdgeAt M a)
    (IH1 : ∀ x y : ZMod (firstHalfSize M a),
      treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) x
          (contactHalfSizes_bounds hn hc.1).1.1 =
        treeCoefficient (firstHalf w.center M a) (g1_firstHalf hn hc.1 hc.2.1) y
          (contactHalfSizes_bounds hn hc.1).1.1)
    (IH2 : ∀ x y : ZMod (secondHalfSize M a),
      treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1) x
          (contactHalfSizes_bounds hn hc.1).2.1 =
        treeCoefficient (secondHalf w.center M a) (g1_secondHalf hn hc.1 hc.2.1) y
          (contactHalfSizes_bounds hn hc.1).2.1)
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁) := by
  have hlaw := (w.vertex_edge_law_treeCoefficient M a hn hc).2.2.2.2
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.sideTuple_false_val s₁ h₁
  have eg := hlaw g s t
  have eh := hlaw h s t
  rw [IH1 (halfRoots M a g).1 (halfRoots M a h).1, IH2 (halfRoots M a g).2 (halfRoots M a h).2] at eg
  have a2g := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 g hn
  have a1g := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 g hn
  have a2h := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 h hn
  have a1h := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 h hn
  rw [deltaAt_of_generic hn g h hg2, deltaAt_of_generic hn g h hg1]
  linarith

/-! ### (B-TEC) triple / extension / cut walls -/
theorem silent_wall_deltaAt_eq {n : ℕ} [NeZero n] (hn : 3 ≤ n) (w : WallGerm n)
    (hw : (∃ e f k, w.TripleAt e f k) ∨ (∃ M a, w.ExtensionAt M a) ∨ (∃ i j k, w.PureCutAt i j k))
    (g h : ZMod n) (s₁ s₂ : w.Parameter) (h₁ : s₁.val < 0) (h₂ : 0 < s₂.val) :
    deltaAt hn g h (w.curve s₂) = deltaAt hn g h (w.curve s₁) := by
  let t : w.SideParameter := ⟨s₂.val, h₂, s₂.property.2⟩
  let s : w.SideParameter := ⟨-s₁.val, by linarith, by linarith [s₁.property.1]⟩
  have hg2 := w.generic_punctured s₂ h₂.ne'
  have hg1 := w.generic_punctured s₁ h₁.ne
  have e2 : (w.sideTuple true t).val = w.curve s₂ := w.sideTuple_true_val s₂ h₂
  have e1 : (w.sideTuple false s).val = w.curve s₁ := w.sideTuple_false_val s₁ h₁
  have key : ∀ x : ZMod n,
      treeCoefficient (w.sideTuple true t).val (w.sideTuple true t).property.1 x hn =
        treeCoefficient (w.sideTuple false s).val (w.sideTuple false s).property.1 x hn := by
    obtain ⟨T, E, C⟩ := WallGerm.triple_and_silent_laws_treeCoefficient (n := n) hn
    rcases hw with ⟨e, f, k, hT⟩ | ⟨M, a, hE⟩ | ⟨i, j, k, hC⟩
    · exact fun x => (T w e f k hT x s t).2.2
    · exact fun x => E w M a hE x s t
    · exact fun x => C w i j k hC x s t
  have a2g := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 g hn
  have a1g := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 g hn
  have a2h := treeCoefficient_congr_tuple _ _ (w.sideTuple true t).property.1 hg2.1 e2 h hn
  have a1h := treeCoefficient_congr_tuple _ _ (w.sideTuple false s).property.1 hg1.1 e1 h hn
  have kg := key g
  have kh := key h
  rw [deltaAt_of_generic hn g h hg2, deltaAt_of_generic hn g h hg1]
  linarith

/-! ### (D1) zero-anchor target with the soft edge avoiding g and h -/
theorem softOldIndex_diag_injective {n : ℕ} [NeZero n] :
    Function.Injective (fun j : ZMod n => softOldIndex j j) := by
  intro j j' h
  simp only [softOldIndex_at_attachment] at h
  have h' := congrArg ZMod.val h
  rw [ZMod.val_natCast, ZMod.val_natCast,
    Nat.mod_eq_of_lt (by have := (canonicalPosition j).isLt; omega),
    Nat.mod_eq_of_lt (by have := (canonicalPosition j').isLt; omega)] at h'
  exact canonicalPosition_injective (Fin.ext (by omega))

theorem exists_softEdge_avoiding {m : ℕ} [NeZero m] (hm : 3 ≤ m) (g h : ZMod (m + 1)) :
    ∃ j : ZMod m, softOldIndex j j ≠ g ∧ softOldIndex j j ≠ h := by
  classical
  by_contra hcon
  push Not at hcon
  have hmaps : ∀ j : ZMod m, softOldIndex j j ∈ ({g, h} : Finset (ZMod (m + 1))) := by
    intro j
    by_cases hg : softOldIndex j j = g
    · simp [hg]
    · simp [hcon j hg]
  have hcard := Finset.card_le_card_of_injOn (fun j : ZMod m => softOldIndex j j)
    (s := Finset.univ) (t := {g, h}) (fun j _ => hmaps j) (softOldIndex_diag_injective.injOn)
  have h2 : ({g, h} : Finset (ZMod (m + 1))).card ≤ 2 := Finset.card_le_two
  rw [Finset.card_univ, ZMod.card] at hcard
  omega

theorem exists_zero_target {m : ℕ} [NeZero m] (hm : 3 ≤ m) {r : ℤ} (hZ : Admissible (m : ℤ) r)
    (g h : ZMod (m + 1)) :
    ∃ Z : LabelledTuple (m + 1), ∃ hZg : Generic Z, rotationNumber Z = (r : ℝ) ∧
      treeCoefficient Z hZg.1 g (by omega) = 0 ∧ treeCoefficient Z hZg.1 h (by omega) = 0 := by
  obtain ⟨P, hP, hr⟩ := exists_generic_of_admissible hZ
  obtain ⟨j, hjg, hjh⟩ := exists_softEdge_avoiding hm g h
  obtain ⟨q, hq, hmixed⟩ := anchor_mixed_sector_nonempty hm hP j
  obtain ⟨⟨ε₀, hε₀, hrot⟩, -⟩ := soft_rotation_law hm hP j q hq
  obtain ⟨ε₁, hε₁, hle, hsoft⟩ :=
    SoftDuplication.soft_theorem_treeCoefficient hm hP j q hq ε₀ hε₀
  have hε : 0 < ε₁ / 2 := by positivity
  have hε' : ε₁ / 2 < ε₁ := by linarith
  obtain ⟨hQ, hroots⟩ := hsoft (ε₁ / 2) hε hε'
  refine ⟨softInsertion P j q (ε₁ / 2), hQ, ?_, ?_, ?_⟩
  · rw [(hrot (ε₁ / 2) hε (by linarith)).2.1 (Or.inr hmixed), hr]
  · obtain ⟨g', ⟨-, -, -, hzero, -⟩, -⟩ := hroots g (Ne.symm hjg)
    exact hzero hmixed
  · obtain ⟨h', ⟨-, -, -, hzero, -⟩, -⟩ := hroots h (Ne.symm hjh)
    exact hzero hmixed

/-! ### (D3) bow-tie target -/
theorem bowTie_deltaAt_zero (g h k : ZMod 4) :
    deltaAt (by norm_num) g h (shift k bowTie) = 0 := by
  have hgen : Generic (shift k bowTie) := (generic_shift k bowTie).mpr bowTie_generic
  rw [deltaAt_of_generic _ g h hgen, A_small_values_ii k g, A_small_values_ii k h]
  simp

/-! ### The transport conclusion, as a hypothesis (statement of work/drafts/TransportLemma_statement.lean) -/
def TransportConclusion {n : ℕ} [NeZero n] (r : ℤ) (P Z : LabelledTuple (n + 1)) : Prop :=
  ∃ k : ZMod (n + 1), ((((n + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
    ∃ path : unitInterval → LabelledTuple (n + 1),
      Continuous path ∧ path 0 = P ∧ path 1 = shift k Z ∧
      (∀ t, Regular (path t)) ∧
      (∃ (N : ℕ) (hN : 0 < N), ∀ j : Fin N, ∃ a b : LabelledTuple (n + 1),
        ∀ t ∈ uniformMeshCell N hN j, path t = a + (t : ℝ) • b) ∧
      {t : unitInterval | ¬ Generic (path t)}.Finite ∧
      (∀ t, ¬ Generic (path t) → ∃ g : WallGerm (n + 1),
        g.center = path t ∧
        (∀ s : g.Parameter, ∃ hs : (t : ℝ) + s.val ∈ Set.Icc (0 : ℝ) 1,
          g.curve s = path ⟨(t : ℝ) + s.val, hs⟩) ∧
        g.Simple ∧
        ((∃ j : ZMod (n + 1), g.FlatAt j ∧ Generic (deleteVertex (path t) j)) ∨
         (∃ M a : ZMod (n + 1), g.VertexEdgeAt M a ∧
            Generic (firstHalf (path t) M a) ∧ Generic (secondHalf (path t) M a) ∧
            firstHalfSize M a < n + 1 ∧ secondHalfSize M a < n + 1) ∨
         (∃ e f k : ZMod (n + 1), g.TripleAt e f k) ∨
         (∃ M a : ZMod (n + 1), g.ExtensionAt M a) ∨
         (∃ i j k : ZMod (n + 1), g.PureCutAt i j k)))

/-- The induction hypothesis: root independence at every arity below `N`. -/
def RootIndepBelow (N : ℕ) : Prop :=
  ∀ k < N, ∀ [NeZero k] (hk : 3 ≤ k) (Q : LabelledTuple k) (hQ : Generic Q) (a b : ZMod k),
    treeCoefficient Q hQ.1 a hk = treeCoefficient Q hQ.1 b hk

/-! ### (C') Δ is transported from P to the target -/
theorem deltaAt_eq_target_of_transport {m : ℕ} [NeZero m] (hm : 3 ≤ m)
    (IH : RootIndepBelow (m + 1)) {r : ℤ} {P Z : LabelledTuple (m + 1)}
    (hP : Generic P) (hZ : Generic Z) (htr : TransportConclusion r P Z) (g h : ZMod (m + 1)) :
    ∃ k : ZMod (m + 1), ((((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) → k = 0) ∧
      deltaAt (by omega) g h P = deltaAt (by omega) g h (shift k Z) := by
  obtain ⟨k, hk, path, hcont, h0, h1, -, -, hfin, hwall⟩ := htr
  refine ⟨k, hk, ?_⟩
  rw [← h0, ← h1]
  apply deltaAt_const_along_path (by omega) g h path hcont hfin _ (h0 ▸ hP) (h1 ▸ (generic_shift k Z).mpr hZ)
  intro t ht
  obtain ⟨w, hcenter, hcurve, -, halt⟩ := hwall t ht
  refine ⟨w, hcurve, ?_⟩
  intro s₁ s₂ h₁ h₂
  rcases halt with ⟨j, hf, hdel⟩ | ⟨M, a, hc, hfst, hsnd, hlt1, hlt2⟩ | hT | hE | hC
  · have hQ : Generic (deleteVertex w.center j) := by rw [hcenter]; exact hdel
    exact flat_wall_deltaAt_eq hm w j hf hQ (IH m (by omega) hm _ hQ) g h s₁ s₂ h₁ h₂
  · have hfst' : Generic (firstHalf w.center M a) := by rw [hcenter]; exact hfst
    have hsnd' : Generic (secondHalf w.center M a) := by rw [hcenter]; exact hsnd
    have hb := contactHalfSizes_bounds (by omega : 3 ≤ m + 1) hc.1
    exact vertexEdge_wall_deltaAt_eq (by omega) w M a hc
      (fun x y => IH _ hlt1 hb.1.1 _ hfst' x y) (fun x y => IH _ hlt2 hb.2.1 _ hsnd' x y)
      g h s₁ s₂ h₁ h₂
  · exact silent_wall_deltaAt_eq (by omega) w (Or.inl hT) g h s₁ s₂ h₁ h₂
  · exact silent_wall_deltaAt_eq (by omega) w (Or.inr (Or.inl hE)) g h s₁ s₂ h₁ h₂
  · exact silent_wall_deltaAt_eq (by omega) w (Or.inr (Or.inr hC)) g h s₁ s₂ h₁ h₂


/-! ### (E) the strong induction wrapper -/
abbrev RootIndepAt (n : ℕ) : Prop :=
  ∀ [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n),
    treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn

theorem rootIndepBelow_of_forall {N : ℕ} (H : ∀ k < N, RootIndepAt k) : RootIndepBelow N :=
  fun k hk _ hk3 Q hQ a b => H k hk hk3 Q hQ a b

theorem root_independence_of_transport
    (transport : ∀ {n : ℕ} [NeZero n], 3 ≤ n + 1 → ∀ {r : ℤ} {P Z : LabelledTuple (n + 1)},
      Generic P → Generic Z → rotationNumber P = r → rotationNumber Z = r →
      TransportConclusion r P Z) :
    ∀ n : ℕ, RootIndepAt n := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n IH =>
  intro _ hn P hP g h
  by_cases h3 : n = 3
  · subst h3
    obtain ⟨τ, -, -, hτ⟩ := A_small_values_lemma.1 P hP.1
    rw [hτ g, hτ h]
  · obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
    have hm : 3 ≤ m := by omega
    haveI : NeZero m := ⟨by omega⟩
    obtain ⟨r, hr⟩ := rotationNumber_integer (generic_regular hn hP)
    have hadm : Admissible ((m + 1 : ℕ) : ℤ) r := generic_rotation_admissible hn hP r hr
    have hIH : RootIndepBelow (m + 1) := rootIndepBelow_of_forall IH
    suffices hΔ : deltaAt hn g h P = 0 by
      rw [deltaAt_of_generic hn g h hP] at hΔ
      exact sub_eq_zero.mp hΔ
    obtain ⟨hcases, -, hex2, hex3⟩ :=
      anchor_cases_exhaustive ((m + 1 : ℕ) : ℤ) r hadm (by push_cast; omega)
    rcases hcases with hZ | ⟨hL, hr2⟩ | h40
    · -- (Z): zero anchor target
      have hcast : (((m + 1 : ℕ) : ℤ) - 1) = (m : ℤ) := by push_cast; ring
      rw [hcast] at hZ
      obtain ⟨Z, hZg, hrZ, hg0, hh0⟩ := exists_zero_target hm hZ g h
      obtain ⟨k, hk, hΔ⟩ :=
        deltaAt_eq_target_of_transport hm hIH hP hZg (transport hn hP hZg hr hrZ) g h
      have hk0 : k = 0 := hk (fun h40 => hex2 ⟨by rwa [hcast], h40⟩)
      rw [hΔ, hk0, shift_zero, deltaAt_of_generic hn g h hZg, hg0, hh0, sub_zero]
    · -- (L): star target K_r
      have hr0 : r ≠ 0 := by rintro rfl; simp at hr2
      have hmN : ((m + 1 : ℕ) : ℤ) = 2 * |r| + 1 := by
        rcases hL.2 with ⟨-, h⟩ | h
        · exact h
        · exact absurd (congrArg Prod.snd h) hr0
      have hne40 : (((m + 1 : ℕ) : ℤ), r) ≠ (4, 0) := fun h40 => hex3 ⟨⟨hL, hr2⟩, h40⟩
      push_cast at hmN
      rcases lt_or_gt_of_ne hr0 with hneg | hpos
      · rw [abs_of_neg hneg] at hmN
        obtain ⟨r', hm2, hrr⟩ : ∃ r' : ℕ, m = 2 * r' ∧ (r' : ℤ) = -r :=
          ⟨(-r).toNat, by omega, Int.toNat_of_nonneg (by omega)⟩
        subst hm2
        have hr1 : 1 ≤ r' := by omega
        have hK : G1 (star r') := (star_generic_law hr1).1.2.2.2.1.1
        have hZg : Generic (starNeg r') := (star_generic_law hr1).1.2.2.2.2.1
        have hrZ : rotationNumber (starNeg r') = (r : ℝ) := by
          rw [(star_generic_law hr1).1.2.2.2.2.2.2]
          have : (r : ℝ) = -((r' : ℤ) : ℝ) := by rw [hrr]; push_cast; ring
          rw [this]; simp
        obtain ⟨k, hk, hΔ⟩ :=
          deltaAt_eq_target_of_transport hm hIH hP hZg (transport hn hP hZg hr hrZ) g h
        rw [hΔ, hk hne40, shift_zero, deltaAt_of_generic hn g h hZg]
        exact sub_eq_zero.mpr (starNeg_treeCoefficient_const hr1 hK g h)
      · rw [abs_of_pos hpos] at hmN
        obtain ⟨r', hm2, hrr⟩ : ∃ r' : ℕ, m = 2 * r' ∧ (r' : ℤ) = r :=
          ⟨r.toNat, by omega, Int.toNat_of_nonneg hpos.le⟩
        subst hm2
        have hr1 : 1 ≤ r' := by omega
        have hZg : Generic (star r') := (star_generic_law hr1).1.2.2.2.1
        have hrZ : rotationNumber (star r') = (r : ℝ) := by
          rw [(star_generic_law hr1).1.2.1.2.2.2.2, ← hrr]; simp
        obtain ⟨k, hk, hΔ⟩ :=
          deltaAt_eq_target_of_transport hm hIH hP hZg (transport hn hP hZg hr hrZ) g h
        rw [hΔ, hk hne40, shift_zero, deltaAt_of_generic hn g h hZg]
        exact sub_eq_zero.mpr (star_treeCoefficient_const hr1 hZg.1 g h)
    · -- (4, 0): bow-tie target
      have h1 := congrArg Prod.fst h40
      have h2 := congrArg Prod.snd h40
      simp only at h1 h2
      have hm3 : m = 3 := by omega
      subst hm3
      subst h2
      have hrZ : rotationNumber bowTie = ((0 : ℤ) : ℝ) := by rw [bowTie_rotation]; simp
      obtain ⟨k, -, hΔ⟩ :=
        deltaAt_eq_target_of_transport hm hIH hP bowTie_generic
          (transport hn hP bowTie_generic hr hrZ) g h
      rw [hΔ]
      exact bowTie_deltaAt_zero g h k

/-- The final statement, conditional on `SM.transport_lemma` (work/drafts/TransportLemma_statement.lean). -/
theorem root_independence
    (transport : ∀ {n : ℕ} [NeZero n], 3 ≤ n + 1 → ∀ {r : ℤ} {P Z : LabelledTuple (n + 1)},
      Generic P → Generic Z → rotationNumber P = r → rotationNumber Z = r →
      TransportConclusion r P Z)
    (n : ℕ) [NeZero n] (hn : 3 ≤ n) (P : LabelledTuple n) (hP : Generic P) (g h : ZMod n) :
    treeCoefficient P hP.1 g hn = treeCoefficient P hP.1 h hn :=
  root_independence_of_transport transport n hn P hP g h


end SM
```
