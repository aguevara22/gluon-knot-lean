import DirectGLSSW.EventSegmentGeometry
import DirectGLSSW.SmoothingPermutations
import DirectGLSSW.OrbitNormalization
import DirectGLSSW.FiniteFirstReturn

set_option autoImplicit false

namespace DirectGLSSW.DaughterFirstReturn

open Equiv
open DirectGLSSW.EventSegmentGeometry

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]
variable {n : ℕ} (q : Fin n → PlanarPoint K)
variable (hG2 : cyclicNoTripleIntersections q)
variable (S : Finset (PolygonCrossing q))

noncomputable abbrev DartPerm : Equiv.Perm (PolygonEvent q) :=
  smoothingDartPermutation q hG2 S

def retainedCorner (x : PolygonEvent q) : Prop :=
  match x with
  | .inl _ => True
  | .inr v => v.1 ∈ S

noncomputable def orbitCard (root : PolygonEvent q) : ℕ :=
  Fintype.card
    (PermutationOrbits.Fibre (DartPerm q hG2 S)
      (PermutationOrbits.componentOf (DartPerm q hG2 S) root))

noncomputable abbrev OrbitCoord (root : PolygonEvent q) :=
  Fin (orbitCard q hG2 S root)

noncomputable def orbitEventAt (root : PolygonEvent q)
    (i : OrbitCoord q hG2 S root) : PolygonEvent q :=
  (PermutationOrbits.orbitEnumeration (DartPerm q hG2 S) root i).val

noncomputable abbrev CornerCoord (root : PolygonEvent q) :=
  {i : OrbitCoord q hG2 S root //
    retainedCorner q S (orbitEventAt q hG2 S root i)}

noncomputable instance cornerCoordFintype (root : PolygonEvent q) :
    Fintype (CornerCoord q hG2 S root) := by
  classical
  unfold CornerCoord
  infer_instance

noncomputable def cornerSuccessor (root : PolygonEvent q) :
    Equiv.Perm (CornerCoord q hG2 S root) := by
  classical
  exact orderedCyclicSuccessor (CornerCoord q hG2 S root)

noncomputable def cornerEnumeration (root : PolygonEvent q) :
    Fin (Fintype.card (CornerCoord q hG2 S root)) ≃o
      CornerCoord q hG2 S root := by
  classical
  exact increasingEnumeration (CornerCoord q hG2 S root)

noncomputable def daughterVertex (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) : PlanarPoint K :=
  polygonEventPoint q
    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)

noncomputable def daughterPointList (root : PolygonEvent q) :
    List (PlanarPoint K) :=
  List.ofFn (daughterVertex q hG2 S root)

noncomputable def daughterSideVector (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) : PlanarPoint K :=
  daughterVertex q hG2 S root (cyclicSuccessor i) -
    daughterVertex q hG2 S root i

noncomputable def terminalEvent (z : PolygonEvent q) : PolygonEvent q :=
  polygonEventSuccessor q hG2 z

noncomputable def nextDartStart (z : PolygonEvent q) : PolygonEvent q :=
  smoothingDartPermutation q hG2 S z

noncomputable def cornerGap (root : PolygonEvent q)
    (i j : OrbitCoord q hG2 S root) : ℕ :=
  if i.val < j.val then j.val - i.val
  else orbitCard q hG2 S root - i.val + j.val

noncomputable def lastDartStart (root : PolygonEvent q)
    (c : CornerCoord q hG2 S root) : PolygonEvent q :=
  (DartPerm q hG2 S ^
    (cornerGap q hG2 S root c.val (cornerSuccessor q hG2 S root c).val - 1))
      (orbitEventAt q hG2 S root c.val)

noncomputable def terminalParameterOn (e : Fin n) (w : PolygonEvent q) : K :=
  if polygonEventEdge q w = e then polygonEventParameter q w else 1

noncomputable def daughterSideScale (root : PolygonEvent q)
    (c : CornerCoord q hG2 S root) : K :=
  let x := orbitEventAt q hG2 S root c.val
  let e := polygonEventEdge q x
  let terminal := terminalEvent q hG2
    (lastDartStart q hG2 S root c)
  terminalParameterOn q e terminal - polygonEventParameter q x

theorem pairing_preserves_retained (x : PolygonEvent q) :
    retainedCorner q S (smoothingPairing q S x) ↔ retainedCorner q S x := by
  cases x with
  | inl e => simp [retainedCorner, smoothingPairing_apply, smoothingPairingMap]
  | inr v =>
      rcases v with ⟨c, b⟩
      by_cases hc : c ∈ S
      · cases b <;>
          simp [retainedCorner, smoothingPairing_apply, smoothingPairingMap,
            crossingVisitFlip, hc]
      · cases b <;>
          simp [retainedCorner, smoothingPairing_apply, smoothingPairingMap, hc]

theorem pairing_fixes_noncorner (x : PolygonEvent q)
    (hx : ¬ retainedCorner q S x) : smoothingPairing q S x = x := by
  cases x with
  | inl e => rfl
  | inr v =>
      rcases v with ⟨c, b⟩
      have hv : c ∉ S := by simpa [retainedCorner] using hx
      cases b <;>
        simp [smoothingPairing_apply, smoothingPairingMap, hv]

theorem orbitCard_pos (root : PolygonEvent q) :
    0 < orbitCard q hG2 S root := by
  unfold orbitCard
  exact Fintype.card_pos_iff.mpr inferInstance

theorem cornerEnumeration_zero_eq_rootcoord (root : PolygonEvent q)
    (hroot : retainedCorner q S root)
    (hcard : 0 < Fintype.card (CornerCoord q hG2 S root)) :
    cornerEnumeration q hG2 S root ⟨0, hcard⟩ =
      ⟨⟨0, orbitCard_pos q hG2 S root⟩,
        by simpa [orbitEventAt] using hroot⟩ := by
  classical
  let c₀ : CornerCoord q hG2 S root :=
    ⟨⟨0, orbitCard_pos q hG2 S root⟩,
      by simpa [orbitEventAt] using hroot⟩
  apply le_antisymm
  · have hzero : (⟨0, hcard⟩ : Fin (Fintype.card (CornerCoord q hG2 S root))) ≤
        (cornerEnumeration q hG2 S root).symm c₀ := by
      apply Fin.le_iff_val_le_val.mpr
      exact Nat.zero_le _
    have hle := (cornerEnumeration q hG2 S root).monotone hzero
    simpa [c₀] using hle
  · change (⟨0, orbitCard_pos q hG2 S root⟩ : OrbitCoord q hG2 S root) ≤
      (cornerEnumeration q hG2 S root ⟨0, hcard⟩).val
    exact Fin.le_iff_val_le_val.mpr (Nat.zero_le _)

theorem daughterPointList_head (root : PolygonEvent q)
    (hroot : retainedCorner q S root) :
    (daughterPointList q hG2 S root).head? =
      some (polygonEventPoint q root) := by
  classical
  have hcard : 0 < Fintype.card (CornerCoord q hG2 S root) :=
    Fintype.card_pos_iff.mpr ⟨⟨⟨0, orbitCard_pos q hG2 S root⟩,
      by simpa [orbitEventAt] using hroot⟩⟩
  rw [List.head?_eq_getElem?]
  simp [daughterPointList, daughterVertex, cornerEnumeration_zero_eq_rootcoord,
    orbitEventAt, hroot, hcard]

theorem cornerEnumeration_successor (root : PolygonEvent q)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    cornerEnumeration q hG2 S root (cyclicSuccessor i) =
      cornerSuccessor q hG2 S root (cornerEnumeration q hG2 S root i) := by
  classical
  simp [cornerEnumeration, cornerSuccessor, orderedCyclicSuccessor_apply]

theorem orbitEventAt_cyclicSuccessor (root : PolygonEvent q)
    (i : OrbitCoord q hG2 S root) :
    orbitEventAt q hG2 S root (cyclicSuccessorPerm
      (orbitCard q hG2 S root) i) =
      DartPerm q hG2 S (orbitEventAt q hG2 S root i) := by
  have h := PermutationOrbits.orbitEnumeration_successor
    (DartPerm q hG2 S) root i
  have hv := congrArg Subtype.val h
  simpa [orbitEventAt, PermutationOrbits.fibrePerm_apply_val] using hv

theorem orbitEventAt_iterate (root : PolygonEvent q)
    (i : OrbitCoord q hG2 S root) (k : ℕ) :
    orbitEventAt q hG2 S root
        ((cyclicSuccessorPerm (orbitCard q hG2 S root) ^ k) i) =
      (DartPerm q hG2 S ^ k) (orbitEventAt q hG2 S root i) := by
  induction k with
  | zero => simp
  | succ k ih =>
      calc
        orbitEventAt q hG2 S root
            ((cyclicSuccessorPerm (orbitCard q hG2 S root) ^ (k + 1)) i) =
            orbitEventAt q hG2 S root
              (cyclicSuccessorPerm (orbitCard q hG2 S root)
                ((cyclicSuccessorPerm (orbitCard q hG2 S root) ^ k) i)) := by
                  simp [pow_succ', Equiv.Perm.mul_apply]
        _ = DartPerm q hG2 S
              (orbitEventAt q hG2 S root
                ((cyclicSuccessorPerm (orbitCard q hG2 S root) ^ k) i)) :=
              orbitEventAt_cyclicSuccessor q hG2 S root _
        _ = DartPerm q hG2 S
              ((DartPerm q hG2 S ^ k) (orbitEventAt q hG2 S root i)) :=
              congrArg (DartPerm q hG2 S) ih
        _ = (DartPerm q hG2 S ^ (k + 1)) (orbitEventAt q hG2 S root i) := by
              simp [pow_succ', Equiv.Perm.mul_apply]

theorem everyDartOrbit_hasCorner (hn : 3 ≤ n) (x : PolygonEvent q) :
    ∃ root : PolygonEvent q,
      (DartPerm q hG2 S).SameCycle x root ∧ retainedCorner q S root := by
  classical
  by_contra hnone
  have havoid : ∀ y : PolygonEvent q,
      PermutationOrbits.componentOf (DartPerm q hG2 S) y =
        PermutationOrbits.componentOf (DartPerm q hG2 S) x →
      ¬ retainedCorner q S y := by
    intro y hy hret
    apply hnone
    exact ⟨y, (PermutationOrbits.componentOf_eq_iff _ _ _).mp hy.symm, hret⟩
  have hstep (y : PolygonEvent q)
      (hy : PermutationOrbits.componentOf (DartPerm q hG2 S) y =
        PermutationOrbits.componentOf (DartPerm q hG2 S) x) :
      DartPerm q hG2 S y = polygonEventSuccessor q hG2 y := by
    have hpy := havoid (DartPerm q hG2 S y) (by
      rw [PermutationOrbits.componentOf_apply]
      exact hy)
    have hterminal : ¬ retainedCorner q S (polygonEventSuccessor q hG2 y) := by
      intro ht
      apply hpy
      exact (pairing_preserves_retained q S _).mpr ht
    rw [smoothingDartPermutation_apply, pairing_fixes_noncorner q S _ hterminal]
  have hpow (k : ℕ) :
      (DartPerm q hG2 S ^ k) x = (polygonEventSuccessor q hG2 ^ k) x := by
    induction k with
    | zero => simp
    | succ k ih =>
        calc
          (DartPerm q hG2 S ^ (k + 1)) x =
              DartPerm q hG2 S ((DartPerm q hG2 S ^ k) x) := by
                simp [pow_succ', Equiv.Perm.mul_apply]
          _ = polygonEventSuccessor q hG2 ((DartPerm q hG2 S ^ k) x) :=
                hstep _ (by simp [PermutationOrbits.componentOf_pow_apply])
          _ = polygonEventSuccessor q hG2 ((polygonEventSuccessor q hG2 ^ k) x) :=
                congrArg (polygonEventSuccessor q hG2) ih
          _ = (polygonEventSuccessor q hG2 ^ (k + 1)) x := by
                simp [pow_succ', Equiv.Perm.mul_apply]
  let anchor : PolygonEvent q := Sum.inl ⟨0, by omega⟩
  obtain ⟨i, hi⟩ :=
    (polygonEventSuccessor_oneTraversal q hG2 x).2 anchor
  have hi' : (polygonEventSuccessor q hG2 ^ (i.val + 1)) x = anchor := by
    simpa using hi
  have hEq : (DartPerm q hG2 S ^ (i.val + 1)) x = anchor :=
    (hpow (i.val + 1)).trans hi'
  have hcomponent :
      PermutationOrbits.componentOf (DartPerm q hG2 S) anchor =
        PermutationOrbits.componentOf (DartPerm q hG2 S) x := by
    calc
      PermutationOrbits.componentOf (DartPerm q hG2 S) anchor =
          PermutationOrbits.componentOf (DartPerm q hG2 S)
            ((DartPerm q hG2 S ^ (i.val + 1)) x) := by rw [hEq]
      _ = PermutationOrbits.componentOf (DartPerm q hG2 S) x :=
        PermutationOrbits.componentOf_pow_apply (DartPerm q hG2 S)
          (i.val + 1) x
  exact havoid anchor hcomponent (by simp [retainedCorner, anchor])

theorem cornerSuccessor_is_firstReturn (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (c : CornerCoord q hG2 S root) :
    let d := cornerGap q hG2 S root c.val
      (cornerSuccessor q hG2 S root c).val
    let start := orbitEventAt q hG2 S root c.val
    let z := lastDartStart q hG2 S root c
    let terminal := terminalEvent q hG2 z
    let nextStart := nextDartStart q hG2 S z
    0 < d ∧
    nextStart = orbitEventAt q hG2 S root
      (cornerSuccessor q hG2 S root c).val ∧
    nextStart = smoothingPairing q S terminal ∧
    polygonEventPoint q nextStart = polygonEventPoint q terminal ∧
    retainedCorner q S terminal ∧
    ∀ k : ℕ, 0 < k → k < d →
      ¬ retainedCorner q S ((DartPerm q hG2 S ^ k) start) := by
  classical
  let next := cornerSuccessor q hG2 S root c
  let d := cornerGap q hG2 S root c.val next.val
  let start := orbitEventAt q hG2 S root c.val
  let z := lastDartStart q hG2 S root c
  let terminal := terminalEvent q hG2 z
  let nextStart := nextDartStart q hG2 S z
  let N := orbitCard q hG2 S root
  let P : Fin N → Prop := fun i =>
    retainedCorner q S (orbitEventAt q hG2 S root i)
  have hfr0 := FiniteFirstReturn.orderedSubtype_firstReturn
    (N := N) P c
  have hfr : 0 < d ∧ d ≤ N ∧
      (cyclicSuccessorPerm N ^ d) c.val = next.val ∧
      ∀ k : ℕ, 0 < k → k < d →
        ¬ P ((cyclicSuccessorPerm N ^ k) c.val) := by
    simpa [N, P, d, next, cornerGap, cornerSuccessor,
      FiniteFirstReturn.forwardGap] using hfr0
  rcases hfr with ⟨hdpos, _, hreach, hno⟩
  have hiterate := orbitEventAt_iterate q hG2 S root c.val d
  rw [hreach] at hiterate
  have hstepNext :
      DartPerm q hG2 S z = orbitEventAt q hG2 S root next.val := by
    have hz : z = (DartPerm q hG2 S ^ (d - 1)) start := rfl
    have hpow : DartPerm q hG2 S z =
        (DartPerm q hG2 S ^ d) start := by
      rw [hz]
      calc
        DartPerm q hG2 S ((DartPerm q hG2 S ^ (d - 1)) start) =
            (DartPerm q hG2 S ^ ((d - 1) + 1)) start := by
              simp [pow_succ', Equiv.Perm.mul_apply]
        _ = (DartPerm q hG2 S ^ d) start := by
              rw [Nat.sub_add_cancel hdpos]
    exact hpow.trans hiterate.symm
  have hpair : nextStart = smoothingPairing q S terminal := by
    rfl
  have hpoint : polygonEventPoint q nextStart = polygonEventPoint q terminal := by
    simpa [nextStart, terminal, z] using
      smoothingDartPermutation_endpoint q hG2 S z
  have hretNext : retainedCorner q S nextStart := by
    change retainedCorner q S (DartPerm q hG2 S z)
    rw [hstepNext]
    exact next.property
  have hretTerminal : retainedCorner q S terminal := by
    rw [hpair] at hretNext
    exact (pairing_preserves_retained q S terminal).mp hretNext
  refine ⟨hdpos, ?_, hpair, hpoint, hretTerminal, ?_⟩
  · simpa [nextStart, z, start] using hstepNext
  · intro k hkpos hkd
    have hcoord := hno k hkpos hkd
    change ¬ retainedCorner q S
      (orbitEventAt q hG2 S root
        ((cyclicSuccessorPerm N ^ k) c.val)) at hcoord
    have hiter := orbitEventAt_iterate q hG2 S root c.val k
    intro hcorner
    apply hcoord
    rw [hiter]
    exact hcorner

theorem orbitPrefix_edge_parameter (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (c : CornerCoord q hG2 S root) (k : ℕ)
    (hk : k < cornerGap q hG2 S root c.val
      (cornerSuccessor q hG2 S root c).val) :
    polygonEventEdge q ((DartPerm q hG2 S ^ k)
      (orbitEventAt q hG2 S root c.val)) =
        polygonEventEdge q (orbitEventAt q hG2 S root c.val) ∧
    polygonEventParameter q (orbitEventAt q hG2 S root c.val) ≤
      polygonEventParameter q ((DartPerm q hG2 S ^ k)
        (orbitEventAt q hG2 S root c.val)) := by
  classical
  let d := cornerGap q hG2 S root c.val
    (cornerSuccessor q hG2 S root c).val
  let start := orbitEventAt q hG2 S root c.val
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot c
  rcases hfr with ⟨_, _, _, _, _, hno⟩
  have hprefix : ∀ k : ℕ, k < d →
      polygonEventEdge q ((DartPerm q hG2 S ^ k) start) =
        polygonEventEdge q start ∧
      polygonEventParameter q start ≤
        polygonEventParameter q ((DartPerm q hG2 S ^ k) start) := by
    intro k
    induction k with
    | zero =>
        intro hk
        simp [start]
    | succ k ih =>
        intro hk
        have hklt : k < d := by omega
        have hprev := ih hklt
        let x := (DartPerm q hG2 S ^ k) start
        have hdestNC : ¬ retainedCorner q S (DartPerm q hG2 S x) := by
          have h := hno (k + 1) (by omega) hk
          simpa [x, pow_succ', Equiv.Perm.mul_apply] using h
        have hterminalNC : ¬ retainedCorner q S (polygonEventSuccessor q hG2 x) := by
          intro hterminal
          apply hdestNC
          change retainedCorner q S
            (smoothingPairing q S (polygonEventSuccessor q hG2 x))
          exact (pairing_preserves_retained q S _).mpr hterminal
        have hfix := pairing_fixes_noncorner q S
          (polygonEventSuccessor q hG2 x) hterminalNC
        have hstep : DartPerm q hG2 S x = polygonEventSuccessor q hG2 x := by
          change smoothingPairing q S (polygonEventSuccessor q hG2 x) = _
          exact hfix
        have hclass := polygonEventSuccessor_sameEdge_next_or_nextAnchor
          q hG2 hn x
        have hsame :
            polygonEventEdge q (polygonEventSuccessor q hG2 x) =
              polygonEventEdge q x ∧
            polygonEventParameter q x <
              polygonEventParameter q (polygonEventSuccessor q hG2 x) := by
          rcases hclass with hsame | hnext
          · exact ⟨hsame.1, hsame.2.1⟩
          · exfalso
            apply hterminalNC
            rw [hnext.1]
            exact True.intro
        have hdest : (DartPerm q hG2 S ^ (k + 1)) start =
            polygonEventSuccessor q hG2 x := by
          calc
            (DartPerm q hG2 S ^ (k + 1)) start =
                DartPerm q hG2 S ((DartPerm q hG2 S ^ k) start) := by
                  simp [pow_succ', Equiv.Perm.mul_apply]
            _ = DartPerm q hG2 S x := rfl
            _ = polygonEventSuccessor q hG2 x := hstep
        constructor
        · rw [hdest, hsame.1, hprev.1]
        · rw [hdest]
          exact le_trans hprev.2 (le_of_lt hsame.2)
  simpa [d, start] using hprefix k hk

theorem terminalParameterOn_successor (hn : 3 ≤ n) (x : PolygonEvent q) :
    terminalParameterOn q (polygonEventEdge q x)
      (polygonEventSuccessor q hG2 x) =
    polygonEventSuccessorTerminalParameter q hG2 hn x := by
  rfl

theorem daughterSide_positive_multiple (hn : 3 ≤ n)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    0 < daughterSideScale q hG2 S root
          (cornerEnumeration q hG2 S root i) ∧
    daughterSideVector q hG2 S root i =
      daughterSideScale q hG2 S root (cornerEnumeration q hG2 S root i) •
        cyclicTangent q (polygonEventEdge q
          (orbitEventAt q hG2 S root
            (cornerEnumeration q hG2 S root i).val)) := by
  classical
  let c := cornerEnumeration q hG2 S root i
  let d := cornerGap q hG2 S root c.val
    (cornerSuccessor q hG2 S root c).val
  let start := orbitEventAt q hG2 S root c.val
  let z := lastDartStart q hG2 S root c
  let terminal := terminalEvent q hG2 z
  let nextStart := nextDartStart q hG2 S z
  let e := polygonEventEdge q start
  let u := polygonEventSuccessorTerminalParameter q hG2 hn z
  have hfr := cornerSuccessor_is_firstReturn q hG2 S hn root hroot c
  rcases hfr with ⟨_, hnext, _, hpoint, _, _⟩
  have hlast : d - 1 < d := Nat.sub_lt (by omega) (by omega)
  have hpref := orbitPrefix_edge_parameter q hG2 S hn root hroot c
    (d - 1) hlast
  have hzedge : polygonEventEdge q z = e := by
    simpa [z, start, lastDartStart, e] using hpref.1
  have hzparam : polygonEventParameter q start ≤ polygonEventParameter q z := by
    simpa [z, start, lastDartStart] using hpref.2
  have hparam_lt : polygonEventParameter q z < u := by
    simpa [u] using
      (polygonEventSuccessor_positive_elementary_step q hG2 hn z).1
  have htermParam : terminalParameterOn q e terminal = u := by
    simpa [terminal, terminalEvent, e, u, hzedge] using
      terminalParameterOn_successor q hG2 hn z
  have hscale : daughterSideScale q hG2 S root c =
      u - polygonEventParameter q start := by
    calc
      daughterSideScale q hG2 S root c =
          terminalParameterOn q e terminal - polygonEventParameter q start := by
            simp [daughterSideScale, terminal, terminalEvent, z, start, e]
      _ = u - polygonEventParameter q start := by rw [htermParam]
  have hvertexStep : daughterSideVector q hG2 S root i =
      polygonEventPoint q terminal - polygonEventPoint q start := by
    have hcornerSucc : cornerEnumeration q hG2 S root (cyclicSuccessor i) =
        cornerSuccessor q hG2 S root c := by
      rw [cornerEnumeration_successor]
    change polygonEventPoint q
        (orbitEventAt q hG2 S root
          (cornerEnumeration q hG2 S root (cyclicSuccessor i)).val) -
      polygonEventPoint q
        (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val) = _
    rw [hcornerSucc, ← hnext, hpoint]
  have hpositive := polygonEventSuccessor_positive_elementary_step q hG2 hn z
  dsimp at hpositive
  rcases hpositive with ⟨hlt, _, _, hterminalPoint, _⟩
  have hterminalAffine : polygonEventPoint q terminal =
      affinePoint (q e) (q (cyclicSuccessor e)) u := by
    simpa [terminal, terminalEvent, z, e, u, hzedge] using hterminalPoint
  have hstartAffine : polygonEventPoint q start =
      affinePoint (q e) (q (cyclicSuccessor e))
        (polygonEventParameter q start) := by
    simpa [e] using polygonEventPoint_eq_affine q start
  refine ⟨?_, ?_⟩
  · rw [hscale]
    exact sub_pos.mpr (lt_of_le_of_lt hzparam hparam_lt)
  · rw [hvertexStep, hterminalAffine, hstartAffine, hscale]
    ext <;> simp [affinePoint, cyclicTangent] <;> ring

theorem daughterSide_ne_zero (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (root : PolygonEvent q) (hroot : retainedCorner q S root)
    (i : Fin (Fintype.card (CornerCoord q hG2 S root))) :
    daughterSideVector q hG2 S root i ≠ 0 := by
  rcases daughterSide_positive_multiple q hG2 S hn root hroot i with
    ⟨hscale, hside⟩
  intro hzero
  rw [hside] at hzero
  have hfst := congrArg Prod.fst hzero
  have hsnd := congrArg Prod.snd hzero
  let e := polygonEventEdge q
    (orbitEventAt q hG2 S root (cornerEnumeration q hG2 S root i).val)
  have hfst_mul : daughterSideScale q hG2 S root
      (cornerEnumeration q hG2 S root i) * (cyclicTangent q e).1 = 0 := by
    simpa [smul_eq_mul, e] using hfst
  have hsnd_mul : daughterSideScale q hG2 S root
      (cornerEnumeration q hG2 S root i) * (cyclicTangent q e).2 = 0 := by
    simpa [smul_eq_mul, e] using hsnd
  have htan : cyclicTangent q e = 0 := by
    apply Prod.ext
    · exact (mul_eq_zero.mp hfst_mul).resolve_left (ne_of_gt hscale)
    · exact (mul_eq_zero.mp hsnd_mul).resolve_left (ne_of_gt hscale)
  exact (cyclicTangent_ne_zero hn q hG1 e) htan

end DirectGLSSW.DaughterFirstReturn
