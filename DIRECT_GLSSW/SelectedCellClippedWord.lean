import InteriorEdgeEvents
import CellAnchorInterval
import DirectGLSSW.ExtendedReturnClippedWord

set_option autoImplicit false
namespace DirectGLSSW.SelectedCellClippedWord
open MixedConsecutiveCapWord MixedEdgeSupportOrder ExtendedReturnArcGeometry
open InteriorEdgeEvents ExtendedReturnClippedWord OrderedCapEvents CrossingCapPairing

variable {n : ℕ}

def leftBoundary {α β : Type*} (u : β) (F : α → β) (L : List α)
    (i : Fin (L.length+1)) : β :=
  if hi : i.val = 0 then u else F (L.get ⟨i.val-1, by omega⟩)

def rightBoundary {α β : Type*} (v : β) (F : α → β) (L : List α)
    (i : Fin (L.length+1)) : β :=
  if hi : i.val < L.length then F (L.get ⟨i.val, hi⟩) else v

def returnRank (q : Fin n → PlanarPoint ℝ) (e : Fin n) (z : DirectGLSSW.EdgeChord q e) : ℕ :=
  complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))

/-- All four cell positions have the same consecutive original-anchor interval. -/
theorem cell_anchor_interval (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (i : Fin (L.length+1)) :
    let k := leftBoundary 1 (fun z => returnRank q e z+1) L i
    let l := rightBoundary (n-1) (fun z => returnRank q e z+1) L i
    0 < k ∧ k < l ∧ l < n ∧
    cellInteriorAnchors q hq e L i =
      List.ofFn (fun j : Fin (l-k) => cyclicVertexIndex e (k+j.val)) := by
  classical
  have hn := hq.size_ge_three
  dsimp only
  by_cases hi0 : i.val = 0
  · have hieq : i = ⟨0, by omega⟩ := Fin.ext hi0
    rw [hieq]
    by_cases hlen : 0 < L.length
    · have hr := InteriorEdgeEvents.return_rank_interior q hq e (L.get ⟨0, hlen⟩)
      simp only [List.get_eq_getElem] at hr
      simp only [leftBoundary, rightBoundary, Fin.val_mk, dif_pos rfl, dif_pos hlen]
      refine ⟨by dsimp [returnRank]; omega, by dsimp [returnRank]; omega, by dsimp [returnRank]; omega, ?_⟩
      simpa only [returnRank, Nat.add_sub_cancel] using
        cellInteriorAnchors_first_eq_interval q hq e L hL hlen
    · have he : L = [] := List.length_eq_zero_iff.mp (by omega)
      subst L
      simp only [leftBoundary, rightBoundary, Fin.val_mk, dif_pos rfl, List.length_nil,
        Nat.lt_irrefl, ↓reduceDIte]
      refine ⟨by omega, by omega, by omega, ?_⟩
      have hsub : n-1-1 = n-2 := by omega
      simpa only [hsub] using cellInteriorAnchors_empty_eq_interval q hq e
  · have hip : 0 < i.val := by omega
    by_cases hiL : i.val < L.length
    · have hr := InteriorEdgeEvents.return_rank_interior q hq e (L.get ⟨i.val-1, by omega⟩)
      have hs := InteriorEdgeEvents.return_rank_interior q hq e (L.get ⟨i.val, hiL⟩)
      have hrs := CellAnchorRanks.internal_return_ranks_strict q hq e L hL i hip hiL
      simp only [List.get_eq_getElem] at hr hs hrs
      simp only [leftBoundary, rightBoundary, dif_neg hi0, dif_pos hiL]
      refine ⟨by dsimp [returnRank]; omega, by dsimp [returnRank]; omega, by dsimp [returnRank]; omega, ?_⟩
      simpa only [returnRank, Nat.add_sub_add_right] using
        CellAnchorInterval.cellInteriorAnchors_internal_eq_interval q hq e L hL i hip hiL
    · have hieq : i = Fin.last L.length := Fin.ext (by simp only [Fin.val_last]; omega)
      subst i
      have hlen : 0 < L.length := by simpa only [Fin.val_last] using hip
      have hr := InteriorEdgeEvents.return_rank_interior q hq e (L.get ⟨L.length-1, by omega⟩)
      simp only [List.get_eq_getElem] at hr
      simp only [leftBoundary, rightBoundary, Fin.val_last, dif_neg (ne_of_gt hlen),
        Nat.lt_irrefl, ↓reduceDIte]
      refine ⟨by omega, by dsimp [returnRank]; omega, by omega, ?_⟩
      exact cellInteriorAnchors_terminal_eq_interval q hq e L hL hlen

/-- A slice of the opened polygon is the point-map of its complementary-rank interval. -/
theorem opened_slice (q : Fin n → PlanarPoint ℝ) (e : Fin n) (k l : ℕ)
    (hkl : k ≤ l) (hln : l ≤ n) :
    (((List.ofFn (q ∘ cyclicVertexEquiv e)).drop k).take (l-k)) =
      (List.ofFn (fun j : Fin (l-k) => cyclicVertexIndex e (k+j.val))).map q := by
  have hlen : (((List.ofFn (q ∘ cyclicVertexEquiv e)).drop k).take (l-k)).length = l-k := by
    simp only [List.length_take, List.length_drop, List.length_ofFn]
    omega
  apply List.ext_getElem
  · simp only [hlen, List.length_map, List.length_ofFn]
  · intro j hj hj'
    simp only [List.getElem_take, List.getElem_drop, List.getElem_ofFn, List.getElem_map]
    rfl

theorem cell_point_boundaries (q : Fin n → PlanarPoint ℝ) (e : Fin n)
    (L : List (DirectGLSSW.EdgeChord q e)) (i : Fin (L.length+1)) :
    polygonEventPoint q (cellLeftEvent q e L i) =
      leftBoundary (q (cyclicSuccessor e)) (fun z => crossingPoint q z.val) L i ∧
    polygonEventPoint q (cellRootEvent q e L i) =
      rightBoundary (q e) (fun z => crossingPoint q z.val) L i := by
  constructor
  · unfold cellLeftEvent leftBoundary
    split <;> rfl
  · unfold cellRootEvent rightBoundary
    split <;> rfl

theorem cell_points_horizontal (q : Fin n → PlanarPoint ℝ) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (i : Fin (L.length+1)) :
    (polygonEventPoint q (cellLeftEvent q e L i)).2 = 0 ∧
    (polygonEventPoint q (cellRootEvent q e L i)).2 = 0 := by
  rw [(cell_point_boundaries q e L i).1, (cell_point_boundaries q e L i).2]
  constructor
  · unfold leftBoundary
    split
    · exact hU
    · exact (edgeChord_point_bounds q e hU hV hleft _).1
  · unfold rightBoundary
    split
    · exact (edgeChord_point_bounds q e hU hV hleft _).1
    · exact hV

theorem cell_word_rotate (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e)) (i : Fin (L.length+1)) :
    ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1 =
      polygonEventPoint q (cellLeftEvent q e L i) ::
        ((cellInteriorAnchors q hq e L i).map q ++
          [polygonEventPoint q (cellRootEvent q e L i)]) := by
  simp [cellEventWord, List.map_map, Function.comp_def, polygonEventPoint]

/-- Exact geometric cap word for every selected cell, before selecting its event indices. -/
theorem clipped_cell_word (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (i : Fin (L.length+1)) :
    let A := polygonEventPoint q (cellLeftEvent q e L i)
    let B := polygonEventPoint q (cellRootEvent q e L i)
    let k := leftBoundary 1 (fun z => returnRank q e z+1) L i
    let l := rightBoundary (n-1) (fun z => returnRank q e z+1) L i
    List.ofFn (crossingClippedCapWord (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε)
      (A.1-(q (cyclicSuccessor e)).1) (B.1-(q (cyclicSuccessor e)).1) k l) =
      ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1 := by
  dsimp only
  obtain ⟨hk,hkl,hln,ha⟩ := cell_anchor_interval q hq e L hL i
  have hp := cell_points_horizontal q e hU hV hleft L i
  rw [clipped_list_eq_original_slice hq.size_ge_three (q ∘ cyclicVertexEquiv e)
    (by rw [opened_zero]; exact hU) ε _ _ _ _ hk hkl hln]
  rw [opened_zero, opened_slice q e _ _ (le_of_lt hkl) (le_of_lt hln), ← ha,
    cell_word_rotate]
  have hpa : ((q (cyclicSuccessor e)).1 +
      ((polygonEventPoint q (cellLeftEvent q e L i)).1 - (q (cyclicSuccessor e)).1), 0) =
      polygonEventPoint q (cellLeftEvent q e L i) := by ext <;> simp [hp.1]
  have hpb : ((q (cyclicSuccessor e)).1 +
      ((polygonEventPoint q (cellRootEvent q e L i)).1 - (q (cyclicSuccessor e)).1), 0) =
      polygonEventPoint q (cellRootEvent q e L i) := by ext <;> simp [hp.2]
  rw [hpa,hpb]

/-- Substitute actual endpoint and crossing-event data into the exact cap-word identity.
Only their proved time and pair specifications are used; root injectivity is unnecessary. -/
theorem actual_selected_cell_word (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ (cU cV : EventIndex Q n) (F : DirectGLSSW.EdgeChord q e → EventIndex Q n),
    eventTime Q n cU = 0 →
    eventTime Q n cV = (q e).1-(q (cyclicSuccessor e)).1 →
    eventPair Q n cU = (1,2) → eventPair Q n cV = (n-1,n) →
    (∀ z, eventTime Q n (F z) = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n (F z) = (returnRank q e z+1,returnRank q e z+2)) →
    ∀ (L : List (DirectGLSSW.EdgeChord q e)) (_hL : OrderedEdgeSupport q hq e L)
      (i : Fin (L.length+1)),
    let a := leftBoundary cU F L i
    let b := rightBoundary cV F L i
    List.ofFn (crossingClippedCapWord Q (eventTime Q n a) (eventTime Q n b)
      (eventPair Q n a).1 (eventPair Q n b).1) =
      ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1 := by
  dsimp only
  intro cU cV F htU htV hpU hpV hF L hL i
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  have hta : eventTime Q n (leftBoundary cU F L i) =
      (polygonEventPoint q (cellLeftEvent q e L i)).1-(q (cyclicSuccessor e)).1 := by
    rw [(cell_point_boundaries q e L i).1]
    unfold leftBoundary
    split
    · simpa only [sub_self] using htU
    · exact (hF _).1
  have htb : eventTime Q n (rightBoundary cV F L i) =
      (polygonEventPoint q (cellRootEvent q e L i)).1-(q (cyclicSuccessor e)).1 := by
    rw [(cell_point_boundaries q e L i).2]
    unfold rightBoundary
    split
    · exact (hF _).1
    · exact htV
  have hpa : (eventPair Q n (leftBoundary cU F L i)).1 =
      leftBoundary 1 (fun z => returnRank q e z+1) L i := by
    unfold leftBoundary
    split
    · exact congrArg Prod.fst hpU
    · exact congrArg Prod.fst (hF _).2
  have hpb : (eventPair Q n (rightBoundary cV F L i)).1 =
      rightBoundary (n-1) (fun z => returnRank q e z+1) L i := by
    unfold rightBoundary
    split
    · exact congrArg Prod.fst (hF _).2
    · exact congrArg Prod.fst hpV
  change List.ofFn (crossingClippedCapWord Q
    (eventTime Q n (leftBoundary cU F L i)) (eventTime Q n (rightBoundary cV F L i))
    (eventPair Q n (leftBoundary cU F L i)).1 (eventPair Q n (rightBoundary cV F L i)).1) = _
  rw [hta,htb,hpa,hpb]
  exact clipped_cell_word q hq e hU hV hleft ε L hL i

/-- Original normalized G1--G2 geometry supplies the actual endpoint indices and the
crossing/event equivalence, with the exact clipped-point-word identity for every cell.
This is a list identity, independent of cap genericity and root independence. -/
theorem exists_actual_selected_cell_words (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q)
    (e : Fin n) (hU : (q (cyclicSuccessor e)).2 = 0) (hV : (q e).2 = 0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0 < ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let ℓ := (q e).1-(q (cyclicSuccessor e)).1
    ∃ (cU cV : EventIndex Q n)
      (E : DirectGLSSW.EdgeChord q e ≃
        {c : EventIndex Q n // 0 < eventTime Q n c ∧ eventTime Q n c < ℓ}),
      eventTime Q n cU = 0 ∧ eventTime Q n cV = ℓ ∧
      eventPair Q n cU = (1,2) ∧ eventPair Q n cV = (n-1,n) ∧ cU < cV ∧
      (∀ z, eventTime Q n (E z).val = (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        eventPair Q n (E z).val = (returnRank q e z+1,returnRank q e z+2)) ∧
      (∀ (L : List (DirectGLSSW.EdgeChord q e)) (_hL : OrderedEdgeSupport q hq e L)
        (i : Fin (L.length+1)),
        let a := leftBoundary cU (fun z => (E z).val) L i
        let b := rightBoundary cV (fun z => (E z).val) L i
        List.ofFn (crossingClippedCapWord Q (eventTime Q n a) (eventTime Q n b)
          (eventPair Q n a).1 (eventPair Q n b).1) =
          ((cellEventWord q hq e L i).map (polygonEventPoint q)).rotate 1) := by
  dsimp only
  have hPu : ((q ∘ cyclicVertexEquiv e) (zeroIndex hq.size_ge_three)).2 = 0 := by
    rw [opened_zero]; exact hU
  have hPv : ((q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three)).2 = 0 := by
    rw [opened_last]; exact hV
  have hPl : ((q ∘ cyclicVertexEquiv e) (zeroIndex hq.size_ge_three)).1 <
      ((q ∘ cyclicVertexEquiv e) (lastIndex hq.size_ge_three)).1 := by
    rw [opened_zero,opened_last]; exact hleft
  obtain ⟨cU,cV,htU,htV,hpU,hpV,hord,_⟩ :=
    ExtendedReturnEndpointEvents.endpoint_events hq.size_ge_three (q ∘ cyclicVertexEquiv e)
      (opened_generic q hq e).g1 hPu hPv hPl ε hε
  rw [opened_zero,opened_last] at htV
  obtain ⟨E,hE⟩ := edgeChord_equiv_interior_actual_events q hq e hU hV hleft ε hε
  refine ⟨cU,cV,E,htU,htV,hpU,hpV,hord,hE,?_⟩
  exact actual_selected_cell_word q hq e hU hV hleft ε cU cV (fun z => (E z).val)
    htU htV hpU hpV hE

end DirectGLSSW.SelectedCellClippedWord











