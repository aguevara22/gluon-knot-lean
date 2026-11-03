import DirectGLSSW.OrderedEventSuccessor
import DirectGLSSW.TruncationVisitTransport
import DirectGLSSW.TruncationEdgeOrientation

set_option autoImplicit false

namespace DirectGLSSW.TruncationEventOrder

open DirectGLSSW
open DirectGLSSW.TruncationDirection
open DirectGLSSW.TruncationEdgeLift

noncomputable def truncationPolygonEventMap {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃
      PolygonCrossing (truncateCyclicCorner q a p scale ε)) :
    PolygonEvent q → PolygonEvent (truncateCyclicCorner q a p scale ε)
  | .inl e => .inl (edgeLift a e)
  | .inr v => .inr (crossingVisit_mapEquiv E v)

private theorem truncationPolygonEventMap_edge {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (x : PolygonEvent q) :
    polygonEventEdge (truncateCyclicCorner q a p scale ε)
      (truncationPolygonEventMap q a p scale ε E x) =
        edgeLift a (polygonEventEdge q x) := by
  cases x with
  | inl e => rfl
  | inr v => exact crossingVisit_mapEquiv_edge q a p scale ε E hleft hright v

private theorem truncationPolygonEventMap_parameter_anchor {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p e : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε)) :
    polygonEventParameter (truncateCyclicCorner q a p scale ε)
      (truncationPolygonEventMap q a p scale ε E (Sum.inl e)) = 0 := rfl

private theorem truncationPolygonEventMap_parameter_visit {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (v : CrossingVisit q) :
    oldEdgeParameter a p (crossingVisitEdge q v) ε scale
      (polygonEventParameter (truncateCyclicCorner q a p scale ε)
        (truncationPolygonEventMap q a p scale ε E (Sum.inr v))) =
      crossingVisitParameter q v := by
  exact crossingVisit_parameter_transport hn q a p hp scale ε hε hε1 hscale hscale1
    hq E hleft hright hpoint v

theorem truncationPolygonEventMap_injective {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε)) :
    Function.Injective (truncationPolygonEventMap q a p scale ε E) := by
  intro x y h
  cases x with
  | inl e =>
    cases y with
    | inl f =>
      have he : edgeLift a e = edgeLift a f := Sum.inl.inj h
      exact congrArg Sum.inl (edgeLift_injective a he)
    | inr v => cases h
  | inr v =>
    cases y with
    | inl e => cases h
    | inr w =>
      have hv : crossingVisit_mapEquiv E v = crossingVisit_mapEquiv E w :=
        Sum.inr.inj h
      exact congrArg Sum.inr ((crossingVisit_mapEquiv E).injective hv)

theorem truncationPolygonEventMap_range {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε)) :
    Set.range (truncationPolygonEventMap q a p scale ε E) =
      {y : PolygonEvent (truncateCyclicCorner q a p scale ε) |
        y ≠ Sum.inl a.castSucc} := by
  classical
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    change truncationPolygonEventMap q a p scale ε E x ≠ Sum.inl a.castSucc
    cases x with
    | inl e =>
      change Sum.inl (edgeLift a e) ≠ Sum.inl a.castSucc
      exact fun h => edgeLift_ne_short a e (Sum.inl.inj h)
    | inr v => simp [truncationPolygonEventMap]
  · intro hy
    change y ≠ Sum.inl a.castSucc at hy
    cases y with
    | inl i =>
      have hi : i ≠ a.castSucc := fun h => hy (congrArg Sum.inl h)
      let e := ShortEdgeCyclicAdapter.collapseFin a i
      have hei : edgeLift a e = i := edgeLift_collapseFin a i hi
      exact ⟨Sum.inl e, by simp [truncationPolygonEventMap, e, hei]⟩
    | inr v =>
      let c := (crossingVisit_mapEquiv E).symm v
      exact ⟨Sum.inr c, by simp [truncationPolygonEventMap, c]⟩

theorem truncationPolygonEventMap_order_iff {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) (x y : PolygonEvent q) :
    (letI := polygonEventOrder q hq.g2; x < y) ↔
    (letI := polygonEventOrder (truncateCyclicCorner q a p scale ε) hQ.g2;
      truncationPolygonEventMap q a p scale ε E x <
        truncationPolygonEventMap q a p scale ε E y) := by
  let Q := truncateCyclicCorner q a p scale ε
  let F := truncationPolygonEventMap q a p scale ε E
  have hlt (e f : Fin n) : e < f ↔ edgeLift a e < edgeLift a f :=
    (edgeLift_strictMono a).lt_iff_lt.symm
  cases x with
  | inl e =>
    cases y with
    | inl f =>
      rw [polygonEvent_lt_iff q hq.g2, polygonEvent_lt_iff Q hQ.g2]
      simp [F, truncationPolygonEventMap, polygonEventEdge, polygonEventParameter, hlt]
    | inr v =>
      rw [polygonEvent_lt_iff q hq.g2, polygonEvent_lt_iff Q hQ.g2]
      dsimp [F, truncationPolygonEventMap, polygonEventEdge, polygonEventParameter]
      have hvpos := (crossingVisitParameter_spec q v).1
      have hvposQ := (crossingVisitParameter_spec Q (crossingVisit_mapEquiv E v)).1
      have hedge : polygonEventEdge Q (.inr (crossingVisit_mapEquiv E v)) =
          edgeLift a (crossingVisitEdge q v) :=
        crossingVisit_mapEquiv_edge q a p scale ε E hleft hright v
      have hedge' : crossingVisitEdge Q (crossingVisit_mapEquiv E v) =
          edgeLift a (crossingVisitEdge q v) := by
        simpa [polygonEventEdge] using hedge
      rw [hedge']
      constructor
      · intro h
        rcases h with h | ⟨hEq, _⟩
        · exact Or.inl ((edgeLift_strictMono a) h)
        · subst e
          exact Or.inr ⟨rfl, hvposQ⟩
      · intro h
        rcases h with h | ⟨hEq, _⟩
        · exact Or.inl (hlt e (crossingVisitEdge q v) |>.mpr h)
        · have : e = crossingVisitEdge q v := (edgeLift_injective a hEq)
          subst e
          exact Or.inr ⟨rfl, hvpos⟩
  | inr v =>
    cases y with
    | inl e =>
      rw [polygonEvent_lt_iff q hq.g2, polygonEvent_lt_iff Q hQ.g2]
      dsimp [F, truncationPolygonEventMap, polygonEventEdge, polygonEventParameter]
      have hedge : polygonEventEdge Q (.inr (crossingVisit_mapEquiv E v)) =
          edgeLift a (crossingVisitEdge q v) :=
        crossingVisit_mapEquiv_edge q a p scale ε E hleft hright v
      have hedge' : crossingVisitEdge Q (crossingVisit_mapEquiv E v) =
          edgeLift a (crossingVisitEdge q v) := by
        simpa [polygonEventEdge] using hedge
      rw [hedge']
      constructor
      · intro h
        rcases h with h | ⟨hEq, hpar⟩
        · exact Or.inl ((edgeLift_strictMono a) h)
        · exact False.elim (not_lt_of_ge (le_of_lt (crossingVisitParameter_spec q v).1) hpar)
      · intro h
        rcases h with h | ⟨hEq, hpar⟩
        · exact Or.inl (hlt (crossingVisitEdge q v) e |>.mpr h)
        · have : crossingVisitEdge q v = e := edgeLift_injective a hEq
          subst e
          exact False.elim (not_lt_of_ge
            (le_of_lt (crossingVisitParameter_spec Q (crossingVisit_mapEquiv E v)).1) hpar)
    | inr w =>
      rw [polygonEvent_lt_iff q hq.g2, polygonEvent_lt_iff Q hQ.g2]
      dsimp [F, truncationPolygonEventMap, polygonEventEdge, polygonEventParameter]
      have hedgeV : polygonEventEdge Q (.inr (crossingVisit_mapEquiv E v)) =
          edgeLift a (crossingVisitEdge q v) :=
        crossingVisit_mapEquiv_edge q a p scale ε E hleft hright v
      have hedgeW : polygonEventEdge Q (.inr (crossingVisit_mapEquiv E w)) =
          edgeLift a (crossingVisitEdge q w) :=
        crossingVisit_mapEquiv_edge q a p scale ε E hleft hright w
      have hedgeV' : crossingVisitEdge Q (crossingVisit_mapEquiv E v) =
          edgeLift a (crossingVisitEdge q v) := by
        simpa [polygonEventEdge] using hedgeV
      have hedgeW' : crossingVisitEdge Q (crossingVisit_mapEquiv E w) =
          edgeLift a (crossingVisitEdge q w) := by
        simpa [polygonEventEdge] using hedgeW
      rw [hedgeV', hedgeW']
      by_cases he : crossingVisitEdge q v = crossingVisitEdge q w
      · rw [he]
        simp only [lt_self_iff_false, true_and, false_or]
        have hpv := crossingVisit_parameter_transport hn q a p hp scale ε
          hε hε1 hscale hscale1 hq E hleft hright hpoint v
        have hpw := crossingVisit_parameter_transport hn q a p hp scale ε
          hε hε1 hscale hscale1 hq E hleft hright hpoint w
        have hpw' : oldEdgeParameter a p (crossingVisitEdge q v) ε scale
            (crossingVisitParameter Q (crossingVisit_mapEquiv E w)) =
              crossingVisitParameter q w := by
          rw [he]
          exact hpw
        have hmono := oldEdgeParameter_strictMono a p (crossingVisitEdge q v)
          ε scale hε hε1 hscale hscale1
        constructor
        · intro h
          have hm : oldEdgeParameter a p (crossingVisitEdge q v) ε scale
              (crossingVisitParameter Q (crossingVisit_mapEquiv E v)) <
            oldEdgeParameter a p (crossingVisitEdge q v) ε scale
              (crossingVisitParameter Q (crossingVisit_mapEquiv E w)) := by
            rw [hpv, hpw']
            exact h
          exact hmono.lt_iff_lt.mp hm
        · intro h
          have hm := hmono h
          rw [hpv, hpw'] at hm
          exact hm
      · have hneq : edgeLift a (crossingVisitEdge q v) ≠ edgeLift a (crossingVisitEdge q w) :=
          fun h => he (edgeLift_injective a h)
        constructor
        · intro h
          rcases h with h | ⟨hEq, _⟩
          · exact Or.inl ((edgeLift_strictMono a) h)
          · exact False.elim (he hEq)
        · intro h
          rcases h with h | ⟨hEq, _⟩
          · exact Or.inl (hlt _ _ |>.mpr h)
          · exact False.elim (hneq hEq)


private theorem truncationPolygonEventVisit_edge_ne_short {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (v : CrossingVisit (truncateCyclicCorner q a p scale ε)) :
    crossingVisitEdge (truncateCyclicCorner q a p scale ε) v ≠ a.castSucc := by
  let w := crossingVisit_mapEquiv E.symm v
  have hw : crossingVisit_mapEquiv E w = v := (crossingVisit_mapEquiv E).apply_symm_apply v
  have hedge := crossingVisit_mapEquiv_edge q a p scale ε E hleft hright w
  rw [hw] at hedge
  exact fun hv => edgeLift_ne_short a (crossingVisitEdge q w) (hedge.symm.trans hv)

noncomputable def truncationPolygonEventEquiv {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε)) :
    PolygonEvent q ≃ {x : PolygonEvent (truncateCyclicCorner q a p scale ε) //
      x ≠ Sum.inl a.castSucc} := by
  classical
  let Q := truncateCyclicCorner q a p scale ε
  let f : PolygonEvent q → {x : PolygonEvent Q // x ≠ Sum.inl a.castSucc} := fun x =>
    ⟨truncationPolygonEventMap q a p scale ε E x, by
      cases x with
      | inl e =>
        change Sum.inl (edgeLift a e) ≠ Sum.inl a.castSucc
        exact fun h => edgeLift_ne_short a e (Sum.inl.inj h)
      | inr v => simp [truncationPolygonEventMap]⟩
  apply Equiv.ofBijective f
  constructor
  · intro x y h
    apply truncationPolygonEventMap_injective q a p scale ε E
    exact congrArg Subtype.val h
  · intro y
    have hy : y.val ∈ Set.range (truncationPolygonEventMap q a p scale ε E) := by
      rw [truncationPolygonEventMap_range]
      exact y.property
    rcases hy with ⟨x, hx⟩
    refine ⟨x, ?_⟩
    apply Subtype.ext
    exact hx

@[simp] theorem truncationPolygonEventEquiv_apply_val {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (a p : Fin n) (scale ε : ℝ)
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (x : PolygonEvent q) :
    (truncationPolygonEventEquiv q a p scale ε E x).val =
      truncationPolygonEventMap q a p scale ε E x := rfl

noncomputable def truncationPolygonEventOrderIso {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) :
    letI := polygonEventOrder q hq.g2
    letI := polygonEventOrder (truncateCyclicCorner q a p scale ε) hQ.g2
    PolygonEvent q ≃o {x : PolygonEvent (truncateCyclicCorner q a p scale ε) //
      x ≠ Sum.inl a.castSucc} := by
  let Q := truncateCyclicCorner q a p scale ε
  letI : LinearOrder (PolygonEvent q) := polygonEventOrder q hq.g2
  letI : LinearOrder (PolygonEvent Q) := polygonEventOrder Q hQ.g2
  refine { toEquiv := truncationPolygonEventEquiv q a p scale ε E, map_rel_iff' := ?_ }
  intro x y
  change (truncationPolygonEventMap q a p scale ε E x ≤
      truncationPolygonEventMap q a p scale ε E y) ↔ x ≤ y
  rw [← not_lt, ← not_lt]
  have horder := truncationPolygonEventMap_order_iff hn q a p hp scale ε
    hε hε1 hscale hscale1 hq hQ E hleft hright hpoint y x
  exact (not_congr horder).symm

theorem truncationPolygonEventSuccessor_extra {n : ℕ}
    (hn : 3 ≤ n) (q : Fin n → PlanarPoint ℝ) (a p : Fin n)
    (hp : cyclicSuccessor p = a) (scale ε : ℝ)
    (hε : 0 < ε) (hε1 : ε < 1) (hscale : 0 < ε * scale)
    (hscale1 : ε * scale < 1) (hq : CyclicGeneric q)
    (hQ : CyclicGeneric (truncateCyclicCorner q a p scale ε))
    (E : PolygonCrossing q ≃ PolygonCrossing (truncateCyclicCorner q a p scale ε))
    (hleft : ∀ c, (E c).val.1 = edgeLift a c.val.1)
    (hright : ∀ c, (E c).val.2 = edgeLift a c.val.2)
    (hpoint : ∀ c, crossingPoint (truncateCyclicCorner q a p scale ε) (E c) =
      crossingPoint q c) :
    polygonEventSuccessor (truncateCyclicCorner q a p scale ε) hQ.g2
      (Sum.inl a.castSucc) =
    truncationPolygonEventMap q a p scale ε E (Sum.inl a) := by
  let Q := truncateCyclicCorner q a p scale ε
  letI : LinearOrder (PolygonEvent Q) := polygonEventOrder Q hQ.g2
  let B : PolygonEvent Q := Sum.inl a.castSucc
  let C : PolygonEvent Q := truncationPolygonEventMap q a p scale ε E (Sum.inl a)
  have hBC : B < C := by
    have hFin : a.castSucc < edgeLift a a := by
      apply Fin.mk_lt_mk.mpr
      simp [edgeLift]
    simpa [B, C, truncationPolygonEventMap, polygonEventEdge,
      polygonEventParameter] using
        (polygonEvent_anchor_lt_iff Q hQ.g2 a.castSucc (edgeLift a a)).2 hFin
  have hmin : ∀ z : PolygonEvent Q, B < z → C ≤ z := by
    intro z hBz
    cases z with
    | inl e =>
      have he : a.castSucc < e := by
        rw [polygonEvent_lt_iff Q hQ.g2] at hBz
        simpa [B, polygonEventEdge, polygonEventParameter] using hBz
      have hidx : edgeLift a a ≤ e := by
        apply Fin.le_iff_val_le_val.mpr
        have heval : a.val < e.val := Fin.lt_iff_val_lt_val.mp he
        simp [edgeLift]
        omega
      rw [← not_lt]
      intro hzc
      have hrev := (polygonEvent_anchor_lt_iff Q hQ.g2 e (edgeLift a a)).mp hzc
      exact (not_lt_of_ge hidx) hrev
    | inr v =>
      have hvshort := truncationPolygonEventVisit_edge_ne_short q a p scale ε E
        hleft hright v
      have hEdge : a.castSucc < crossingVisitEdge Q v := by
        rw [polygonEvent_lt_iff Q hQ.g2] at hBz
        rcases hBz with hlt | ⟨heq, hpar⟩
        · exact hlt
        · exact False.elim (hvshort (heq.symm))
      have hidx : edgeLift a a ≤ crossingVisitEdge Q v := by
        apply Fin.le_iff_val_le_val.mpr
        have hEdgeVal : a.val < (crossingVisitEdge Q v).val :=
          Fin.lt_iff_val_lt_val.mp hEdge
        simp [edgeLift]
        omega
      rw [← not_lt]
      intro hzC
      have hrev := (polygonEvent_lt_iff Q hQ.g2 (Sum.inr v) C).mp hzC
      rcases hrev with hlt | ⟨heq, hpar⟩
      · exact (not_lt_of_ge hidx) hlt
      · have hpv := (crossingVisitParameter_spec Q v).1
        have hparam : crossingVisitParameter Q v ≥ 0 := le_of_lt hpv
        have hpar' : crossingVisitParameter Q v < 0 := by
          simpa [C, truncationPolygonEventMap, polygonEventParameter] using hpar
        exact (not_lt_of_ge hparam) hpar'
  have hspec := polygonEventSuccessor_order_spec Q hQ.g2 B
  rcases hspec with ⟨hBs, hleast⟩ | ⟨hmax, _⟩
  · have hle : polygonEventSuccessor Q hQ.g2 B ≤ C := hleast C hBC
    have hge : C ≤ polygonEventSuccessor Q hQ.g2 B := hmin _ hBs
    exact le_antisymm hle hge
  · exact False.elim ((not_le_of_gt hBC) (hmax C))

end DirectGLSSW.TruncationEventOrder
