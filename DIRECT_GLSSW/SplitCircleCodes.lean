import SplitCircleTriangle
import Mathlib.Data.Fintype.EquivFin

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.SplitCircleConstructor
open DirectGLSSW

variable (D : PLLinkDiagram) (R : ℝ)

abbrev VertexCode := Fin D.nVertex ⊕ Fin (rightTriangle R).nVertex
abbrev ArcCode := Fin D.nArc ⊕ Fin (rightTriangle R).nArc

noncomputable def vertexEquiv : VertexCode D R ≃
    Fin (D.nVertex + (rightTriangle R).nVertex) :=
  Fintype.equivFinOfCardEq (by simp [VertexCode])

noncomputable def arcEquiv : ArcCode D R ≃
    Fin (D.nArc + (rightTriangle R).nArc) :=
  Fintype.equivFinOfCardEq (by simp [ArcCode])

def vertexPointCode : VertexCode D R → PlanarPoint ℝ
  | .inl v => D.vertexPoint v
  | .inr v => (rightTriangle R).vertexPoint v

def sourceCode : ArcCode D R → VertexCode D R
  | .inl e => .inl (D.arcSource e)
  | .inr e => .inr ((rightTriangle R).arcSource e)

def targetCode : ArcCode D R → VertexCode D R
  | .inl e => .inl (D.arcTarget e)
  | .inr e => .inr ((rightTriangle R).arcTarget e)

def continuationCode : Equiv.Perm (ArcCode D R) :=
  Equiv.sumCongr D.continuation (rightTriangle R).continuation

theorem continuationCode_incidence (e : ArcCode D R) :
    targetCode D R e = sourceCode D R (continuationCode D R e) := by
  cases e with
  | inl e => exact congrArg Sum.inl (D.continuation_incidence e)
  | inr e => exact congrArg Sum.inr ((rightTriangle R).continuation_incidence e)

theorem sourceCode_ne_targetCode (e : ArcCode D R) :
    sourceCode D R e ≠ targetCode D R e := by
  cases e with
  | inl e => exact fun h => D.arc_endpoints_distinct e (Sum.inl.inj h)
  | inr e => exact fun h => (rightTriangle R).arc_endpoints_distinct e (Sum.inr.inj h)

theorem vertexPointCode_injective
    (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
    (hright : ∀ v : Fin (rightTriangle R).nVertex,
      R < ((rightTriangle R).vertexPoint v).1) :
    Function.Injective (vertexPointCode D R) := by
  intro v w h
  cases v with
  | inl v =>
      cases w with
      | inl w => exact congrArg Sum.inl (D.vertexPoint_injective h)
      | inr w =>
          have he : (D.vertexPoint v).1 = ((rightTriangle R).vertexPoint w).1 := by
            simpa only [vertexPointCode] using congrArg Prod.fst h
          have hv := hleft v
          rw [he] at hv
          exact False.elim (lt_asymm hv (hright w))
  | inr v =>
      cases w with
      | inl w =>
          have he : ((rightTriangle R).vertexPoint v).1 = (D.vertexPoint w).1 := by
            simpa only [vertexPointCode] using congrArg Prod.fst h
          have hw := hleft w
          rw [← he] at hw
          exact False.elim (lt_asymm hw (hright v))
      | inr w => exact congrArg Sum.inr ((rightTriangle R).vertexPoint_injective h)

def arcPointCode (e : ArcCode D R) (t : ℝ) : PlanarPoint ℝ :=
  affinePoint (vertexPointCode D R (sourceCode D R e))
    (vertexPointCode D R (targetCode D R e)) t

theorem arcPointCode_left (e : Fin D.nArc) (t : ℝ) :
    arcPointCode D R (.inl e) t =
      affinePoint (D.vertexPoint (D.arcSource e))
        (D.vertexPoint (D.arcTarget e)) t := rfl

theorem arcPointCode_right (e : Fin (rightTriangle R).nArc) (t : ℝ) :
    arcPointCode D R (.inr e) t =
      affinePoint ((rightTriangle R).vertexPoint ((rightTriangle R).arcSource e))
        ((rightTriangle R).vertexPoint ((rightTriangle R).arcTarget e)) t := rfl

theorem arcPointCode_left_x_lt
    (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
    (e : Fin D.nArc) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (arcPointCode D R (.inl e) t).1 < R := by
  rw [arcPointCode_left]
  exact affine_x_lt (hleft _) (hleft _) ht0 ht1

theorem arcPointCode_right_x_gt
    (hright : ∀ v : Fin (rightTriangle R).nVertex,
      R < ((rightTriangle R).vertexPoint v).1)
    (e : Fin (rightTriangle R).nArc) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    R < (arcPointCode D R (.inr e) t).1 := by
  rw [arcPointCode_right]
  exact affine_x_gt (hright _) (hright _) ht0 ht1

theorem arcPointCode_interiors_disjoint
    (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
    (hright : ∀ v : Fin (rightTriangle R).nVertex,
      R < ((rightTriangle R).vertexPoint v).1)
    (e f : ArcCode D R) (hef : e ≠ f)
    (s t : ℝ) (hs0 : 0 < s) (hs1 : s < 1) (ht0 : 0 < t) (ht1 : t < 1) :
    arcPointCode D R e s ≠ arcPointCode D R f t := by
  cases e with
  | inl e =>
      cases f with
      | inl f =>
          exact D.arc_interiors_disjoint e f (fun h => hef (congrArg Sum.inl h))
            s t hs0 hs1 ht0 ht1
      | inr f =>
          intro h
          have hx := congrArg Prod.fst h
          have hl := arcPointCode_left_x_lt D R hleft e s (le_of_lt hs0) (le_of_lt hs1)
          have hr := arcPointCode_right_x_gt D R hright f t (le_of_lt ht0) (le_of_lt ht1)
          rw [hx] at hl
          exact lt_asymm hl hr
  | inr e =>
      cases f with
      | inl f =>
          intro h
          have hx := congrArg Prod.fst h
          have hr := arcPointCode_right_x_gt D R hright e s (le_of_lt hs0) (le_of_lt hs1)
          have hl := arcPointCode_left_x_lt D R hleft f t (le_of_lt ht0) (le_of_lt ht1)
          rw [hx] at hr
          exact lt_asymm hl hr
      | inr f =>
          exact (rightTriangle R).arc_interiors_disjoint e f
            (fun h => hef (congrArg Sum.inr h)) s t hs0 hs1 ht0 ht1

theorem vertexPointCode_avoid_arc_interiors
    (hleft : ∀ v : Fin D.nVertex, (D.vertexPoint v).1 < R)
    (hright : ∀ v : Fin (rightTriangle R).nVertex,
      R < ((rightTriangle R).vertexPoint v).1)
    (v : VertexCode D R) (e : ArcCode D R) (t : ℝ)
    (ht0 : 0 < t) (ht1 : t < 1) :
    vertexPointCode D R v ≠ arcPointCode D R e t := by
  cases v with
  | inl v =>
      cases e with
      | inl e => exact D.vertices_avoid_arc_interiors v e t ht0 ht1
      | inr e =>
          intro h
          have hx := congrArg Prod.fst h
          have hl := hleft v
          have hr := arcPointCode_right_x_gt D R hright e t (le_of_lt ht0) (le_of_lt ht1)
          change (D.vertexPoint v).1 = (arcPointCode D R (.inr e) t).1 at hx
          rw [hx] at hl
          exact lt_asymm hl hr
  | inr v =>
      cases e with
      | inl e =>
          intro h
          have hx := congrArg Prod.fst h
          have hr := hright v
          have hl := arcPointCode_left_x_lt D R hleft e t (le_of_lt ht0) (le_of_lt ht1)
          change ((rightTriangle R).vertexPoint v).1 = (arcPointCode D R (.inl e) t).1 at hx
          rw [hx] at hr
          exact lt_asymm hl hr
      | inr e => exact (rightTriangle R).vertices_avoid_arc_interiors v e t ht0 ht1

theorem code_regular_degree_one (v : VertexCode D R)
    (hv : ∀ c : Fin D.nCrossing, Sum.inl (D.crossingVertex c) ≠ v) :
    (Finset.univ.filter (fun e : ArcCode D R => targetCode D R e = v)).card = 1 ∧
    (Finset.univ.filter (fun e : ArcCode D R => sourceCode D R e = v)).card = 1 := by
  classical
  cases v with
  | inl v =>
      have hD : (incomingArcs D.arcTarget v).card = 1 ∧
          (outgoingArcs D.arcSource v).card = 1 :=
        D.regular_degree_one v (fun c h => hv c (congrArg Sum.inl h))
      constructor
      · have heq : (Finset.univ.filter (fun e : ArcCode D R =>
            targetCode D R e = Sum.inl v)) =
            (incomingArcs D.arcTarget v).map ⟨Sum.inl, Sum.inl_injective⟩ := by
          ext e
          cases e with
          | inl e => simp [incomingArcs, targetCode]
          | inr e => simp [targetCode]
        rw [heq, Finset.card_map]
        exact hD.1
      · have heq : (Finset.univ.filter (fun e : ArcCode D R =>
            sourceCode D R e = Sum.inl v)) =
            (outgoingArcs D.arcSource v).map ⟨Sum.inl, Sum.inl_injective⟩ := by
          ext e
          cases e with
          | inl e => simp [outgoingArcs, sourceCode]
          | inr e => simp [sourceCode]
        rw [heq, Finset.card_map]
        exact hD.2
  | inr v =>
      have hT : (incomingArcs (rightTriangle R).arcTarget v).card = 1 ∧
          (outgoingArcs (rightTriangle R).arcSource v).card = 1 :=
        (rightTriangle R).regular_degree_one v (by
          intro c
          exact Fin.elim0 c)
      constructor
      · have heq : (Finset.univ.filter (fun e : ArcCode D R =>
            targetCode D R e = Sum.inr v)) =
            (incomingArcs (rightTriangle R).arcTarget v).map
              ⟨Sum.inr, Sum.inr_injective⟩ := by
          ext e
          cases e with
          | inl e => simp [targetCode]
          | inr e => simp [incomingArcs, targetCode]
        rw [heq, Finset.card_map]
        exact hT.1
      · have heq : (Finset.univ.filter (fun e : ArcCode D R =>
            sourceCode D R e = Sum.inr v)) =
            (outgoingArcs (rightTriangle R).arcSource v).map
              ⟨Sum.inr, Sum.inr_injective⟩ := by
          ext e
          cases e with
          | inl e => simp [sourceCode]
          | inr e => simp [outgoingArcs, sourceCode]
        rw [heq, Finset.card_map]
        exact hT.2

end DirectGLSSW.HOMFLY.SplitCircleConstructor

