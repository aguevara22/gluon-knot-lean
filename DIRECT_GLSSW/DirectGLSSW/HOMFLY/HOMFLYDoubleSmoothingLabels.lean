import DirectGLSSW.HOMFLY.HOMFLYSwitchSmoothDiamond

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY

/-- The common label for an original crossing retained after deleting both
distinct sites. -/
abbrev TwiceDeletedCrossingCode (D : PLLinkDiagram)
    (c d : Fin D.nCrossing) :=
  {e : Fin D.nCrossing // e ≠ c ∧ e ≠ d}

/-- The nested sum code for arcs after smoothing c and then d. -/
abbrev TwiceSmoothArcCode (D : PLLinkDiagram) :=
  ((Fin D.nArc ⊕ Fin 2) ⊕ Fin 2)

/-- Reordering two smoothing steps fixes old arcs and swaps the two connector
blocks. -/
def twiceSmoothArcCodeSwap (D : PLLinkDiagram) :
    TwiceSmoothArcCode D ≃ TwiceSmoothArcCode D where
  toFun
    | Sum.inl (Sum.inl e) => Sum.inl (Sum.inl e)
    | Sum.inl (Sum.inr i) => Sum.inr i
    | Sum.inr i => Sum.inl (Sum.inr i)
  invFun
    | Sum.inl (Sum.inl e) => Sum.inl (Sum.inl e)
    | Sum.inl (Sum.inr i) => Sum.inr i
    | Sum.inr i => Sum.inl (Sum.inr i)
  left_inv := by
    intro x
    cases x with
    | inl y =>
      cases y <;> rfl
    | inr i => rfl
  right_inv := by
    intro x
    cases x with
    | inl y =>
      cases y <;> rfl
    | inr i => rfl

/-- The source twice-smoothed crossing labels correspond to original labels
other than c and d. -/
noncomputable def smoothTwiceCrossingToDeleted_cFirst
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hd : d ≠ c) :
    Fin (smoothCrossing
      (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hd⟩)).nCrossing ≃
        TwiceDeletedCrossingCode D c d := by
  let e1 := smoothCrossingEquiv D c
  let d1 := e1 ⟨d, hd⟩
  let e2 := smoothCrossingEquiv (smoothCrossing D c) d1
  refine
    { toFun := fun x =>
        let x2 := e2.symm x
        let x1 := e1.symm x2.val
        ⟨x1.val, x1.property, ?_⟩
      invFun := fun y =>
        let y1 : {q : Fin (D.nCrossing - 1) // q ≠ d1} :=
          ⟨e1 ⟨y.val, y.property.1⟩, ?_⟩
        e2 y1
      left_inv := ?_
      right_inv := ?_ }
  · intro hx
    let x2 := e2.symm x
    let x1 := e1.symm x2.val
    have hx1 : x1 = ⟨d, hd⟩ := Subtype.ext hx
    have hx2 : x2.val = e1 ⟨d, hd⟩ := by
      calc
        x2.val = e1 (e1.symm x2.val) := (e1.apply_symm_apply x2.val).symm
        _ = e1 ⟨d, hd⟩ := congrArg e1 hx1
    exact x2.property hx2
  · intro heq
    have heq' : e1 ⟨y.val, y.property.1⟩ = e1 ⟨d, hd⟩ := by
      simpa [d1] using heq
    have hsub := e1.injective heq'
    exact y.property.2 (congrArg Subtype.val hsub)
  · intro x
    simp [e1, e2, d1]
  · intro y
    apply Subtype.ext
    simp [e2, e1, d1]

/-- The target twice-smoothed crossing labels correspond to the same
double-deleted parent labels, with the two exclusions in the opposite order. -/
noncomputable def smoothTwiceCrossingToDeleted_dFirst
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hc : c ≠ d) :
    Fin (smoothCrossing
      (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hc⟩)).nCrossing ≃
        {e : Fin D.nCrossing // e ≠ d ∧ e ≠ c} := by
  let hdc : c ≠ d := hc
  let e1 := smoothCrossingEquiv D d
  let c1 := e1 ⟨c, hdc⟩
  let e2 := smoothCrossingEquiv (smoothCrossing D d) c1
  refine
    { toFun := fun x =>
        let x2 := e2.symm x
        let x1 := e1.symm x2.val
        ⟨x1.val, x1.property, ?_⟩
      invFun := fun y =>
        let y1 : {q : Fin (D.nCrossing - 1) // q ≠ c1} :=
          ⟨e1 ⟨y.val, y.property.1⟩, ?_⟩
        e2 y1
      left_inv := ?_
      right_inv := ?_ }
  · intro hx
    let x2 := e2.symm x
    let x1 := e1.symm x2.val
    have hx1 : x1 = ⟨c, hc⟩ := Subtype.ext hx
    have hx2 : x2.val = e1 ⟨c, hc⟩ := by
      calc
        x2.val = e1 (e1.symm x2.val) := (e1.apply_symm_apply x2.val).symm
        _ = e1 ⟨c, hc⟩ := congrArg e1 hx1
    exact x2.property hx2
  · intro heq
    have heq' : e1 ⟨y.val, y.property.1⟩ = e1 ⟨c, hc⟩ := by
      simpa [c1] using heq
    have hsub := e1.injective heq'
    exact y.property.2 (congrArg Subtype.val hsub)
  · intro x
    simp [e1, e2, c1]
  · intro y
    apply Subtype.ext
    simp [e2, e1, c1]


/-- Exchange the order of the two exclusions in the common parent label. -/
def twiceDeletedCrossingSwap {D : PLLinkDiagram}
    {c d : Fin D.nCrossing} :
    TwiceDeletedCrossingCode D c d ≃
      {e : Fin D.nCrossing // e ≠ d ∧ e ≠ c} where
  toFun e := ⟨e.val, e.property.2, e.property.1⟩
  invFun e := ⟨e.val, e.property.2, e.property.1⟩
  left_inv := by intro e; apply Subtype.ext; rfl
  right_inv := by intro e; apply Subtype.ext; rfl

/-- Crossing labels after smoothing c,d map to the same parent labels as
smoothing d,c, by deleting both sites at the subtype level. -/
noncomputable def smoothTwiceCrossingLabelEquiv
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    Fin (smoothCrossing
      (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nCrossing ≃
    Fin (smoothCrossing
      (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).nCrossing :=
  (smoothTwiceCrossingToDeleted_cFirst D c d hcd.symm).trans
    ((twiceDeletedCrossingSwap).trans
      (smoothTwiceCrossingToDeleted_dFirst D c d hcd).symm)

/-- Arc labels after smoothing c,d map to labels after d,c by flattening the
two local Sum codes, swapping the connector blocks, then returning to Fin. -/
noncomputable def smoothTwiceArcLabelEquiv
    (D : PLLinkDiagram) (c d : Fin D.nCrossing) (hcd : c ≠ d) :
    Fin (smoothCrossing
      (smoothCrossing D c)
      (smoothCrossingEquiv D c ⟨d, hcd.symm⟩)).nArc ≃
    Fin (smoothCrossing
      (smoothCrossing D d)
      (smoothCrossingEquiv D d ⟨c, hcd⟩)).nArc := by
  let e0 := smoothArcEquiv D
  let ec := smoothArcEquiv (smoothCrossing D c)
  let ed := smoothArcEquiv (smoothCrossing D d)
  exact ec.symm.trans
    ((Equiv.sumCongr e0.symm (Equiv.refl (Fin 2))).trans
      ((twiceSmoothArcCodeSwap D).trans
        ((Equiv.sumCongr e0 (Equiv.refl (Fin 2))).trans ed)))

end DirectGLSSW.HOMFLY







