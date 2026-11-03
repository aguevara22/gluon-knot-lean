import ActualSplitBasePath

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.DescendingSpatial
open HOMFLY

/-- Same-height planar comparison segment, oriented A to B. -/
def splitBeta (D : PLLinkDiagram) (e : Fin D.nArc) : C(unitInterval, ℂ) where
  toFun t := Complex.equivRealProd.symm (affinePoint (splitBaseA D e) (splitBaseB D e) t.val)
  continuous_toFun := by
    simp only [Complex.equivRealProd_symm_apply, affinePoint]
    fun_prop

def splitMainComplex (D : PLLinkDiagram) (e : Fin D.nArc) : C(unitInterval, ℂ) where
  toFun t := Complex.equivRealProd.symm (splitMainPlanar D e t)
  continuous_toFun := by
    simp only [Complex.equivRealProd_symm_apply]
    fun_prop

def descendingMain (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    unitInterval → ℂ × ℝ := fun t => (splitMainComplex D e t, H+1-t.val)

/-- The omitted actual base subsegment, traversed B to A with rising height. -/
def ascendingClosure (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    unitInterval → ℂ × ℝ := fun t =>
      (Complex.equivRealProd.symm (affinePoint (splitBaseB D e) (splitBaseA D e) t.val),
        H+t.val)

def splitSpatialTrace (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) : Set (ℂ × ℝ) :=
  Set.range (descendingMain D e H) ∪ Set.range (ascendingClosure D e H)

theorem splitBeta_apply (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    splitBeta D e t = Complex.equivRealProd.symm
      (affinePoint (splitBaseA D e) (splitBaseB D e) t.val) := rfl

theorem splitMainComplex_apply (D : PLLinkDiagram) (e : Fin D.nArc) (t : unitInterval) :
    splitMainComplex D e t = Complex.equivRealProd.symm (splitMainPlanar D e t) := rfl

theorem descendingMain_apply (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ)
    (t : unitInterval) : descendingMain D e H t = (splitMainComplex D e t,H+1-t.val) := rfl

theorem ascendingClosure_apply (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ)
    (t : unitInterval) : ascendingClosure D e H t =
      (Complex.equivRealProd.symm (affinePoint (splitBaseB D e) (splitBaseA D e) t.val),
        H+t.val) := rfl

theorem mem_splitSpatialTrace_iff (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ)
    (x : ℂ × ℝ) : x ∈ splitSpatialTrace D e H ↔
      (∃ t, descendingMain D e H t = x) ∨ (∃ t, ascendingClosure D e H t = x) := Iff.rfl

theorem descendingMain_continuous (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Continuous (descendingMain D e H) := height_arc_continuous _ _

theorem descendingMain_injective (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Function.Injective (descendingMain D e H) := height_arc_injective _ _

theorem ascendingClosure_continuous (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Continuous (ascendingClosure D e H) := by
  unfold ascendingClosure
  simp only [Complex.equivRealProd_symm_apply, affinePoint]
  fun_prop

theorem ascendingClosure_injective (D : PLLinkDiagram) (e : Fin D.nArc) (H : ℝ) :
    Function.Injective (ascendingClosure D e H) := by
  intro s t h
  apply Subtype.ext
  have hh := congrArg Prod.snd h
  dsimp [ascendingClosure] at hh
  linarith

theorem splitMainComplex_endpoints (D : PLLinkDiagram) (e : Fin D.nArc) :
    splitMainComplex D e 0 = splitBeta D e 0 ∧
      splitMainComplex D e 1 = splitBeta D e 1 := by
  constructor
  · simp only [splitMainComplex_apply, splitBeta_apply]
    change Complex.equivRealProd.symm (splitMainPlanar D e 0) =
      Complex.equivRealProd.symm (affinePoint _ _ 0)
    rw [(splitMainPlanar_endpoints D e).1, affinePoint_zero]
  · simp only [splitMainComplex_apply, splitBeta_apply]
    change Complex.equivRealProd.symm (splitMainPlanar D e 1) =
      Complex.equivRealProd.symm (affinePoint _ _ 1)
    rw [(splitMainPlanar_endpoints D e).2, affinePoint_one]

end DirectGLSSW.DescendingSpatial










