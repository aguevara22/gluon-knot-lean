import ActiveArcParentProperness
import CarrierFamilyDensity
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc RetainedWords Split AuxiliaryCarrierChart
variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hcut : c.val.2.val=a)

/-- The determinant numerator for c and two later vertices of the actual parent word. -/
def parentFarNumerator (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
    (i j : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val))
    (L : Fin (a+b+1) ⊕ Unit → CarrierLine) : ℝ :=
  let z := openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val
  let f := parentCarrierChain q hR c hcut T
  carrierTripleNumerator (L (f z.castSucc)) (L (f z.succ))
    (L (f i.castSucc)) (L (f i.succ)) (L (f j.castSucc)) (L (f j.succ))

/-- One carrier assignment excludes every actual parent's far triple, for every NA support. -/
def parentFarLocus (L : Fin (a+b+1) ⊕ Unit → CarrierLine) : Prop :=
  ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
    ∀ i j : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val),
      0 < i.val → i.val < j.val → parentFarNumerator q hR c hcut T i j L≠0

private abbrev FarIndex :=
  Σ T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut),
    {p : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) ×
      Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val) //
      0 < p.1.val ∧ p.1.val < p.2.val}

/-- The finite actual-parent far-triple family has a common dense open carrier locus. -/
theorem parent_far_family_dense_open :
    Dense {L | parentFarLocus q hR c hcut L} ∧ IsOpen {L | parentFarLocus q hR c hcut L} := by
  classical
  letI : Fintype (FarIndex q hR c hcut) := by unfold FarIndex; infer_instance
  let A : FarIndex q hR c hcut → Set (Fin (a+b+1) ⊕ Unit → CarrierLine) :=
    fun x => {L | parentFarNumerator q hR c hcut x.1 x.2.val.1 x.2.val.2 L≠0}
  have hD : ∀ x, Dense (A x) := by
    rintro ⟨T,⟨⟨i,j⟩,hi,hij⟩⟩
    change 0 < i.val at hi
    change i.val < j.val at hij
    apply parent_triple_numerator_dense q hR c hcut T
      (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val) i j
    · intro h; have hh := congrArg Fin.val h; change 0=i.val at hh; omega
    · exact Fin.ne_of_val_ne (ne_of_lt hij)
    · intro h; have hh := congrArg Fin.val h; change 0=j.val at hh; omega
  have hO : ∀ x, IsOpen (A x) := by
    intro x
    exact CarrierDensity.isOpen_assignmentNumerator_ne_zero _ _ _ _ _ _
  have hJoint := CarrierFamilyDensity.finite_family_dense_open A hD hO
  have heq : (⋂ x, A x)={L | parentFarLocus q hR c hcut L} := by
    ext L
    simp only [Set.mem_iInter,Set.mem_setOf_eq]
    constructor
    · intro h T i j hi hij
      exact h ⟨T,⟨(i,j),hi,hij⟩⟩
    · intro h x
      exact h x.1 x.2.val.1 x.2.val.2 x.2.property.1 x.2.property.2
  rw [heq] at hJoint
  exact hJoint

/-- At the actual source-G1 geometry this is exactly the required literal far determinant. -/
theorem parent_far_numerator_zero_iff (hG1 : cyclicNoncollinear q)
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut))
    (i j : Fin (openCount (parent q c hcut) (regular_parent q hR c hcut) T.val)) :
    parentFarNumerator q hR c hcut T i j (parentChartLines q)=0 ↔
      planarDet
        (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T i-crossingPoint q c)
        (Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T j-crossingPoint q c)=0 := by
  have h := parent_triple_numerator_zero_iff q hR c hcut T hG1
    (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val) i j
  have hp : Primitive.OpenVertex (parent q c hcut) (regular_parent q hR c hcut) T
      (openFirst (parent q c hcut) (regular_parent q hR c hcut) T.val)=crossingPoint q c :=
    (open_vertex_first (parent q c hcut) (regular_parent q hR c hcut) T.val).trans (parent_zero q c hcut)
  rw [hp] at h
  exact h

end DirectGLSSW.ActiveArc.OpenCarrier
