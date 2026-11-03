import ActiveArcConfigurationParentChain
import ActiveArcParentFarFamily
import ActiveArcParentSuppliedLines
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationParent
open DirectGLSSW ActiveArc ConfigurationLocality Split Cursor RetainedWords OpenCarrier AuxiliaryCarrierChart
attribute [local instance] Classical.propDecidable
variable {a b : ℕ} (q r : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (L : Fin (a+b+1) ⊕ Unit → CarrierLine)
variable (hinc : ∀ e : Fin (a+b+1), lineValue (L (Sum.inl e)) (r e.castSucc)=0 ∧
  lineValue (L (Sum.inl e)) (r e.succ)=0)
variable (hterminal : lineValue (L (Sum.inr ())) (r ⟨a+b+1,by omega⟩)=0)
variable (hden : ∀ T : Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut),
  ∀ i : Fin (openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val),
    lineDenominator (L (parentCarrierChain q hQ c hcut T i.castSucc))
      (L (parentCarrierChain q hQ c hcut T i.succ))≠0)

include hinc hterminal hden horder hc in
/-- A fixed original chain pair, evaluated at supplied L, is the corresponding
actual nearby retained parent vertex. No identification L=parentChartLines r is used. -/
theorem mapped_vertex_supplied_intersection
    (T : Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut))
    (i : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val)) :
    lineIntersection
      (L (parentCarrierChain q hQ c hcut T
        (Fin.cast (parent_open_count q r hQ hR E hlabels horder c hc hcut T) i).castSucc))
      (L (parentCarrierChain q hQ c hcut T
        (Fin.cast (parent_open_count q r hQ hR E hlabels horder c hc hcut T) i).succ)) =
    Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i := by
  let j := Fin.cast (parent_open_count q r hQ hR E hlabels horder c hc hcut T) i
  have h0 := parent_chain_eq q r hQ hR E hlabels horder c hc hcut T i.castSucc j.castSucc rfl
  have h1 := parent_chain_eq q r hQ hR E hlabels horder c hc hcut T i.succ j.succ rfl
  have hd : lineDenominator
      (L (parentCarrierChain r hR (E c) (mapped_cut q r E hlabels c hcut)
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i.castSucc))
      (L (parentCarrierChain r hR (E c) (mapped_cut q r E hlabels c hcut)
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i.succ))≠0 := by
    rw [h0,h1]
    exact hden T j
  have hi := parent_vertex_supplied_line_intersection r hR (E c)
    (mapped_cut q r E hlabels c hcut) (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T)
    L hinc hterminal i hd
  rw [h0,h1] at hi
  exact hi

include hinc hterminal hden horder hc in
/-- The fixed original far-locus excludes the actual mapped nearby parent far triple. -/
theorem mapped_parent_far_nonzero (hfar : parentFarLocus q hQ c hcut L)
    (T : Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut))
    (i j : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val))
    (hi : 0 < i.val) (hij : i.val < j.val) :
    planarDet
      (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i-crossingPoint r (E c))
      (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) j-crossingPoint r (E c))≠0 := by
  let p := parent r (E c) (mapped_cut q r E hlabels c hcut)
  let hp := regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)
  let U := parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T
  let z := openFirst p hp U.val
  let z0 := openFirst (parent q c hcut) (regular_parent q hQ c hcut) T.val
  let hn := parent_open_count q r hQ hR E hlabels horder c hc hcut T
  let i0 := Fin.cast hn i
  let j0 := Fin.cast hn j
  have hzi : Fin.cast hn z=z0 := Fin.ext rfl
  have hz := mapped_vertex_supplied_intersection q r hQ hR E hlabels horder c hc hcut L hinc hterminal hden T z
  rw [hzi] at hz
  have hpz : Primitive.OpenVertex p hp U z=crossingPoint r (E c) :=
    (open_vertex_first p hp U.val).trans (parent_zero r (E c) (mapped_cut q r E hlabels c hcut))
  rw [hpz] at hz
  have hvi := mapped_vertex_supplied_intersection q r hQ hR E hlabels horder c hc hcut L hinc hterminal hden T i
  have hvj := mapped_vertex_supplied_intersection q r hQ hR E hlabels horder c hc hcut L hinc hterminal hden T j
  have hnz := hfar T i0 j0 hi hij
  dsimp only [parentFarNumerator] at hnz
  intro hzero
  apply hnz
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hden T z0) (hden T i0) (hden T j0)).mpr
  rw [hz,hvi,hvj]
  exact hzero

include hinc hterminal hden horder hc in
/-- Every actual nearby parent support is covered by the inverse support equivalence. -/
theorem all_parent_far_nonzero (hfar : parentFarLocus q hQ c hcut L)
    (U : Primitive.Support (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)))
    (i j : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) U.val))
    (hi : 0 < i.val) (hij : i.val < j.val) :
    planarDet
      (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) U i-crossingPoint r (E c))
      (Primitive.OpenVertex (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut)) U j-crossingPoint r (E c))≠0 := by
  obtain ⟨T,rfl⟩ := (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut).surjective U
  exact mapped_parent_far_nonzero q r hQ hR E hlabels horder c hc hcut L hinc hterminal hden hfar T i j hi hij

end DirectGLSSW.ActiveArc.ConfigurationParent
