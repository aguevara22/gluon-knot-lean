import ActiveArcConfigurationParentTransport
import ActiveArcParentCarrierChain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationParent
open DirectGLSSW ActiveArc ConfigurationLocality Split Cursor RetainedWords OpenCarrier
attribute [local instance] Classical.propDecidable

private theorem ofFn_at_equal_indices {α : Type*} {m n : ℕ} (f : Fin m → α) (g : Fin n → α)
    (h : List.ofFn f=List.ofFn g) (i : Fin m) (j : Fin n) (hij : i.val=j.val) : f i=g j := by
  have hmn : m=n := by simpa only [List.length_ofFn] using congrArg List.length h
  subst n
  have hfg := List.ofFn_injective h
  rw [hfg,Fin.ext hij]

variable {a b : ℕ} (q r : Fin (a+b+2) → PlanarPoint ℝ) (hQ : Regular q) (hR : Regular r)
variable (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
variable (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
  (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (T : Primitive.Support (parent q c hcut) (regular_parent q hQ c hcut))

theorem parent_sideCarrier_eq
    (i : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val - 1))
    (j : Fin (openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val - 1))
    (hij : i.val=j.val) :
    openSideCarrier (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val i =
    openSideCarrier (parent q c hcut) (regular_parent q hQ c hcut) T.val j := by
  apply Fin.ext
  exact ofFn_at_equal_indices _ _ (parent_open_carrier_word q r hQ hR E hlabels horder c hc hcut T)
    ⟨i.val,by change i.val < openCount _ _ _; have := i.isLt; omega⟩
    ⟨j.val,by change j.val < openCount _ _ _; have := j.isLt; omega⟩ hij

/-- The actual coordinate-label chains agree at corresponding integer positions.
Only the last label is the nonphysical terminal coordinate line. -/
theorem parent_chain_eq
    (i : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val + 1))
    (j : Fin (openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val + 1))
    (hij : i.val=j.val) :
    parentCarrierChain r hR (E c) (mapped_cut q r E hlabels c hcut)
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i =
    parentCarrierChain q hQ c hcut T j := by
  have hn := parent_open_count q r hQ hR E hlabels horder c hc hcut T
  by_cases hi0 : i.val=0
  · have hj0 : j.val=0 := hij.symm.trans hi0
    simp only [parentCarrierChain,dif_pos hi0,dif_pos hj0,hlabels]
  · have hj0 : j.val≠0 := fun he => hi0 (hij.trans he)
    by_cases hil : i.val=openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
        (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
        (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val
    · have hjl : j.val=openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val :=
        hij.symm.trans (hil.trans hn)
      simp only [parentCarrierChain,dif_neg hi0,dif_neg hj0,dif_pos hil,dif_pos hjl]
    · have hjl : j.val≠openCount (parent q c hcut) (regular_parent q hQ c hcut) T.val :=
        fun he => hil (hij.trans (he.trans hn.symm))
      simp only [parentCarrierChain,dif_neg hi0,dif_neg hj0,dif_neg hil,dif_neg hjl]
      congr 2
      apply parent_sideCarrier_eq q r hQ hR E hlabels horder c hc hcut T
      exact congrArg (fun k => k-1) hij

/-- Direct Fin.cast form for the actual nearby-to-original chain. -/
theorem parent_chain_cast
    (i : Fin (openCount (parent r (E c) (mapped_cut q r E hlabels c hcut))
      (regular_parent r hR (E c) (mapped_cut q r E hlabels c hcut))
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T).val + 1)) :
    parentCarrierChain r hR (E c) (mapped_cut q r E hlabels c hcut)
      (parentSupportEquiv q r hQ hR E hlabels horder c hc hcut T) i =
    parentCarrierChain q hQ c hcut T
      (Fin.cast (congrArg (fun k => k+1) (parent_open_count q r hQ hR E hlabels horder c hc hcut T)) i) :=
  parent_chain_eq q r hQ hR E hlabels horder c hc hcut T i _ rfl

end DirectGLSSW.ActiveArc.ConfigurationParent
