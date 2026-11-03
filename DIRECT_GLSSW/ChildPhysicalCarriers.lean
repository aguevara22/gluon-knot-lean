import TruncatedCanonicalInventory
import ActiveArcClosedChildGeometry
import CutArcAuxiliaryConsumers

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain ActiveArc ActiveArc.Cursor ActiveArc.Split

theorem child_physical_carrier_incidence {a b : ℕ}
    (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q) (c : Crossing q)
    (hfirst : c.val.1 = 0) (hcut : c.val.2.val = a)
    (L : Fin (a+b+1) → CarrierLine)
    (hinc : ∀ e, lineValue (L e) (q e.castSucc) = 0 ∧ lineValue (L e) (q e.succ) = 0) :
    ∀ i : Fin (a+1), lineValue (L (childEdge (b:=b) i)) (child q hR c hfirst hcut i) = 0 ∧
      lineValue (L (childEdge (b:=b) i)) (child q hR c hfirst hcut (cyclicSuccessor i)) = 0 := by
  intro i
  constructor
  · by_cases hi : i = 0
    · subst i
      rw [child_zero]
      change lineValue (L 0) _ = 0
      have hp := (leftParameter_spec q c).2.2
      rw [hfirst] at hp
      rw [hp]
      exact ActualCarrierTransport.lineValue_affine _ _ _ _ (hinc 0).1 (hinc 0).2
    · rw [child_nonzero q hR c hfirst hcut i hi]
      exact (hinc (childEdge (b:=b) i)).1
  · by_cases hi : i.val = a
    · rw [child_last_successor i hi,child_zero]
      have he : childEdge (b:=b) i = c.val.2 := Fin.ext (hi.trans hcut.symm)
      rw [he,(rightParameter_spec q c).2.2]
      exact ActualCarrierTransport.lineValue_affine _ _ _ _ (hinc c.val.2).1 (hinc c.val.2).2
    · have hil : i.val < a := by have := i.isLt; omega
      have hs := child_successor_val i hil
      have hs0 : cyclicSuccessor i ≠ 0 := by
        intro h
        have hh := congrArg Fin.val h
        simp only [Fin.val_zero] at hh
        omega
      rw [child_nonzero q hR c hfirst hcut _ hs0]
      have hv : childVertex (b:=b) (cyclicSuccessor i) = (childEdge (b:=b) i).succ := Fin.ext hs
      rw [hv]
      exact (hinc (childEdge (b:=b) i)).2

/-- The terminal/artificial label cannot occur on any physical edge. -/
theorem physical_label_ne_terminal {m N : ℕ} (f : Fin m ⊕ Unit → Fin (N+1))
    (hf : Function.Injective f) (ht : f (Sum.inr ()) = Fin.last N) (i : Fin m) :
    f (Sum.inl i) ≠ Fin.last N := by
  intro h
  exact Sum.noConfusion (hf (h.trans ht.symm))

/-- A literal child's physical-edge labels land in the original N carriers.
The actual old-label injection is constructed from the terminal-label invariant. -/
theorem exists_child_old_labels {a b N : ℕ}
    (f : Fin (a+b+1) ⊕ Unit → Fin (N+1)) (hf : Function.Injective f)
    (ht : f (Sum.inr ()) = Fin.last N) :
    ∃ g : Fin (a+1) → Fin N, Function.Injective g ∧
      ∀ i, (g i).castSucc = f (Sum.inl (childEdge (b:=b) i)) := by
  have hlt (i : Fin (a+1)) : (f (Sum.inl (childEdge (b:=b) i))).val < N := by
    have hn := physical_label_ne_terminal f hf ht (childEdge (b:=b) i)
    have hb := (f (Sum.inl (childEdge (b:=b) i))).isLt
    have hne : (f (Sum.inl (childEdge (b:=b) i))).val ≠ N := fun h => hn (Fin.ext h)
    omega
  let g : Fin (a+1) → Fin N := fun i => ⟨(f (Sum.inl (childEdge (b:=b) i))).val,hlt i⟩
  have he (i) : (g i).castSucc = f (Sum.inl (childEdge (b:=b) i)) := Fin.ext rfl
  refine ⟨g,?_,he⟩
  intro i j hij
  have hh := congrArg Fin.castSucc hij
  rw [he i,he j] at hh
  exact childEdge_injective (Sum.inl.inj (hf hh))

/-- Parent restriction preserves the actual terminal label and injectivity,
so the same omission proof applies at every later recursive cut. -/
theorem parent_label_invariants {a b N : ℕ}
    (f : Fin (a+b+1) ⊕ Unit → Fin (N+1)) (hf : Function.Injective f)
    (ht : f (Sum.inr ()) = Fin.last N) :
    Function.Injective (f ∘ suffixCarrierMap (a:=a) (b:=b)) ∧
      (f ∘ suffixCarrierMap (a:=a) (b:=b)) (Sum.inr ()) = Fin.last N := by
  exact ⟨hf.comp suffixCarrierMap_injective,ht⟩

end DirectGLSSW.CyclicCarrierClearing




