import ActiveArcAfterFirstWords

set_option autoImplicit false
set_option maxHeartbeats 800000
noncomputable section
namespace DirectGLSSW.ActiveArc.Cursor.Surviving
open DirectGLSSW ActiveArc Nonalternation FiniteCycleOrder
attribute [local instance] Classical.propDecidable
variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ) (hR : Regular q)
variable (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t < 1)

def crossingEmbedding : Crossing (moveStart q t) ↪ Crossing q where
  toFun := crossingToOriginal q t ht0 ht1
  inj' := by
    intro d e h
    exact Subtype.ext (congrArg (fun x : Crossing q => x.val) h)

/-- Image of the actual moving physical crossings in the original label set. -/
def originalSelection (T : Finset (Crossing (moveStart q t))) : Finset (Crossing q) :=
  T.map (crossingEmbedding q t ht0 ht1)

@[simp] theorem originalSelection_card (T : Finset (Crossing (moveStart q t))) :
    (originalSelection q t ht0 ht1 T).card = T.card := Finset.card_map _

theorem eventMap_between (hM : Regular (moveStart q t)) (x y z : Event (moveStart q t)) :
    Nonalternation.between q hR (eventMap q t ht0 ht1 x)
      (eventMap q t ht0 ht1 y) (eventMap q t ht0 ht1 z) ↔
    Nonalternation.between (moveStart q t) hM x y z := by
  letI := eventOrder q hR.noTriple
  letI := eventOrder (moveStart q t) hM.noTriple
  simp only [Nonalternation.between,strictCyclicBetween,eventMap_lt q hR t ht0 ht1 hM]

theorem originalSelection_nonalternating (hM : Regular (moveStart q t))
    (T : Finset (Crossing (moveStart q t))) :
    Nonalternation.Nonalternating q hR (originalSelection q t ht0 ht1 T) ↔
      Nonalternation.Nonalternating (moveStart q t) hM T := by
  let E := crossingEmbedding q t ht0 ht1
  have hb (d e : Crossing (moveStart q t)) (b : Bool) :
      Nonalternation.between q hR (Sum.inr (E d,false)) (Sum.inr (E e,b)) (Sum.inr (E d,true)) ↔
      Nonalternation.between (moveStart q t) hM
        (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true)) :=
    eventMap_between q hR t ht0 ht1 hM (Sum.inr (d,false)) (Sum.inr (e,b)) (Sum.inr (d,true))
  constructor
  · intro h d hd e he hde
    have hh := h (E d) (Finset.mem_map.mpr ⟨d,hd,rfl⟩)
      (E e) (Finset.mem_map.mpr ⟨e,he,rfl⟩) (fun hh => hde (E.injective hh))
    exact (hb d e false).symm.trans (hh.trans (hb d e true))
  · intro h d hd e he hde
    obtain ⟨d',hd',hdd⟩ := Finset.mem_map.mp (show d ∈ T.map E from hd)
    obtain ⟨e',he',hee⟩ := Finset.mem_map.mp (show e ∈ T.map E from he)
    subst d; subst e
    have hh := h d' hd' e' he' (fun hh => hde (congrArg E hh))
    exact (hb d' e' false).trans (hh.trans (hb d' e' true).symm)

theorem movingSelection_originalSelection (T : Finset (Crossing (moveStart q t))) :
    movingSelection q t ht0 ht1 (originalSelection q t ht0 ht1 T) = T := by
  ext d
  rw [movingSelection_mem]
  change crossingEmbedding q t ht0 ht1 d ∈ T.map (crossingEmbedding q t ht0 ht1) ↔ d ∈ T
  exact Finset.mem_map' _

theorem originalSelection_movingSelection (S : Finset (Crossing q))
    (hS : ∀ d∈S, Survives q t d) :
    originalSelection q t ht0 ht1 (movingSelection q t ht0 ht1 S) = S := by
  ext d
  constructor
  · intro hd
    obtain ⟨e,he,hed⟩ := Finset.mem_map.mp hd
    rw [movingSelection_mem] at he
    exact hed ▸ he
  · intro hd
    let e := crossingFromOriginal q t ht1 d (hS d hd)
    apply Finset.mem_map.mpr
    refine ⟨e,?_,rfl⟩
    rw [movingSelection_mem]
    exact hd

include hR in
theorem originalSelection_survives (T : Finset (Crossing (moveStart q t)))
    (d : Crossing q) (hd : d ∈ originalSelection q t ht0 ht1 T) : Survives q t d := by
  obtain ⟨e,he,hed⟩ := Finset.mem_map.mp hd
  subst d
  exact crossingToOriginal_survives q hR t ht0 ht1 e

end DirectGLSSW.ActiveArc.Cursor.Surviving
