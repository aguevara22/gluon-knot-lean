import ActiveArcEventMap
import ActiveArcConfigurationOrbits
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.ConfigurationLocality
open DirectGLSSW ActiveArc Filter Topology ConfigurationTransport RetainedWords
private theorem ofFn_at_equal_positions {α : Type*} {m k : ℕ} (f : Fin m → α) (g : Fin k → α)
    (h : List.ofFn f=List.ofFn g) (u : Fin m) (v : Fin k) (huv : u.val=v.val) :
    f u=g v := by
  have hmk : m=k := by simpa only [List.length_ofFn] using congrArg List.length h
  subst k
  rw [List.ofFn_injective h,Fin.ext huv]

variable {n : ℕ} (q r : Fin (n+2) → PlanarPoint ℝ)

/-- Fixed physical event labels evaluated at arbitrary anchor coordinates.
On the actual configuration chart this is exactly the mapped event point. -/
def eventPointFormula (x : Event q) : PlanarPoint ℝ :=
  match x with
  | .inl i => r i
  | .inr v => affinePoint (r v.1.val.1.castSucc) (r v.1.val.1.succ)
      (parameterFormula r v.1.val false)

theorem eventPointFormula_eq_mapped (hR : Regular r) (E : Crossing q ≃ Crossing r)
    (hlabels : ∀ c, (E c).val=c.val) (x : Event q) :
    eventPointFormula q r x=eventPoint r (eventMapEquiv q r E x) := by
  cases x with
  | inl i => rfl
  | inr v =>
    have hp := parameterFormula_eq_mapped q r hR E hlabels (v.1,false)
    change parameterFormula r v.1.val false=leftParameter r (E v.1) at hp
    change affinePoint _ _ _=crossingPoint r (E v.1)
    rw [hp,(leftParameter_spec r (E v.1)).2.2,hlabels]

theorem eventPointFormula_recovery (hQ : Regular q) (x : Event q) :
    eventPointFormula q q x=eventPoint q x := by
  cases x with
  | inl i => rfl
  | inr v =>
    have hp := parameterFormula_eq_actual q hQ (v.1,false)
    change parameterFormula q v.1.val false=leftParameter q v.1 at hp
    change affinePoint _ _ _=crossingPoint q v.1
    rw [hp]
    exact (leftParameter_spec q v.1).2.2.symm

theorem eventPointFormula_continuousAt (hQ : Regular q) (x : Event q) :
    ContinuousAt (fun r => eventPointFormula q r x) q := by
  cases x with
  | inl i => exact (continuous_apply i).continuousAt
  | inr v =>
    have hp := parameterFormula_continuousAt q hQ (v.1,false)
    change ContinuousAt (fun r => parameterFormula r v.1.val false) q at hp
    change ContinuousAt (fun r => affinePoint (r v.1.val.1.castSucc)
      (r v.1.val.1.succ) (parameterFormula r v.1.val false)) q
    have ha := (continuous_apply (π := fun _ : Fin (n+2) => PlanarPoint ℝ)
      v.1.val.1.castSucc).continuousAt (x := q)
    have hb := (continuous_apply (π := fun _ : Fin (n+2) => PlanarPoint ℝ)
      v.1.val.1.succ).continuousAt (x := q)
    exact (ha.fst.add (hp.mul (hb.fst.sub ha.fst))).prodMk
      (ha.snd.add (hp.mul (hb.snd.sub ha.snd)))

/-- Actual retained vertices are the fixed-label continuous point formulas at
the same integer positions. Counts and ordering are supplied by the chart. -/
theorem retained_vertex_eq_formula (hQ : Regular q) (hR : Regular r)
    (E : Crossing q ≃ Crossing r) (hlabels : ∀ c, (E c).val=c.val)
    (horder : ∀ x y : Event q, (eventOrder q hQ.noTriple).lt x y ↔
      (eventOrder r hR.noTriple).lt (eventMapEquiv q r E x) (eventMapEquiv q r E y))
    (S : Finset (Crossing q)) (root : Event q)
    (i : Fin (Fintype.card (Corner q hQ S root)))
    (j : Fin (Fintype.card (Corner r hR (selectionEquiv q r E S)
      (eventMapEquiv q r E root)))) (hij : i.val=j.val) :
    vertex r hR (selectionEquiv q r E S) (eventMapEquiv q r E root) j=
      eventPointFormula q r (cornerEvent q hQ S root i) := by
  have hw := event_retainedEvents q r hQ hR E horder S root
  rw [List.map_ofFn] at hw
  have he : cornerEvent r hR (selectionEquiv q r E S) (eventMapEquiv q r E root) j=
      eventMapEquiv q r E (cornerEvent q hQ S root i) := by
    exact ofFn_at_equal_positions
      (cornerEvent r hR (selectionEquiv q r E S) (eventMapEquiv q r E root))
      (fun i => eventMapEquiv q r E (cornerEvent q hQ S root i)) hw j i hij.symm
  rw [vertex,he,← eventPointFormula_eq_mapped q r hR E hlabels]





end DirectGLSSW.ActiveArc.ConfigurationLocality
