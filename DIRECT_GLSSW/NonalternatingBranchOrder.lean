import DirectGLSSW.ChordNonalternation
import DirectGLSSW.FiniteCycleOrder

set_option autoImplicit false

namespace DirectGLSSW.ChordNonalternation

open DirectGLSSW.FiniteCycleOrder

private theorem strictCyclicBetween_outer_swap_iff_not {m : ℕ}
    (x y z : Fin m) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z) :
    strictCyclicBetween y z x ↔ ¬ strictCyclicBetween x z y := by
  have hxy' : x.val ≠ y.val := fun h => hxy (Fin.ext h)
  have hxz' : x.val ≠ z.val := fun h => hxz (Fin.ext h)
  have hyz' : y.val ≠ z.val := fun h => hyz (Fin.ext h)
  simp only [strictCyclicBetween, Fin.lt_def]
  omega

private theorem iff_complements_iff {P Q : Prop} :
    (P ↔ Q) ↔ (¬ P ↔ ¬ Q) := by
  constructor
  · exact not_congr
  · intro h
    have hh := not_congr h
    simpa using hh

/-- Independently swapping the two endpoint labels of any chord preserves the
literal pairwise nonalternation relation. -/
theorem nonalternating_endpoint_relabel_iff {C : Type*} {m : ℕ}
    (e : C × Bool → Fin m) (he : Function.Injective e)
    (β : C → Equiv.Perm Bool) (S : Finset C) :
    Nonalternating e S ↔
      Nonalternating (fun x : C × Bool => e (x.1, β x.1 x.2)) S := by
  classical
  let eβ : C × Bool → Fin m := fun x => e (x.1, β x.1 x.2)
  have hβcases (c : C) :
      (β c false = false ∧ β c true = true) ∨
      (β c false = true ∧ β c true = false) := by
    by_cases h0 : β c false = false
    · left
      refine ⟨h0, ?_⟩
      cases h1 : β c true with
      | false =>
          have hbad : (false : Bool) = true := (β c).injective (by rw [h0, h1])
          cases hbad
      | true => rfl
    · right
      have h0' : β c false = true := by
        cases h : β c false with
        | false => exact False.elim (h0 h)
        | true => rfl
      refine ⟨h0', ?_⟩
      cases h1 : β c true with
      | false => rfl
      | true =>
          have hbad : (false : Bool) = true := (β c).injective (by rw [h0', h1])
          cases hbad
  have houter (c d : C) (hcd : c ≠ d) :
      let A := e (c, false); let B := e (c, true)
      let X := e (d, false); let Y := e (d, true)
      (strictCyclicBetween B X A ↔ ¬ strictCyclicBetween A X B) ∧
      (strictCyclicBetween B Y A ↔ ¬ strictCyclicBetween A Y B) := by
    dsimp
    have hAB : e (c, false) ≠ e (c, true) := by
      intro h
      have hp := he h
      cases hp
    have hAX : e (c, false) ≠ e (d, false) := by
      intro h
      have hp := he h
      exact hcd (congrArg Prod.fst hp)
    have hAY : e (c, false) ≠ e (d, true) := by
      intro h
      have hp := he h
      exact hcd (congrArg Prod.fst hp)
    have hBX : e (c, true) ≠ e (d, false) := by
      intro h
      have hp := he h
      exact hcd (congrArg Prod.fst hp)
    have hBY : e (c, true) ≠ e (d, true) := by
      intro h
      have hp := he h
      exact hcd (congrArg Prod.fst hp)
    exact ⟨strictCyclicBetween_outer_swap_iff_not _ _ _ hAB hAX hBX,
      strictCyclicBetween_outer_swap_iff_not _ _ _ hAB hAY hBY⟩
  have hpair (c d : C) (hcd : c ≠ d) :
      (strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) ↔
        strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true))) ↔
      (strictCyclicBetween (eβ (c, false)) (eβ (d, false)) (eβ (c, true)) ↔
        strictCyclicBetween (eβ (c, false)) (eβ (d, true)) (eβ (c, true))) := by
    rcases hβcases c with ⟨hc0, hc1⟩ | ⟨hc0, hc1⟩ <;>
      rcases hβcases d with ⟨hd0, hd1⟩ | ⟨hd0, hd1⟩
    · simp [eβ, hc0, hc1, hd0, hd1]
    · simp only [eβ, hc0, hc1, hd0, hd1]
      change (strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) ↔
        strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true))) ↔
        (strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)) ↔
          strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)))
      exact ⟨Iff.symm, Iff.symm⟩
    · let A := e (c, false); let B := e (c, true)
      let X := e (d, false); let Y := e (d, true)
      simp only [eβ, hc0, hc1, hd0, hd1]
      have hcx := (houter c d hcd).1
      have hcy := (houter c d hcd).2
      change (strictCyclicBetween A X B ↔ strictCyclicBetween A Y B) ↔
        (strictCyclicBetween B X A ↔ strictCyclicBetween B Y A)
      have hcx' : strictCyclicBetween (e (c, true)) (e (d, false)) (e (c, false)) ↔
          ¬ strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) := hcx
      have hcy' : strictCyclicBetween (e (c, true)) (e (d, true)) (e (c, false)) ↔
          ¬ strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)) := hcy
      have hrel :
          (strictCyclicBetween (e (c, true)) (e (d, false)) (e (c, false)) ↔
            strictCyclicBetween (e (c, true)) (e (d, true)) (e (c, false))) ↔
          (¬ strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) ↔
            ¬ strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true))) := by
        constructor
        · intro h
          exact ⟨fun hP => hcy'.mp (h.mp (hcx'.mpr hP)),
            fun hQ => hcx'.mp (h.mpr (hcy'.mpr hQ))⟩
        · intro h
          exact ⟨fun hP' => hcy'.mpr (h.mp (hcx'.mp hP')),
            fun hQ' => hcx'.mpr (h.mpr (hcy'.mp hQ'))⟩
      exact (iff_complements_iff).trans hrel.symm
    · let A := e (c, false); let B := e (c, true)
      let X := e (d, false); let Y := e (d, true)
      simp only [eβ, hc0, hc1, hd0, hd1]
      have hcx := (houter c d hcd).1
      have hcy := (houter c d hcd).2
      change (strictCyclicBetween A X B ↔ strictCyclicBetween A Y B) ↔
        (strictCyclicBetween B Y A ↔ strictCyclicBetween B X A)
      have hcx' : strictCyclicBetween (e (c, true)) (e (d, false)) (e (c, false)) ↔
          ¬ strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) := hcx
      have hcy' : strictCyclicBetween (e (c, true)) (e (d, true)) (e (c, false)) ↔
          ¬ strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)) := hcy
      have hsymm :
          (strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)) ↔
            strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true))) ↔
          (strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)) ↔
            strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true))) :=
        ⟨Iff.symm, Iff.symm⟩
      have hcomp := iff_complements_iff
        (P := strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)))
        (Q := strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true)))
      have hrel :
          (¬ strictCyclicBetween (e (c, false)) (e (d, true)) (e (c, true)) ↔
            ¬ strictCyclicBetween (e (c, false)) (e (d, false)) (e (c, true))) ↔
          (strictCyclicBetween (e (c, true)) (e (d, true)) (e (c, false)) ↔
            strictCyclicBetween (e (c, true)) (e (d, false)) (e (c, false))) := by
        constructor
        · intro h
          exact ⟨fun hQ' => hcx'.mpr (h.mp (hcy'.mp hQ')),
            fun hX' => hcy'.mpr (h.mpr (hcx'.mp hX'))⟩
        · intro h
          exact ⟨fun hQ => hcx'.mp (h.mp (hcy'.mpr hQ)),
            fun hX => hcy'.mp (h.mpr (hcx'.mpr hX))⟩
      exact hsymm.trans (hcomp.trans hrel)
  constructor
  · intro hS c hc d hd hcd
    exact (hpair c d hcd).mp (hS c hc d hd hcd)
  · intro hS c hc d hd hcd
    exact (hpair c d hcd).mpr (hS c hc d hd hcd)

/-- An increasing relabeling of the whole finite endpoint order, followed by
independent endpoint relabelings within each chord, preserves nonalternation. -/
theorem nonalternating_order_relabel_iff {C D : Type*} [DecidableEq C]
    [DecidableEq D] {m n : ℕ}
    (e : C × Bool → Fin m) (he : Function.Injective e)
    (f : D × Bool → Fin n) (hf : Function.Injective f)
    (g : C ≃ D) (β : C → Equiv.Perm Bool)
    (horder : ∀ x y : C × Bool,
      (e x < e y ↔ f (g x.1, β x.1 x.2) < f (g y.1, β y.1 y.2)))
    (S : Finset C) :
    Nonalternating e S ↔ Nonalternating f (S.map g.toEmbedding) := by
  classical
  let eβ : C × Bool → Fin n := fun x => f (g x.1, β x.1 x.2)
  let β' : D → Equiv.Perm Bool := fun d => β (g.symm d)
  let fβ : D × Bool → Fin n := fun x => f (x.1, β' x.1 x.2)
  let T : Finset D := S.map g.toEmbedding
  have hBetween (x y z : C × Bool) :
      strictCyclicBetween (e x) (e y) (e z) ↔
        strictCyclicBetween (eβ x) (eβ y) (eβ z) := by
    change strictCyclicBetween (e x) (e y) (e z) ↔
      strictCyclicBetween (f (g x.1, β x.1 x.2))
        (f (g y.1, β y.1 y.2)) (f (g z.1, β z.1 z.2))
    simp only [strictCyclicBetween, horder x y, horder y z, horder z x]
  have horderRel : Nonalternating e S ↔ Nonalternating eβ S := by
    unfold Nonalternating
    constructor
    · intro h c hc d hd hcd
      have h0 := hBetween (c, false) (d, false) (c, true)
      have h1 := hBetween (c, false) (d, true) (c, true)
      exact h0.symm.trans ((h c hc d hd hcd).trans h1)
    · intro h c hc d hd hcd
      have h0 := hBetween (c, false) (d, false) (c, true)
      have h1 := hBetween (c, false) (d, true) (c, true)
      exact h0.trans ((h c hc d hd hcd).trans h1.symm)
  have hmatch (c : C) (b : Bool) : eβ (c, b) = fβ (g c, b) := by
    simp [eβ, fβ, β', Equiv.apply_symm_apply]
  have hfβ : Function.Injective fβ := by
    intro x y h
    have hp : (x.1, β' x.1 x.2) = (y.1, β' y.1 y.2) := hf (by simpa [fβ] using h)
    have hfst := congrArg Prod.fst hp
    have hsnd := congrArg Prod.snd hp
    have hbool : x.2 = y.2 := by
      rw [hfst] at hsnd
      exact (β' y.1).injective hsnd
    exact Prod.ext hfst hbool
  have hmap : Nonalternating eβ S ↔ Nonalternating fβ T := by
    unfold Nonalternating
    constructor
    · intro h d hd d' hd' hdd
      rcases Finset.mem_map.mp hd with ⟨c, hc, rfl⟩
      rcases Finset.mem_map.mp hd' with ⟨c', hc', rfl⟩
      have hcd : c ≠ c' := fun hcc => hdd (congrArg g hcc)
      simpa only [hmatch] using h c hc c' hc' hcd
    · intro h c hc c' hc' hcc
      have hgg : g c ≠ g c' := fun heq => hcc (g.injective heq)
      have h := h (g c) (Finset.mem_map.mpr ⟨c, hc, rfl⟩)
        (g c') (Finset.mem_map.mpr ⟨c', hc', rfl⟩) hgg
      simpa only [hmatch] using h
  let βinv : D → Equiv.Perm Bool := fun d => (β' d).symm
  have hflip := nonalternating_endpoint_relabel_iff fβ hfβ βinv T
  have hflip' : Nonalternating fβ T ↔ Nonalternating f T := by
    simpa [βinv, fβ] using hflip
  exact horderRel.trans (hmap.trans hflip')

#check @nonalternating_endpoint_relabel_iff

#check @nonalternating_order_relabel_iff


end DirectGLSSW.ChordNonalternation
