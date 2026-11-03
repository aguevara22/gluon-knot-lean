import DirectGLSSW.LocalCoordinates

set_option autoImplicit false
namespace DirectGLSSW.NonalternatingEndpointTransport
open ChordNonalternation FiniteCycleOrder
noncomputable section

set_option maxHeartbeats 2000000 in
/-- Independent orientation choices for either chord leave the pair test unchanged. -/
theorem pair_test_relabel {C : Type*} {m : ℕ} (e : C × Bool → Fin m)
    (he : Function.Injective e) (c d : C) (hcd : c ≠ d) (a b : Bool) :
    (strictCyclicBetween (e (c,a)) (e (d,b)) (e (c,!a)) ↔
      strictCyclicBetween (e (c,a)) (e (d,!b)) (e (c,!a))) ↔
    (strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
      strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true))) := by
  have h00 : (e (c,false)).val ≠ (e (d,false)).val :=
    fun h => endpoints_ne_of_ne e he hcd false false (Fin.ext h)
  have h01 : (e (c,false)).val ≠ (e (d,true)).val :=
    fun h => endpoints_ne_of_ne e he hcd false true (Fin.ext h)
  have h10 : (e (c,true)).val ≠ (e (d,false)).val :=
    fun h => endpoints_ne_of_ne e he hcd true false (Fin.ext h)
  have h11 : (e (c,true)).val ≠ (e (d,true)).val :=
    fun h => endpoints_ne_of_ne e he hcd true true (Fin.ext h)
  cases a <;> cases b <;>
    simp only [Bool.not_false,Bool.not_true,strictCyclicBetween,Fin.lt_def] <;> omega

def relabelEndpoint {C : Type*} {m : ℕ} (e : C × Bool → Fin m) (flip : C → Bool) :
    C × Bool → Fin m := fun v => if flip v.1 then e (v.1,!v.2) else e v

theorem nonalternating_relabel {C : Type*} {m : ℕ} (e : C × Bool → Fin m)
    (he : Function.Injective e) (flip : C → Bool) (T : Finset C) :
    Nonalternating (relabelEndpoint e flip) T ↔ Nonalternating e T := by
  have hp (c d : C) (hcd : c ≠ d) :
      (strictCyclicBetween (relabelEndpoint e flip (c,false)) (relabelEndpoint e flip (d,false))
        (relabelEndpoint e flip (c,true)) ↔
       strictCyclicBetween (relabelEndpoint e flip (c,false)) (relabelEndpoint e flip (d,true))
        (relabelEndpoint e flip (c,true))) ↔
      (strictCyclicBetween (e (c,false)) (e (d,false)) (e (c,true)) ↔
       strictCyclicBetween (e (c,false)) (e (d,true)) (e (c,true))) := by
    cases hc : flip c <;> cases hd : flip d <;>
      simpa only [relabelEndpoint,hc,hd,Bool.false_eq_true,ite_false,ite_true,
        Bool.not_false,Bool.not_true] using pair_test_relabel e he c d hcd (flip c) (flip d)
  exact ⟨fun h c hc d hd hcd => (hp c d hcd).mp (h c hc d hd hcd),
    fun h c hc d hd hcd => (hp c d hcd).mpr (h c hc d hd hcd)⟩

theorem nonalternating_map {C D : Type*} {m : ℕ} (F : C ↪ D)
    (e : D × Bool → Fin m) (T : Finset C) :
    Nonalternating e (T.map F) ↔ Nonalternating (fun v => e (F v.1,v.2)) T := by
  constructor
  · intro h c hc d hd hcd
    exact h (F c) (Finset.mem_map.mpr ⟨c,hc,rfl⟩) (F d) (Finset.mem_map.mpr ⟨d,hd,rfl⟩)
      (fun heq => hcd (F.injective heq))
  · intro h c hc d hd hcd
    obtain ⟨a,ha,rfl⟩ := Finset.mem_map.mp hc
    obtain ⟨b,hb,rfl⟩ := Finset.mem_map.mp hd
    exact h a ha b hb (fun heq => hcd (congrArg F heq))





end
end DirectGLSSW.NonalternatingEndpointTransport
