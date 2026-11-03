import DirectGLSSW.OrbitWordPrerequisite

set_option autoImplicit false
namespace DirectGLSSW.PermutationOrbits

/-- An injective intertwining identifies the literal rooted orbit word. No
surjectivity onto the entire ambient carrier is required. -/
theorem orbitWord_map_injective {A B : Type*} [Fintype A] [Fintype B]
    (p : Equiv.Perm A) (s : Equiv.Perm B) (f : A → B)
    (hf : Function.Injective f) (hstep : ∀ x, s (f x)=f (p x)) (root : A) :
    orbitWord s (f root)=(orbitWord p root).map f := by
  classical
  let N := Fintype.card (Fibre p (componentOf p root))
  have hN : 0<N := Fintype.card_pos_iff.mpr ⟨⟨root,rfl⟩⟩
  let g : Fin N → B := fun i => f (orbitEnumeration p root i).val
  have hg : Function.Injective g := hf.comp
    (Subtype.val_injective.comp (orbitEnumeration p root).injective)
  have hs : ∀ i, s (g i)=g (cyclicSuccessor i) := by
    intro i
    have he := congrArg Subtype.val (orbitEnumeration_successor p root i)
    exact (hstep _).trans (congrArg f he.symm)
  have hr : g ⟨0,hN⟩=f root := by simp [g]
  have hw := orbitWord_eq_of_injective_cyclicSuccessor s hN g hg hs
  rw [hr] at hw
  simpa only [g,orbitWord,List.map_ofFn,Function.comp_def] using hw

end DirectGLSSW.PermutationOrbits
