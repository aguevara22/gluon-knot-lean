import HoleClockwiseIncidence

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits
noncomputable section
attribute [local instance] Classical.propDecidable

theorem secantVisitHalfCell_injective {D : PLLinkDiagram} (T : BasedTraversal D)
    (c : Fin D.nCrossing) (i : Fin 2) :
    Function.Injective (secantVisitHalfCell T c i) := by
  intro h k he
  have hs := secantVisit_endpoints_straddle T c i
  fin_cases h <;> fin_cases k
  · rfl
  · have he' := congrArg Prod.fst he
    simp only [secantVisitHalfCell,ite_true,show (1 : Fin 2)≠0 by decide,ite_false] at he'
    exact False.elim ((ne_of_lt hs.1) he')
  · have he' := congrArg Prod.fst he
    simp only [secantVisitHalfCell,ite_true,show (1 : Fin 2)≠0 by decide,ite_false] at he'
    exact False.elim ((ne_of_lt hs.1) he'.symm)
  · rfl

theorem crossingHoleOutsideSideIndex_injective :
    Function.Injective crossingHoleOutsideSideIndex := by
  intro s t he
  fin_cases s <;> fin_cases t <;>
    simp [crossingHoleOutsideSideIndex] at he ⊢

/-- Multiplicity-free local hole incidence: two exterior labels produce the
same literal retained side only when all three labels agree. -/
theorem crossingHoleOutsideSide_injective {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (c : Fin D.nCrossing) (i j : Fin 2)
    (hij : i≠j) (hi : componentOf D.continuation (D.incoming c i)=C)
    (hj : componentOf D.continuation (D.incoming c j)=C)
    (horder : crossingVisitTime T c i < crossingVisitTime T c j)
    (a b u v : ℝ)
    (ha : secantAxisAdjacent T C a (secantVisitLeft T c i))
    (hb : secantAxisAdjacent T C (secantVisitRight T c i) b)
    (hu : secantAxisAdjacent T C u (secantVisitLeft T c j))
    (hv : secantAxisAdjacent T C (secantVisitRight T c j) v)
    (h k h' k' : Fin 2) (s s' : Fin 4)
    (hext : crossingHoleGridExterior h k s)
    (hext' : crossingHoleGridExterior h' k' s')
    (he : crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h k s =
      crossingHoleOutsideSide T C c i j hij hi hj horder a b u v ha hb hu hv h' k' s') :
    h=h' ∧ k=k' ∧ s=s' := by
  have hs : s=s' := crossingHoleOutsideSideIndex_injective (congrArg Prod.snd he)
  subst s'
  have hc := congrArg (fun e : RetainedRectangleSide T C => e.1.val) he
  change crossingHoleOutsideCell T c i j h k a b u v s =
    crossingHoleOutsideCell T c i j h' k' a b u v s at hc
  fin_cases s
  · have hk : k=0 := by simpa [crossingHoleGridExterior] using hext
    have hk' : k'=0 := by simpa [crossingHoleGridExterior] using hext'
    have hh := secantVisitHalfCell_injective T c i (by simpa [crossingHoleOutsideCell] using congrArg Prod.fst hc)
    exact ⟨hh,hk.trans hk'.symm,rfl⟩
  · have hh : h=1 := by simpa [crossingHoleGridExterior] using hext
    have hh' : h'=1 := by simpa [crossingHoleGridExterior] using hext'
    have hk := secantVisitHalfCell_injective T c j (by simpa [crossingHoleOutsideCell] using congrArg Prod.snd hc)
    exact ⟨hh.trans hh'.symm,hk,rfl⟩
  · have hk : k=1 := by simpa [crossingHoleGridExterior] using hext
    have hk' : k'=1 := by simpa [crossingHoleGridExterior] using hext'
    have hh := secantVisitHalfCell_injective T c i (by simpa [crossingHoleOutsideCell] using congrArg Prod.fst hc)
    exact ⟨hh,hk.trans hk'.symm,rfl⟩
  · have hh : h=0 := by simpa [crossingHoleGridExterior] using hext
    have hh' : h'=0 := by simpa [crossingHoleGridExterior] using hext'
    have hk := secantVisitHalfCell_injective T c j (by simpa [crossingHoleOutsideCell] using congrArg Prod.snd hc)
    exact ⟨hh.trans hh'.symm,hk,rfl⟩

end
end DirectGLSSW.HOMFLY.PrincipalTurning



