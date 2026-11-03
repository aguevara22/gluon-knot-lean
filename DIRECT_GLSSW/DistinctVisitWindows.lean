import CommonSecantCrossingWindow
import FiniteSecantRetainedRectangles

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open PermutationOrbits

/-- Actual distinct incoming crossing ports, including different crossings. -/
theorem crossingIncoming_pair_injective (D : PLLinkDiagram) :
    Function.Injective (fun ci : Fin D.nCrossing × Fin 2 => D.incoming ci.1 ci.2) := by
  intro ⟨c,i⟩ ⟨d,j⟩ he
  have hc : c=d := D.crossingVertex_injective (by
    rw [← D.incoming_target c i,← D.incoming_target d j]
    exact congrArg D.arcTarget he)
  subst d
  have hij : i=j := by
    have hn := (D.four_ports_distinct c).1
    fin_cases i <;> fin_cases j <;> simp_all
  subst j
  rfl

/-- Same-component rank injectivity is derived from the actual BasedTraversal. -/
theorem crossingVisit_position_ne {D : PLLinkDiagram} (T : BasedTraversal D)
    (c d : Fin D.nCrossing) (i j : Fin 2)
    (hne : (c,i) ≠ (d,j))
    (hC : componentOf D.continuation (D.incoming c i) =
      componentOf D.continuation (D.incoming d j)) :
    visitPosition T (D.incoming c i) ≠ visitPosition T (D.incoming d j) := by
  intro hp
  apply hne
  apply crossingIncoming_pair_injective D
  apply visitRank_injective T
  simp only [visitRank,hC,hp]

/-- SOURCE-PREPARED, UNCOMPILED: every distinct pair of actual component
visit windows has a strict gap greater than1/2, in its actual visit order. -/
theorem distinctVisitWindows_separated {D : PLLinkDiagram} (T : BasedTraversal D)
    (c d : Fin D.nCrossing) (i j : Fin 2)
    (hne : (c,i) ≠ (d,j))
    (hC : componentOf D.continuation (D.incoming c i) =
      componentOf D.continuation (D.incoming d j)) :
    secantVisitRight T c i + 1/2 < secantVisitLeft T d j ∨
      secantVisitRight T d j + 1/2 < secantVisitLeft T c i := by
  have hε := secantMeshEpsilon_positive D
  have hrightc := secantMesh_inverse_window D c i (2*secantMeshEpsilon D) ⟨by linarith,le_rfl⟩
  have hrightd := secantMesh_inverse_window D d j (2*secantMeshEpsilon D) ⟨by linarith,le_rfl⟩
  have hleftc := secantMesh_inverse_window D c i (-secantMeshEpsilon D) ⟨le_rfl,by linarith⟩
  have hleftd := secantMesh_inverse_window D d j (-secantMeshEpsilon D) ⟨le_rfl,by linarith⟩
  rcases lt_or_gt_of_ne (crossingVisit_position_ne T c d i j hne hC) with hp | hp
  · have hg : (visitPosition T (D.incoming c i) : ℝ)+1 ≤
        (visitPosition T (D.incoming d j) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hp)
    left
    dsimp [secantVisitRight,secantVisitLeft,crossingVisitTime]
    linarith [hrightc.2,hleftd.1]
  · have hg : (visitPosition T (D.incoming d j) : ℝ)+1 ≤
        (visitPosition T (D.incoming c i) : ℝ) := by exact_mod_cast (Nat.succ_le_iff.mpr hp)
    right
    dsimp [secantVisitRight,secantVisitLeft,crossingVisitTime]
    linarith [hrightd.2,hleftc.1]

end DirectGLSSW.HOMFLY.PrincipalTurning



