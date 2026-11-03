import UniformPLOrbitAddress
import UniformPLVisitWindow

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
open Equiv PermutationOrbits

noncomputable def basedArcIndex (t : ℝ) : ℕ := (Int.floor (t+1/2)).toNat

theorem basedArcIndex_decomposition (m : ℕ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) m) :
    (basedArcIndex t : ℝ) + Int.fract (t+1/2) = t+1/2 := by
  have h := Int.floor_add_fract (t+1/2)
  rw [← (basedUniform_address_bounds m t ht).1] at h
  simpa only [Int.cast_natCast] using h

theorem basedUniform_integer_visit_of_outgoing {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (t : ℝ)
    (ht : t ∈ Set.Icc (0 : ℝ) (componentArcLength D (T.baseArc C).val))
    (hfrac : Int.fract (t+1/2)=0) (c : Fin D.nCrossing) (i : Fin 2)
    (hout : (D.continuation ^ basedArcIndex t) (T.baseArc C).val = D.outgoing c (D.through c i)) :
    componentOf D.continuation (D.incoming c i)=C ∧ t=crossingVisitTime T c i := by
  let e := (T.baseArc C).val
  let m := componentArcLength D e
  let k := basedArcIndex t
  have hk : k ≤ m := (basedUniform_address_bounds m t ht).2
  have htdec := basedArcIndex_decomposition m t ht
  rw [hfrac,add_zero] at htdec
  have hkpos : 0 < k := by
    have hkr : (0 : ℝ) < (k : ℝ) := by dsimp [k]; linarith [ht.1]
    exact_mod_cast hkr
  have hcompout : componentOf D.continuation (D.outgoing c (D.through c i))=C := by
    rw [← hout, componentOf_pow_apply]
    exact (T.baseArc C).property
  have hcomp : componentOf D.continuation (D.incoming c i)=C := by
    have hp := componentOf_apply D.continuation (D.incoming c i)
    rw [D.continuation_crossing] at hp
    exact hp.symm.trans hcompout
  have hpre : (D.continuation ^ visitPosition T (D.incoming c i)) e = D.incoming c i := by
    have hb : (T.baseArc (componentOf D.continuation (D.incoming c i))).val = e :=
      congrArg (fun K : diagramComponent D => (T.baseArc K).val) hcomp
    rw [← hb]
    exact visitPosition_reconstruct T (D.incoming c i)
  have hpost : (D.continuation ^ (visitPosition T (D.incoming c i)+1)) e =
      D.outgoing c (D.through c i) := by
    rw [pow_succ',Perm.mul_apply,hpre,D.continuation_crossing]
  have hrank : visitPosition T (D.incoming c i)+1 ≤ m := by
    have h := visitPosition_lt_actual_period T (D.incoming c i)
    rw [hcomp] at h
    exact h
  have hpow : (D.continuation ^ k) e = (D.continuation ^ (visitPosition T (D.incoming c i)+1)) e :=
    hout.trans hpost.symm
  have heq : k=visitPosition T (D.incoming c i)+1 := by
    rcases (continuation_pow_closed_period_iff D e k _ hk hrank).mp hpow with h | ⟨h,_⟩ | ⟨_,h⟩
    · exact h
    · omega
    · omega
  refine ⟨hcomp,?_⟩
  change t = (visitPosition T (D.incoming c i) : ℝ)+1/2
  change (k : ℝ) = t+1/2 at htdec
  rw [heq] at htdec
  push_cast at htdec
  linarith

end DirectGLSSW.HOMFLY.PrincipalTurning


