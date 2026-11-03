import ProcessedChildOriginalChain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.HOMFLY
open PermutationOrbits LowestRowContract
attribute [local instance] Classical.propDecidable
variable {s t : MarkedParentState} (h : MarkedParentTrace s t)
    (c : Fin t.1.nCrossing) (hc : badAt t.2.1 c)
    (R : ComponentRestriction (smoothCrossing t.1 c)
      (rootSelfCutComponents t.1 c (t.2.2.connected _ _)
        (firstVisitedBranch t.2.1 c) (Sum.inl true)))

/-- A genuine PL component cannot consist of a single nondegenerate arc. Thus
the old word after removing the new connector is nonempty. -/
theorem detachedOldOrbitSize_pos : 0 < detachedOrbitSize t c R-1 := by
  have hpos := detachedOrbitSize_pos t c R
  by_contra hn
  have hsize : detachedOrbitSize t c R=1 := by omega
  let root := detachedConnector t c R
  let j := (detachedOrbitEquiv t c R).symm (R.diagram.continuation root)
  have hj : j = ⟨0,detachedOrbitSize_pos t c R⟩ := by
    apply Fin.ext
    have hlt := j.isLt
    change j.val=0
    omega
  have hfix : R.diagram.continuation root = root := by
    have he := (detachedOrbitEquiv t c R).apply_symm_apply (R.diagram.continuation root)
    change detachedOrbitEquiv t c R j = _ at he
    rw [hj,detachedOrbitEquiv_zero] at he
    exact he.symm
  have hinc := R.diagram.continuation_incidence root
  rw [hfix] at hinc
  exact R.diagram.arc_endpoints_distinct root hinc.symm

/-- The actual old-arc word is a literal consecutive segment of the original
continuation orbit, not merely a word with a supplied cyclic-order relation. -/
theorem MarkedParentTrace.detachedOriginalArc_power
    (i : Fin (detachedOrbitSize t c R-1)) :
    h.detachedOriginalArc c hc R i =
      (s.1.continuation ^ i.val)
        (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
  have main : ∀ (n : ℕ) (hn : n < detachedOrbitSize t c R-1),
      h.detachedOriginalArc c hc R ⟨n,hn⟩ =
        (s.1.continuation ^ n)
          (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩) := by
    intro n
    induction n with
    | zero => intro hn; rfl
    | succ n ih =>
      intro hn
      have hn' : n < detachedOrbitSize t c R-1 := by omega
      have hstep := h.detachedOriginalArc_successor c hc R ⟨n,hn'⟩ ⟨n+1,hn⟩ rfl
      rw [← hstep,ih hn',pow_succ',Equiv.Perm.mul_apply]
  exact main i.val i.isLt

theorem MarkedParentTrace.detachedOriginalWord_eq :
    List.ofFn (h.detachedOriginalArc c hc R) =
      List.ofFn (fun i : Fin (detachedOrbitSize t c R-1) =>
        (s.1.continuation ^ i.val)
          (h.detachedOriginalArc c hc R ⟨0,detachedOldOrbitSize_pos c R⟩)) := by
  congr 1
  funext i
  exact h.detachedOriginalArc_power c hc R i

end DirectGLSSW.HOMFLY
