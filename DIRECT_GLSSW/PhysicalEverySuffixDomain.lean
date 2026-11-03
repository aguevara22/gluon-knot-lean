import PhysicalAllSuffixDomain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive Split AuxiliaryCarrierChart Filter Topology

/-- Natural-index version: one original configuration works for every literal
suffix and every cut size. The only index premise is the exact size equation. -/
theorem exists_nearby_every_literal_suffix_domains {N : ℕ}
    (q : Fin (N+2) → PlanarPoint ℝ) (hQ : Regular q)
    (hG1 : cyclicNoncollinear q) (hAux : ClosedAuxiliary q hQ)
    (V : Set (Fin (N+2) → PlanarPoint ℝ)) (hV : V∈𝓝 q) :
    ∃ r∈V, (∃ hR : Regular r, ClosedAuxiliary r hR) ∧ cyclicNoncollinear r ∧
      ∀ (k a b : ℕ) (hdim : N=k+(a+b)),
        MatchedAllFirstEvents (dropWord q hdim) (dropWord_regular q hdim hQ)
          (dropWord r hdim) := by
  obtain ⟨r,hrV,hrA,hrG,hr⟩ := exists_nearby_all_suffix_domains q hQ hG1 hAux V hV
  refine ⟨r,hrV,hrA,hrG,?_⟩
  intro k a b hdim
  let t : SuffixShape N := ⟨(⟨k,by omega⟩,⟨a,by omega⟩,⟨b,by omega⟩),hdim⟩
  exact hr t
end DirectGLSSW.ActiveArc.OpenCarrier
