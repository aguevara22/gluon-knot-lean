import LiteralHistorySupportedTruncation

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceAuxiliaryWorkingDomain
open MvPolynomial Set

/-- An explicitly parameterized sufficient working locus. No polynomial is
selected by this definition, and no maximal admissibility claim is made. -/
def workingAuxiliaryDomain {n : ℕ} (c : MvPolynomial (Fin n × Fin 2) ℝ) :
    Set (Fin n → PlanarPoint ℝ) :=
  {r | CyclicGeneric r ∧ eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0}

theorem workingAuxiliaryDomain_eq {n : ℕ} (c : MvPolynomial (Fin n × Fin 2) ℝ) :
    workingAuxiliaryDomain c =
      {r | CyclicGeneric r ∧ eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} := rfl

theorem mem_workingAuxiliaryDomain_iff {n : ℕ}
    (c : MvPolynomial (Fin n × Fin 2) ℝ) (r : Fin n → PlanarPoint ℝ) :
    r ∈ workingAuxiliaryDomain c ↔
      CyclicGeneric r ∧ eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 := Iff.rfl

/-- The complement formula is literal and unconditional on properness. -/
theorem workingAuxiliaryDomain_inter_eq_diff {n : ℕ}
    (c : MvPolynomial (Fin n × Fin 2) ℝ) (U : Set (Fin n → PlanarPoint ℝ))
    (hU : ∀ r ∈ U, CyclicGeneric r) :
    U ∩ workingAuxiliaryDomain c =
      U \ {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c = 0} := by
  ext r
  constructor
  · exact fun h => ⟨h.1,h.2.2⟩
  · exact fun h => ⟨h.1,hU r h.1,h.2⟩

/-- Relative openness and density on every open subset of the generic locus.
The explicit closure inclusion is density relative to that subset, and the
last assertion witnesses that its excluded hypersurface is proper. -/
theorem workingAuxiliaryDomain_on_open {n : ℕ}
    (c : MvPolynomial (Fin n × Fin 2) ℝ)
    (hDense : Dense {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (hOpen : IsOpen {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (U : Set (Fin n → PlanarPoint ℝ)) (hU : IsOpen U)
    (hGeneric : ∀ r ∈ U, CyclicGeneric r) :
    IsOpen (U ∩ workingAuxiliaryDomain c) ∧
      U ⊆ closure (U ∩ workingAuxiliaryDomain c) ∧
      (U.Nonempty → (U ∩ workingAuxiliaryDomain c).Nonempty) := by
  have heq : U ∩ workingAuxiliaryDomain c =
      U ∩ {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} := by
    ext r
    constructor
    · exact fun h => ⟨h.1,h.2.2⟩
    · exact fun h => ⟨h.1,hGeneric r h.1,h.2⟩
  refine ⟨?_,?_,?_⟩
  · rw [heq]
    exact hU.inter hOpen
  · intro r hr
    apply mem_closure_iff.mpr
    intro V hV hrV
    obtain ⟨x,hxUV,hxc⟩ := hDense.inter_open_nonempty (U ∩ V) (hU.inter hV) ⟨r,hr,hrV⟩
    exact ⟨x,hxUV.2,hxUV.1,hGeneric x hxUV.1,hxc⟩
  · intro hne
    rw [heq]
    exact hDense.inter_open_nonempty U hU hne

end DirectGLSSW.SourceAuxiliaryWorkingDomain




