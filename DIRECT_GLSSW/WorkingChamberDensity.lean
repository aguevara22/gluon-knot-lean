import WorkingAuxiliaryDomain
import CyclicGenericOpenness
import Mathlib.Topology.Connected.LocallyConnected

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceAuxiliaryWorkingDomain
open MvPolynomial Set Filter Topology

theorem generic_locus_isOpen (n : ℕ) :
    IsOpen {q : Fin n → PlanarPoint ℝ | CyclicGeneric q} := by
  apply isOpen_iff_mem_nhds.mpr
  intro q hq
  exact CyclicGenericLocality.eventually_cyclicGeneric q hq

/-- Actual connected components of the finite generic configuration locus are
open; no chamber-openness premise is added to the density theorem. -/
theorem generic_chamber_isOpen {n : ℕ} (q : Fin n → PlanarPoint ℝ) :
    IsOpen (connectedComponentIn {r : Fin n → PlanarPoint ℝ | CyclicGeneric r} q) :=
  (generic_locus_isOpen n).connectedComponentIn

/-- The explicit working locus is exactly one proper algebraic exclusion on
each actual generic chamber, and is open and dense relative to that chamber. -/
theorem workingAuxiliaryDomain_on_chamber {n : ℕ}
    (c : MvPolynomial (Fin n × Fin 2) ℝ)
    (hDense : Dense {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (hOpen : IsOpen {r : Fin n → PlanarPoint ℝ |
      eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0})
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    let U := connectedComponentIn {r : Fin n → PlanarPoint ℝ | CyclicGeneric r} q
    U ∩ workingAuxiliaryDomain c =
      U \ {r | eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c = 0} ∧
      IsOpen (U ∩ workingAuxiliaryDomain c) ∧
      U ⊆ closure (U ∩ workingAuxiliaryDomain c) ∧
      ∃ r ∈ U, eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 := by
  intro U
  have hU : IsOpen U := generic_chamber_isOpen q
  have hGeneric : ∀ r ∈ U, CyclicGeneric r :=
    fun _ hr => connectedComponentIn_subset _ q hr
  obtain ⟨hO,hD,hN⟩ := workingAuxiliaryDomain_on_open c hDense hOpen U hU hGeneric
  obtain ⟨r,hrU,hrc⟩ := hN ⟨q,mem_connectedComponentIn hq⟩
  exact ⟨workingAuxiliaryDomain_inter_eq_diff c U hGeneric,hO,hD,r,hrU,hrc.2⟩

end DirectGLSSW.SourceAuxiliaryWorkingDomain
