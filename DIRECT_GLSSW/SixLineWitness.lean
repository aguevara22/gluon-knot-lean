import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Int.Basic
import Mathlib.Data.Fintype.Pi

set_option autoImplicit false
set_option maxRecDepth 20000
set_option maxHeartbeats 800000

/- Internal finite witness candidate. UNCOMPILED; not a density theorem. -/
namespace DirectGLSSW.AuxiliaryDeterminants

def witnessParameter : Fin 6 → ℤ := ![0, 1, 3, 7, 12, 20]

def witnessPair : Fin 15 → Fin 6 × Fin 6 :=
  ![(0, 1), (0, 2), (0, 3), (0, 4), (0, 5),
    (1, 2), (1, 3), (1, 4), (1, 5),
    (2, 3), (2, 4), (2, 5), (3, 4), (3, 5), (4, 5)]

def witnessPoint (e : Fin 15) : ℤ × ℤ :=
  let t := witnessParameter (witnessPair e).1
  let u := witnessParameter (witnessPair e).2
  (-(t + u), -(t * u))

def witnessIncident (e : Fin 15) (i : Fin 6) : Prop :=
  i = (witnessPair e).1 ∨ i = (witnessPair e).2

instance (e : Fin 15) (i : Fin 6) : Decidable (witnessIncident e i) :=
  inferInstanceAs (Decidable (i = (witnessPair e).1 ∨ i = (witnessPair e).2))

def witnessTripleDet (e f g : Fin 15) : ℤ :=
  (witnessPoint f).1 * (witnessPoint g).2 -
  (witnessPoint f).1 * (witnessPoint e).2 -
  (witnessPoint e).1 * (witnessPoint g).2 -
  (witnessPoint f).2 * (witnessPoint g).1 +
  (witnessPoint f).2 * (witnessPoint e).1 +
  (witnessPoint e).2 * (witnessPoint g).1

theorem witnessPair_enumerates :
    ∀ i j : Fin 6, i < j → ∃ e : Fin 15, witnessPair e = (i, j) := by
  decide

theorem witnessPair_injective : Function.Injective witnessPair := by
  decide

theorem witnessParameter_injective : Function.Injective witnessParameter := by
  decide

theorem witnessPoint_on_incident_line :
    ∀ (e : Fin 15) (i : Fin 6), witnessIncident e i →
      (witnessPoint e).2 = witnessParameter i * (witnessPoint e).1 +
        witnessParameter i * witnessParameter i := by
  decide

theorem witnessTripleDet_zero_iff :
    ∀ e f g : Fin 15, e ≠ f → f ≠ g → e ≠ g →
      (witnessTripleDet e f g = 0 ↔
        ∃ i : Fin 6, witnessIncident e i ∧ witnessIncident f i ∧ witnessIncident g i) := by
  decide

end DirectGLSSW.AuxiliaryDeterminants






