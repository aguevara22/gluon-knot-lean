import SM.LinePolynomials

/-! Six distinct actual endpoints and unrestricted extension of finite tuples.
This is a geometric presentation of the actual line determinant, not a separate
axiomatic model of concurrence. -/

namespace SM

noncomputable section

variable {n : ℕ}

def sixEndpointMap (e f g : ZMod n) : Fin 6 → ZMod n :=
  ![e, e + 1, f, f + 1, g, g + 1]

theorem sixEndpointMap_injective [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g) :
    Function.Injective (sixEndpointMap e f g) := by
  obtain ⟨hfe, hfe1, hf1e, hf1e1⟩ := remote_endpoints e f hef
  obtain ⟨hge, hge1, hg1e, hg1e1⟩ := remote_endpoints e g heg
  obtain ⟨hgf, hgf1, hg1f, hg1f1⟩ := remote_endpoints f g hfg
  have he := next_ne_self e
  have hf := next_ne_self f
  have hg := next_ne_self g
  intro a b h
  fin_cases a <;> fin_cases b <;> simp_all [sixEndpointMap]

def extendSixEndpointTuple (e f g : ZMod n) (U : Fin 6 → Plane) : LabelledTuple n :=
  Function.extend (sixEndpointMap e f g) U (fun _ => (0, 0))

theorem extendSixEndpointTuple_apply [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (U : Fin 6 → Plane) (j : Fin 6) :
    extendSixEndpointTuple e f g U (sixEndpointMap e f g j) = U j :=
  (sixEndpointMap_injective e f g hef heg hfg).extend_apply U (fun _ => (0, 0)) j

theorem extendSixEndpointTuple_agree [Nontrivial (ZMod n)] (e f g : ZMod n)
    (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (U V : Fin 6 → Plane) (j : Fin 6) (hUV : ∀ k, k ≠ j → U k = V k)
    (v : ZMod n) (hv : v ≠ sixEndpointMap e f g j) :
    extendSixEndpointTuple e f g U v = extendSixEndpointTuple e f g V v := by
  classical
  by_cases hex : ∃ k, sixEndpointMap e f g k = v
  · obtain ⟨k, rfl⟩ := hex
    rw [extendSixEndpointTuple_apply e f g hef heg hfg,
      extendSixEndpointTuple_apply e f g hef heg hfg]
    apply hUV k
    intro h
    subst k
    exact hv rfl
  · simp [extendSixEndpointTuple, Function.extend_apply', hex]

def pointLineRow (a b : Plane) : Fin 3 → ℝ :=
  ![a.2 - b.2, b.1 - a.1, a.1 * b.2 - b.1 * a.2]

def sixPointConcurrence (U : Fin 6 → Plane) : ℝ :=
  (Matrix.of ![pointLineRow (U 0) (U 1), pointLineRow (U 2) (U 3),
    pointLineRow (U 4) (U 5)]).det

theorem sixPointConcurrence_formula (U : Fin 6 → Plane) :
    sixPointConcurrence U =
      ((U 0).2 - (U 1).2) * ((U 3).1 - (U 2).1) *
        ((U 4).1 * (U 5).2 - (U 5).1 * (U 4).2) -
      ((U 0).2 - (U 1).2) * ((U 2).1 * (U 3).2 - (U 3).1 * (U 2).2) *
        ((U 5).1 - (U 4).1) -
      ((U 1).1 - (U 0).1) * ((U 2).2 - (U 3).2) *
        ((U 4).1 * (U 5).2 - (U 5).1 * (U 4).2) +
      ((U 1).1 - (U 0).1) * ((U 2).1 * (U 3).2 - (U 3).1 * (U 2).2) *
        ((U 4).2 - (U 5).2) +
      ((U 0).1 * (U 1).2 - (U 1).1 * (U 0).2) * ((U 2).2 - (U 3).2) *
        ((U 5).1 - (U 4).1) -
      ((U 0).1 * (U 1).2 - (U 1).1 * (U 0).2) * ((U 3).1 - (U 2).1) *
        ((U 4).2 - (U 5).2) := by
  rw [sixPointConcurrence, Matrix.det_fin_three]
  rfl

theorem edgeLineRow_eq_pointLineRow (P : LabelledTuple n) (e : ZMod n) :
    edgeLineRow P e = pointLineRow (P e) (P (e + 1)) := rfl

theorem concurrenceDet_eq_sixPointConcurrence (P : LabelledTuple n) (e f g : ZMod n) :
    concurrenceDet P e f g = sixPointConcurrence (P ∘ sixEndpointMap e f g) := rfl

theorem concurrenceDet_extendSixEndpointTuple [Nontrivial (ZMod n)]
    (e f g : ZMod n) (hef : remote e f) (heg : remote e g) (hfg : remote f g)
    (U : Fin 6 → Plane) :
    concurrenceDet (extendSixEndpointTuple e f g U) e f g = sixPointConcurrence U := by
  rw [concurrenceDet_eq_sixPointConcurrence]
  congr 1
  funext j
  exact extendSixEndpointTuple_apply e f g hef heg hfg U j

theorem sixEndpointMap_mem (e f g : ZMod n) (j : Fin 6) :
    sixEndpointMap e f g j ∈ ({e, e + 1, f, f + 1, g, g + 1} : Finset (ZMod n)) := by
  classical
  fin_cases j <;> simp [sixEndpointMap]

theorem mem_sixEndpointMap_range (e f g : ZMod n) (v : ZMod n) :
    (∃ j, sixEndpointMap e f g j = v) ↔
      v ∈ ({e, e + 1, f, f + 1, g, g + 1} : Finset (ZMod n)) := by
  classical
  constructor
  · rintro ⟨j, rfl⟩
    exact sixEndpointMap_mem e f g j
  · intro h
    simp only [Finset.mem_insert, Finset.mem_singleton] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
    · exact ⟨5, rfl⟩

end

end SM
