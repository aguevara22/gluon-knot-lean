import CanonicalInventoryCharacterizations

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.CyclicCarrierClearing
open AuxiliaryCarrierChart UniversalCarrierDomain MvPolynomial Set

/-- The polynomial hypersurface complement in literal original vertex space,
and an admissible augmented line in every actual open line window. -/
theorem exists_original_vertex_coefficient_and_windows {n : ℕ}
    (q : Fin n → PlanarPoint ℝ) (hq : CyclicGeneric q) :
    ∃ c : MvPolynomial (Fin n × Fin 2) ℝ, c ≠ 0 ∧
      Dense {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      IsOpen {r : Fin n → PlanarPoint ℝ |
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0} ∧
      ∀ r : Fin n → PlanarPoint ℝ,
        eval (fun p => if p.2 = 0 then (r p.1).1 else (r p.1).2) c ≠ 0 →
        ∀ V : Set CarrierLine, IsOpen V → V.Nonempty → ∃ K ∈ V,
          PairTransverse (canonicalAugmentedCarrier r K) ∧
          UniversalLocus (canonicalAugmentedCarrier r K) ∧
          allCycleSecantExclusions (canonicalAugmentedCarrier r K) := by
  obtain ⟨c,hc,hD,hO,hW⟩ := exists_original_coefficient_for_all_auxiliary_windows q hq
  let flat : (Fin n → PlanarPoint ℝ) → (Fin n × Fin 2 → ℝ) :=
    fun r p => if p.2 = 0 then (r p.1).1 else (r p.1).2
  let unflat : (Fin n × Fin 2 → ℝ) → (Fin n → PlanarPoint ℝ) :=
    fun x i => (x (i,0),x (i,1))
  have hf : Continuous flat := by
    apply continuous_pi
    intro p
    dsimp [flat]
    split_ifs <;> fun_prop
  have hu : Continuous unflat := by unfold unflat; fun_prop
  have huf (r : Fin n → PlanarPoint ℝ) : unflat (flat r) = r := by
    funext i
    simp [unflat,flat]
  have hfu (x : Fin n × Fin 2 → ℝ) : flat (unflat x) = x := by
    funext p
    rcases p with ⟨i,j⟩
    fin_cases j <;> simp [flat,unflat]
  have hDv : Dense {r : Fin n → PlanarPoint ℝ | eval (flat r) c ≠ 0} := by
    rw [dense_iff_inter_open]
    intro U hU hUn
    obtain ⟨r,hr⟩ := hUn
    have hpre : IsOpen (unflat ⁻¹' U) := hU.preimage hu
    have hprene : (unflat ⁻¹' U).Nonempty := ⟨flat r,by simpa only [Set.mem_preimage,huf] using hr⟩
    obtain ⟨x,hxU,hx⟩ := hD.inter_open_nonempty _ hpre hprene
    exact ⟨unflat x,hxU,by simpa only [Set.mem_setOf_eq,hfu] using hx⟩
  have hOv : IsOpen {r : Fin n → PlanarPoint ℝ | eval (flat r) c ≠ 0} := hO.preimage hf
  refine ⟨c,hc,hDv,hOv,?_⟩
  intro r hr V hV hVn
  let line : (Fin 3 → ℝ) → CarrierLine := fun y => ((y 0,y 1),y 2)
  have hl : Continuous line := by unfold line; fun_prop
  have hpre : IsOpen (line ⁻¹' V) := hV.preimage hl
  obtain ⟨K,hK⟩ := hVn
  let y₀ : Fin 3 → ℝ := fun i => if i = 0 then K.1.1 else if i = 1 then K.1.2 else K.2
  have hy₀ : line y₀ = K := by simp [line,y₀]
  obtain ⟨y,hy,hinv⟩ := hW (flat r) hr (line ⁻¹' V) hpre ⟨y₀,by simpa only [Set.mem_preimage,hy₀] using hK⟩
  have hv : jointVertices (Sum.elim (flat r) y) = r := by funext i; simp [jointVertices,flat]
  have hline : jointLine (Sum.elim (flat r) y) = line y := rfl
  exact ⟨line y,hy,by simpa only [hv,hline] using hinv⟩

end DirectGLSSW.CyclicCarrierClearing

