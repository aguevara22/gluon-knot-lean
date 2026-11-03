import PhysicalTwoStageDomain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW AuxiliaryCarrierChart Topology

def dropVertex {N M k : ℕ} (h : N=k+M) (i : Fin (M+2)) : Fin (N+2) := ⟨k+i.val,by omega⟩
def dropEdge {N M k : ℕ} (h : N=k+M) (i : Fin (M+1)) : Fin (N+1) := ⟨k+i.val,by omega⟩
def dropWord {N M k : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (h : N=k+M) :
    Fin (M+2) → PlanarPoint ℝ := fun i => q (dropVertex h i)
def dropCarriers {N M k : ℕ} (h : N=k+M) (L : Fin (N+1) ⊕ Unit → CarrierLine) :
    Fin (M+1) ⊕ Unit → CarrierLine := fun i => L (i.map (dropEdge h) id)

private def dropCarrierSplit {N M k : ℕ} (h : N=k+M) :
    (Fin (N+1) ⊕ Unit → CarrierLine) ≃ₜ
      (Fin k → CarrierLine) × (Fin (M+1) ⊕ Unit → CarrierLine) where
  toFun L := ((fun i => L (Sum.inl ⟨i.val,by omega⟩)),dropCarriers h L)
  invFun P := Sum.elim (fun e => if he : e.val<k then P.1 ⟨e.val,he⟩
    else P.2 (Sum.inl ⟨e.val-k,by omega⟩)) (fun u => P.2 (Sum.inr u))
  left_inv L := by
    funext i
    cases i with
    | inl e =>
      dsimp [dropCarriers]
      split_ifs with he
      · rfl
      · congr 2
        apply Fin.ext
        dsimp [dropEdge]
        omega
    | inr u => rfl
  right_inv P := by
    apply Prod.ext
    · funext i
      simp only [Sum.elim_inl,Fin.val_mk,dif_pos i.isLt]
    · funext i
      cases i with
      | inl e =>
        dsimp [dropCarriers,dropEdge]
        rw [dif_neg (by omega)]
        apply congrArg P.2
        apply congrArg Sum.inl
        apply Fin.ext
        dsimp
        omega
      | inr u => rfl
  continuous_toFun := by
    apply Continuous.prodMk
    · exact continuous_pi (fun i => continuous_apply _)
    · exact continuous_pi (fun i => continuous_apply _)
  continuous_invFun := by
    apply continuous_pi
    intro i
    cases i with
    | inl e =>
      by_cases he : e.val<k
      · simp only [Sum.elim_inl,dif_pos he]
        exact (continuous_apply _).comp continuous_fst
      · simp only [Sum.elim_inl,dif_neg he]
        exact (continuous_apply _).comp continuous_snd
    | inr u => exact (continuous_apply _).comp continuous_snd

theorem dropCarriers_continuous {N M k : ℕ} (h : N=k+M) : Continuous (dropCarriers h) :=
  continuous_pi (fun i => continuous_apply _)
theorem dropCarriers_isOpenMap {N M k : ℕ} (h : N=k+M) : IsOpenMap (dropCarriers h) :=
  isOpenMap_snd.comp (dropCarrierSplit h).isOpenMap

lemma dropEdge_injective {N M k : ℕ} (h : N=k+M) : Function.Injective (dropEdge h) := by
  intro i j heq
  apply Fin.ext
  have := congrArg Fin.val heq
  dsimp [dropEdge] at this
  omega
lemma dropVertex_injective {N M k : ℕ} (h : N=k+M) : Function.Injective (dropVertex h) := by
  intro i j heq
  apply Fin.ext
  have := congrArg Fin.val heq
  dsimp [dropVertex] at this
  omega

lemma dropWord_regular {N M k : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=k+M) (hR : Regular q) : Regular (dropWord q h) where
  edge_nonzero e := hR.edge_nonzero (dropEdge h e)
  transverse e f hef x he hf := hR.transverse (dropEdge h e) (dropEdge h f)
    (fun hh => hef (dropEdge_injective h hh)) x he hf
  noTriple e f g x hef hfg hge hh := hR.noTriple (dropEdge h e) (dropEdge h f) (dropEdge h g) x
    (fun heq => hef (dropEdge_injective h heq))
    (fun heq => hfg (dropEdge_injective h heq))
    (fun heq => hge (dropEdge_injective h heq)) hh
  anchor_avoid e i hil hir hi := hR.anchor_avoid (dropEdge h e) (dropVertex h i)
    (fun heq => hil (dropVertex_injective h heq))
    (fun heq => hir (dropVertex_injective h heq)) hi

lemma dropWord_G1 {N M k : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=k+M) (hG : cyclicNoncollinear q) : cyclicNoncollinear (dropWord q h) := by
  intro i j l hij hjl hli
  exact hG (dropVertex h i) (dropVertex h j) (dropVertex h l)
    (fun heq => hij (dropVertex_injective h heq))
    (fun heq => hjl (dropVertex_injective h heq))
    (fun heq => hli (dropVertex_injective h heq))

lemma dropWord_continuous {N M k : ℕ} (h : N=k+M) :
    Continuous (fun q : Fin (N+2) → PlanarPoint ℝ => dropWord q h) :=
  continuous_pi (fun i => continuous_apply _)

lemma dropCarriers_chart {N M k : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (h : N=k+M) :
    dropCarriers h (openChartLines q) = openChartLines (dropWord q h) := by
  funext i
  cases i with
  | inl e => rfl
  | inr u =>
    simp only [dropCarriers,Sum.map_inr,openChartLines,Sum.elim_inr,terminalLine,dropWord]
    have hlast : dropVertex h ⟨M+1,by omega⟩ = (⟨N+1,by omega⟩ : Fin (N+2)) :=
      Fin.ext (by dsimp [dropVertex]; omega)
    have hprev : dropVertex h ⟨M,by omega⟩ = (⟨N,by omega⟩ : Fin (N+2)) :=
      Fin.ext (by dsimp [dropVertex]; omega)
    rw [hlast,hprev]

lemma dropWord_eq_literal_suffix {k M : ℕ} (q : Fin (k+M+2) → PlanarPoint ℝ) :
    dropWord q (show k+M=k+M from rfl) = Split.suffix (a:=k) (b:=M) q := by
  funext i
  change q (dropVertex _ i) = q (Split.vertex i)
  congr 1
end DirectGLSSW.ActiveArc.OpenCarrier
