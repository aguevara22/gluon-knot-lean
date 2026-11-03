import PhysicalSuffixCarrierProjection
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW AuxiliaryCarrierChart

def firstSuffixVertex {N M : ℕ} (h : N=M+1) (i : Fin (M+2)) : Fin (N+2) :=
  ⟨i.val+1,by omega⟩
def firstSuffixEdge {N M : ℕ} (h : N=M+1) (i : Fin (M+1)) : Fin (N+1) :=
  ⟨i.val+1,by omega⟩
def firstSuffixWord {N M : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (h : N=M+1) :
    Fin (M+2) → PlanarPoint ℝ := fun i => q (firstSuffixVertex h i)
def firstSuffixCarriers {N M : ℕ} (h : N=M+1)
    (L : Fin (N+1) ⊕ Unit → CarrierLine) : Fin (M+1) ⊕ Unit → CarrierLine :=
  fun i => L (i.map (firstSuffixEdge h) id)

lemma firstSuffixEdge_castSucc {N M : ℕ} (h : N=M+1) (e : Fin (M+1)) :
    firstSuffixVertex h e.castSucc = (firstSuffixEdge h e).castSucc := rfl
lemma firstSuffixEdge_succ {N M : ℕ} (h : N=M+1) (e : Fin (M+1)) :
    firstSuffixVertex h e.succ = (firstSuffixEdge h e).succ := rfl

lemma firstSuffixEdge_injective {N M : ℕ} (h : N=M+1) : Function.Injective (firstSuffixEdge h) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp [firstSuffixEdge] at this
  omega
lemma firstSuffixVertex_injective {N M : ℕ} (h : N=M+1) : Function.Injective (firstSuffixVertex h) := by
  intro i j hij
  apply Fin.ext
  have := congrArg Fin.val hij
  dsimp [firstSuffixVertex] at this
  omega

lemma firstSuffixWord_regular {N M : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=M+1) (hR : Regular q) : Regular (firstSuffixWord q h) where
  edge_nonzero e := hR.edge_nonzero (firstSuffixEdge h e)
  transverse e f hef x he hf := hR.transverse (firstSuffixEdge h e) (firstSuffixEdge h f)
    (fun hh => hef (firstSuffixEdge_injective h hh)) x he hf
  noTriple e f g x hef hfg hge hh := hR.noTriple
    (firstSuffixEdge h e) (firstSuffixEdge h f) (firstSuffixEdge h g) x
    (fun heq => hef (firstSuffixEdge_injective h heq))
    (fun heq => hfg (firstSuffixEdge_injective h heq))
    (fun heq => hge (firstSuffixEdge_injective h heq)) hh
  anchor_avoid e i hil hir hi := hR.anchor_avoid (firstSuffixEdge h e) (firstSuffixVertex h i)
    (fun heq => hil (firstSuffixVertex_injective h heq))
    (fun heq => hir (firstSuffixVertex_injective h heq)) hi

lemma firstSuffixWord_G1 {N M : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=M+1) (hG : cyclicNoncollinear q) : cyclicNoncollinear (firstSuffixWord q h) := by
  intro i j k hij hjk hki
  exact hG (firstSuffixVertex h i) (firstSuffixVertex h j) (firstSuffixVertex h k)
    (fun heq => hij (firstSuffixVertex_injective h heq))
    (fun heq => hjk (firstSuffixVertex_injective h heq))
    (fun heq => hki (firstSuffixVertex_injective h heq))

lemma firstSuffixWord_continuous {N M : ℕ} (h : N=M+1) :
    Continuous (fun q : Fin (N+2) → PlanarPoint ℝ => firstSuffixWord q h) :=
  continuous_pi (fun i => continuous_apply _)

lemma firstSuffixCarriers_continuous {N M : ℕ} (h : N=M+1) : Continuous (firstSuffixCarriers h) :=
  continuous_pi (fun i => continuous_apply _)
lemma firstSuffixCarriers_isOpenMap {N M : ℕ} (h : N=M+1) : IsOpenMap (firstSuffixCarriers h) := by
  subst N
  exact suffixCarrierProjection_isOpenMap

lemma firstSuffixCarriers_chart {N M : ℕ} (q : Fin (N+2) → PlanarPoint ℝ) (h : N=M+1) :
    firstSuffixCarriers h (openChartLines q) = openChartLines (firstSuffixWord q h) := by
  funext i
  cases i with
  | inl e => rfl
  | inr u =>
    simp only [firstSuffixCarriers,Sum.map_inr,openChartLines,Sum.elim_inr,terminalLine,firstSuffixWord]
    have hlast : firstSuffixVertex h ⟨M+1,by omega⟩ = (⟨N+1,by omega⟩ : Fin (N+2)) := Fin.ext (by dsimp [firstSuffixVertex]; omega)
    have hprev : firstSuffixVertex h ⟨M,by omega⟩ = (⟨N,by omega⟩ : Fin (N+2)) := Fin.ext (by dsimp [firstSuffixVertex]; omega)
    rw [hlast,hprev]

end DirectGLSSW.ActiveArc.OpenCarrier
