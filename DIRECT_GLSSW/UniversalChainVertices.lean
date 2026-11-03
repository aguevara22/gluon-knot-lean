import UniversalNoConcurrency
import UniversalCarrierChains
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.UniversalCarrierDomain
open AuxiliaryCarrierChart
variable {α : Type*} [DecidableEq α] {m : ℕ}
variable (L : α → CarrierLine) (hL : UniversalLocus L) (hT : PairTransverse L)
variable (f : Fin (m+1) → α) (hf : Function.Injective f) (V : Fin m → PlanarPoint ℝ)
variable (hinc : ∀ i, lineValue (L (f i.castSucc)) (V i)=0 ∧ lineValue (L (f i.succ)) (V i)=0)
include hL hT hf hinc

theorem chain_vertices_noncollinear (i j k : Fin m) (hij : i.val<j.val) (hjk : j.val<k.val) :
    planarDet (V j-V k) (V i-V k)≠0 := by
  have hd (v : Fin m) : lineDenominator (L (f v.castSucc)) (L (f v.succ))≠0 := by
    apply hT
    intro he
    have hh := congrArg Fin.val (hf he)
    simp at hh
  have hx (v : Fin m) : lineIntersection (L (f v.castSucc)) (L (f v.succ))=V v :=
    (lineIntersection_unique _ _ _ (hd v) (hinc v).1 (hinc v).2).symm
  intro hz
  apply hL _ _ _ (properPairs_consecutive f hf i j k hij hjk)
  apply (carrierTripleNumerator_zero_iff _ _ _ _ _ _ (hd i) (hd j) (hd k)).2
  rw [hx i,hx j,hx k]
  have he : planarDet (V j-V i) (V k-V i) = -planarDet (V j-V k) (V i-V k) := by
    dsimp [planarDet];ring
  rw [he,hz,neg_zero]

theorem chain_vertex_off_first (i : Fin m) (hi : 0 < i.val) :
    lineValue (L (f 0)) (V i)≠0 := by
  apply no_three_concurrent L hL hT (f i.castSucc) (f i.succ) (f 0)
  · intro he;have hh:=congrArg Fin.val (hf he);simp at hh
  · intro he;have hh:=congrArg Fin.val (hf he);simp at hh;omega
  · intro he;have hh:=congrArg Fin.val (hf he);simp at hh
  · exact (hinc i).1
  · exact (hinc i).2

theorem chain_vertices_distinct (i j : Fin m) (hij : i.val<j.val) : V i≠V j := by
  intro he
  apply no_three_concurrent L hL hT (f i.castSucc) (f i.succ) (f j.succ)
    (fun h => by have hh:=congrArg Fin.val (hf h);simp at hh)
    (fun h => by have hh:=congrArg Fin.val (hf h);simp only [Fin.coe_castSucc,Fin.val_succ] at hh;omega)
    (fun h => by have hh:=congrArg Fin.val (hf h);simp only [Fin.val_succ] at hh;omega)
    (V i) (hinc i).1 (hinc i).2
  rw [he]
  exact (hinc j).2

omit [DecidableEq α] hL hT hf hinc in
/-- Literal physical first-line incidence turns off-carrier incidence into the
nonzero planar determinant required by affine cursor avoidance. -/
theorem first_line_off_det (K : CarrierLine) (p q x : PlanarPoint ℝ)
    (hp : lineValue K p=0) (hq : lineValue K q=0) (hne : q≠p)
    (hoff : lineValue K x≠0) : planarDet (q-p) (x-p)≠0 := by
  intro hz
  have hz' : planarDet (x-q) (p-q)=0 := by
    convert hz using 1 <;> simp only [planarDet,Prod.fst_sub,Prod.snd_sub] <;> ring
  obtain ⟨s,hs⟩ := CursorWallTransport.collinear_parameter p x q hne hz'
  apply hoff
  rw [hs]
  have hh : lineValue K (p+s • (q-p))=(1-s)*lineValue K p+s*lineValue K q := by
    dsimp [lineValue,planarDet]
    ring
  rw [hh,hp,hq]
  ring
end DirectGLSSW.UniversalCarrierDomain
