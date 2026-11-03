import FiniteSecantAxis

set_option autoImplicit false
namespace DirectGLSSW.HOMFLY.PrincipalTurning
noncomputable section
open scoped Classical

/-- Literal adjacent points in the actual finite cut set. -/
def secantAxisAdjacent {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (a b : ℝ) : Prop :=
  a ∈ secantAxisCuts T C ∧ b ∈ secantAxisCuts T C ∧ a<b ∧
    ∀ u ∈ secantAxisCuts T C, a<u → u<b → False

def secantAxisCells {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D) : Finset (ℝ × ℝ) :=
  ((secantAxisCuts T C).product (secantAxisCuts T C)).filter
    (fun ab => secantAxisAdjacent T C ab.1 ab.2)

theorem secantAxisCuts_quarter {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (k : ℕ) (hk : k ≤ 4*componentArcLength D (T.baseArc C).val) :
    (k : ℝ)/4 ∈ secantAxisCuts T C := by
  apply Finset.mem_union_left
  apply Finset.mem_image.mpr
  exact ⟨k,by simpa only [Finset.mem_range,Nat.lt_succ_iff] using hk,rfl⟩

theorem secantAxisAdjacent_width {D : PLLinkDiagram} (T : BasedTraversal D) (C : diagramComponent D)
    (a b : ℝ) (h : secantAxisAdjacent T C a b) : b-a ≤ 1/4 := by
  classical
  have ha := secantAxisCuts_bounds T C a h.1
  have hb := secantAxisCuts_bounds T C b h.2.1
  have hf : 0 ≤ Int.floor (4*a) := Int.floor_nonneg.mpr (by linarith [ha.1])
  let k := (Int.floor (4*a)).toNat+1
  have hcast : (k : ℝ) = (Int.floor (4*a) : ℝ)+1 := by
    dsimp [k]
    have hc : (((Int.floor (4*a)).toNat : ℕ) : ℤ) = Int.floor (4*a) := Int.toNat_of_nonneg hf
    have hr : ((Int.floor (4*a)).toNat : ℝ) = (Int.floor (4*a) : ℝ) := by exact_mod_cast hc
    push_cast
    rw [hr]
  have hdec := Int.floor_add_fract (4*a)
  have hlow : a < (k : ℝ)/4 := by rw [hcast]; linarith [Int.fract_lt_one (4*a)]
  have hhigh : (k : ℝ)/4 ≤ a+1/4 := by rw [hcast]; linarith [Int.fract_nonneg (4*a)]
  by_contra hn
  have hgap : a+1/4 < b := by linarith
  have hkreal : (k : ℝ) ≤ 4*(componentArcLength D (T.baseArc C).val : ℝ) := by linarith [hb.2]
  have hk : k ≤ 4*componentArcLength D (T.baseArc C).val := by exact_mod_cast hkreal
  exact h.2.2.2 _ (secantAxisCuts_quarter T C k hk) hlow (lt_of_le_of_lt hhigh hgap)

/-- If a zero center lies in an adjacent cell, that cell stays inside any
actual cut-bounded open window around the center. Used for removed star cells. -/
theorem secantAxisAdjacent_window_containment {D : PLLinkDiagram}
    (T : BasedTraversal D) (C : diagramComponent D) (a b L R v : ℝ)
    (h : secantAxisAdjacent T C a b) (hL : L ∈ secantAxisCuts T C) (hR : R ∈ secantAxisCuts T C)
    (hv : v ∈ Set.Icc a b) (hLv : L<v) (hvR : v<R) : L≤a ∧ b≤R := by
  constructor
  · by_contra hn
    exact h.2.2.2 L hL (lt_of_not_ge hn) (by linarith [hv.2])
  · by_contra hn
    exact h.2.2.2 R hR (by linarith [hv.1]) (lt_of_not_ge hn)

/-- Each actual adjacent cell lies on one closed uniform affine arc cell,
including an original knot when it is the right endpoint. -/
theorem basedUniformPLCurve_axis_cell {D : PLLinkDiagram} (T : BasedTraversal D)
    (C : diagramComponent D) (a b t : ℝ) (h : secantAxisAdjacent T C a b)
    (ht : t ∈ Set.Icc a b) :
    basedUniformPLCurve T C t =
      affinePoint (D.vertexPoint (D.arcSource ((D.continuation ^ Int.floor (a+1/2)) (T.baseArc C).val)))
        (D.vertexPoint (D.arcTarget ((D.continuation ^ Int.floor (a+1/2)) (T.baseArc C).val)))
        (t+1/2-(Int.floor (a+1/2) : ℝ)) := by
  let m := componentArcLength D (T.baseArc C).val
  let n := (Int.floor (a+1/2)).toNat
  have ha := secantAxisCuts_bounds T C a h.1
  have hb := secantAxisCuts_bounds T C b h.2.1
  have hn := basedUniform_address_bounds m a ha
  have hncast : (n : ℝ) = (Int.floor (a+1/2) : ℝ) := by exact_mod_cast hn.1
  have hfloor := Int.floor_le (a+1/2)
  have hlt := Int.lt_floor_add_one (a+1/2)
  have hupper : b+1/2 ≤ (Int.floor (a+1/2) : ℝ)+1 := by
    by_cases hnm : n<m
    · by_contra hh
      have hx := secantAxisCuts_original_knot T C n hnm
      exact h.2.2.2 _ hx (by rw [hncast]; linarith) (by rw [hncast]; linarith)
    · have heq : n=m := by omega
      rw [← hncast,heq]
      linarith [hb.2]
  have hu : t+1/2-(Int.floor (a+1/2) : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by
    constructor <;> linarith [ht.1,ht.2]
  have hc := uniformPLCurve_arc_cell D (T.baseArc C).val (Int.floor (a+1/2)) _ hu
  have htime : (Int.floor (a+1/2) : ℝ)+(t+1/2-(Int.floor (a+1/2) : ℝ))=t+1/2 := by ring
  rw [htime] at hc
  exact hc

end
end DirectGLSSW.HOMFLY.PrincipalTurning




