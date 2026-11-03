import SourceBoundaryPositiveOrdinary
import ActiveArcSingletonWords
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceBoundaryCurrent
open DirectGLSSW ActiveArc ActiveArc.Cursor ActiveArc.Split ActiveArc.SingletonWords
open ActiveArc.Primitive EndpointEventGeometry
private theorem congr_amplitude {n : ℕ} (P Q : Fin n → PlanarPoint ℝ)
    (h : P=Q) (hP : CyclicGeneric P) (hQ : CyclicGeneric Q) :
    polygonAmplitude P hP=polygonAmplitude Q hQ := by cases h; rfl

/-- Point genericity excludes a virtual first-row secant event everywhere
strictly before the terminal point of the first physical edge. -/
theorem first_edge_virtual_det_ne_zero {n : ℕ}
    (q : Fin (n+2) → PlanarPoint ℝ) (hG : cyclicNoncollinear q)
    (j : Fin (n+2)) (hj : 1 < j.val) (t : ℝ) (ht : t < 1) :
    planarDet (q 1-q j) (affinePoint (q 0) (q 1) t-q j) ≠ 0 := by
  have hD : planarDet (q 1-q j) (q 0-q j) ≠ 0 :=
    hG 0 1 j (by intro h; have := congrArg Fin.val h; simp at this) (by intro h; have := congrArg Fin.val h; simp at this; omega)
      (by intro h; have := congrArg Fin.val h; simp at this; omega)
  have heq : planarDet (q 1-q j) (affinePoint (q 0) (q 1) t-q j) =
      (1-t)*planarDet (q 1-q j) (q 0-q j) := by
    simp only [planarDet,affinePoint,Prod.fst_sub,Prod.snd_sub]
    ring
  rw [heq]
  exact mul_ne_zero (ne_of_gt (by linarith)) hD

/-- Literal unsmoothed physical boundary-b source case. hF is only the finite
nonphysical secant exclusion at the event, part of the standing point-generic
auxiliary domain. Virtual first-row pairs are derived from G1, physical
transversality from Regular, and child genericity from ClosedAuxiliary. -/
theorem exists_source_physical_boundary_b
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : c.val.1 = 0) (hcut : c.val.2.val=a)
    (hRI : GLSSWRootIndependence) (hG : cyclicNoncollinear q)
    (hAux : ClosedAuxiliary q hR)
    (hF : ∀ i j : Fin (a+b+2), 1 < i.val → i.val < j.val →
      (i.val≠a ∨ j.val≠a+1) →
      planarDet (q i-q j) (ActiveArc.crossingPoint q c-q j)≠0) :
    let W : ℕ → PlanarPoint ℝ := fun i => if i=0 then ActiveArc.crossingPoint q c else
      q ⟨i%(a+b+2),Nat.mod_lt _ (by omega)⟩
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ ε : ℝ, 0 < ε → ε < ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (q 1-q 0) ε) (a+b+1) ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (q 1-q 0) (-ε)) (a+b+1) ∧
      ∀ j, a < j → j≤a+b+1 →
      ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W (q 1-q 0) ε)) 0 j -
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W (q 1-q 0) (-ε))) 0 j =
      scalarSignValue (planarDet (q 1-q 0) (q c.val.2.succ-q c.val.2.castSucc)) *
        polygonAmplitude (child q hR c hc hcut)
          (child_cyclicGeneric_of_closedAuxiliary q hR c hc hcut hAux) *
        ordinaryCurrent (fun _ _ _ => -1)
          (polygonSignArray (fun i => if i=0 then W 0 else W (a+i))) 0 (j-a) := by
  intro W
  have ha : 0 < a := cut_positive q c hcut
  have hw0 : W 0=ActiveArc.crossingPoint q c := by simp [W]
  have hw (i : ℕ) (hi : 0 < i) (hin : i < a+b+2) :
      W i=q ⟨i,hin⟩ := by simp [W,Nat.ne_of_gt hi,Nat.mod_eq_of_lt hin]
  have heqa : (⟨a,by omega⟩ : Fin (a+b+2))=c.val.2.castSucc := by
    apply Fin.ext; simpa using hcut.symm
  have heqa1 : (⟨a+1,by omega⟩ : Fin (a+b+2))=c.val.2.succ := by
    apply Fin.ext; simp [hcut]
  have hside : W (a+1)-W a=q c.val.2.succ-q c.val.2.castSucc := by
    rw [hw (a+1) (by omega) (by omega),hw a ha (by omega),heqa,heqa1]
  have hfirst : ActiveArc.crossingPoint q c=affinePoint (q 0) (q 1) (leftParameter q c) := by
    simpa only [hc] using (leftParameter_spec q c).2.2
  have hone : (⟨1,by omega⟩ : Fin (a+b+2)) = 1 := by apply Fin.ext; simp
  have hdir : W 1-W 0=(1-leftParameter q c) • (q 1-q 0) := by
    rw [hw 1 (by omega) (by omega),hone,hw0,hfirst]
    ext  <;> simp only [affinePoint,Prod.fst_sub,Prod.snd_sub,Prod.smul_fst,Prod.smul_snd,smul_eq_mul]  <;> ring
  have htr : planarDet (q 1-q 0) (W (a+1)-W a)≠0 := by
    rw [hside]
    have H := hR.transverse c.val.1 c.val.2 (ne_of_lt c.property.1)
      (ActiveArc.crossingPoint q c) (crossingPoint_mem q c).1 (crossingPoint_mem q c).2
    simpa only [hc] using H
  have hcross : W 0=affinePoint (W a) (W (a+1)) (rightParameter q c) := by
    rw [hw0,hw a ha (by omega),hw (a+1) (by omega) (by omega),heqa,heqa1]
    exact (rightParameter_spec q c).2.2
  have hiso : ∀ i j l, i < j → j < l → l≤a+b+1 →
      (i≠0 ∨ j≠a ∨ l≠a+1) → polygonHDet W i j l≠0 := by
    intro i j l hij hjl hl hex
    have hj : 0 < j := by omega
    have hlp : 0 < l := by omega
    unfold polygonHDet
    rw [hw j hj (by omega),hw l hlp (by omega)]
    by_cases hi : i=0
    · subst i
      rw [hw0]
      by_cases hj1 : j=1
      · subst j
        rw [hfirst]
        exact first_edge_virtual_det_ne_zero q hG ⟨l,by omega⟩ (by change 1 < l; omega)
          _ (leftParameter_spec q c).2.1
      · apply hF ⟨j,by omega⟩ ⟨l,by omega⟩ (by change 1 < j; omega) hjl
        rcases hex with h|h|h
        · exact False.elim (h rfl)
        · exact Or.inl h
        · exact Or.inr h
    · rw [hw i (Nat.pos_of_ne_zero hi) (by omega)]
      apply hG
      all_goals intro he; have hv := congrArg Fin.val he; dsimp at hv; omega
  have hfun : (fun i : Fin (a+1) => W i.val)=child q hR c hc hcut := by
    funext i
    by_cases hi : i=0
    · subst i; simp [hw0]
    · have hv : 0 < i.val := by
        apply Nat.pos_of_ne_zero
        intro hz
        apply hi
        apply Fin.ext
        simpa using hz
      rw [hw i.val hv (by omega),child_nonzero q hR c hc hcut i hi]
      rfl
  have hQ : CyclicGeneric (fun i : Fin (a+1) => W i.val) := by
    rw [hfun]; exact child_cyclicGeneric_of_closedAuxiliary q hR c hc hcut hAux
  obtain ⟨ρ,hρ,hjump⟩ := exists_ordinary_boundary_positive_direction hRI W
    (q 1-q 0) (1-leftParameter q c) (by linarith [(leftParameter_spec q c).2.1]) hdir
    (a+b+1) a (by omega) (rightParameter q c) (rightParameter_spec q c).1
    (rightParameter_spec q c).2.1 hcross htr hiso hQ
  refine ⟨ρ,hρ,?_⟩
  intro ε he her
  obtain ⟨hp,hm,H⟩ := hjump ε he her
  refine ⟨hp,hm,?_⟩
  intro j haj hjN
  have H' := H j haj hjN
  have hamp : polygonAmplitude (fun i : Fin (a+1) => W i.val) hQ =
      polygonAmplitude (child q hR c hc hcut)
        (child_cyclicGeneric_of_closedAuxiliary q hR c hc hcut hAux) := by
    apply congr_amplitude _ _ hfun
  rw [hside,hamp] at H' 
  exact H'



end DirectGLSSW.SourceBoundaryCurrent
