import PathTransAngleSplit
import ActualComponentWord
import UnitLoopPositionalIndex
import SourcePLWindingIndex
import ComplexPLLoop

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Topology unitInterval

namespace DirectGLSSW.HOMFLY.PrincipalTurning

def orbitWordSource (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℕ) : ℂ :=
  Complex.equivRealProd.symm
    (D.vertexPoint (D.arcSource ((D.continuation ^ k) e)))

def orbitWordTarget (D : PLLinkDiagram) (e : Fin D.nArc) (k : ℕ) : ℂ :=
  Complex.equivRealProd.symm
    (D.vertexPoint (D.arcTarget ((D.continuation ^ k) e)))

/-- The argument increment of the literal `continuationPath` is the sum of
the principal argument increments of its actual constituent chords. -/
theorem continuationPath_argument_increment (D : PLLinkDiagram)
    (e : Fin D.nArc) (n : ℕ) (z : ℂ)
    (havoid : ∀ k : ℕ, k < n →
      (0 : ℂ) ∉ segment ℝ (orbitWordSource D e k-z) (orbitWordTarget D e k-z))
    (θ : C(I, ℝ))
    (hθ : ∀ u : I,
      (θ u : Real.Angle) =
        ((Complex.equivRealProd.symm (continuationPath D e n u)-z).arg : Real.Angle)) :
    θ 1-θ 0 =
      ∑ k ∈ Finset.range n,
        Complex.arg ((orbitWordTarget D e k-z)/(orbitWordSource D e k-z)) := by
  revert θ
  induction n with
  | zero =>
      intro θ hθ
      let ψ : C(I, ℝ) := ⟨fun _ => Complex.arg (orbitWordSource D e 0-z), continuous_const⟩
      have hangle : ∀ u : I, (θ u : Real.Angle) = (ψ u : Real.Angle) := by
        intro u
        have h := hθ u
        simpa [ψ, orbitWordSource, continuationPath, Path.cast_coe] using h
      have hdiff := PositionalIndex.angle_lift_difference_constant θ ψ
        θ.continuous ψ.continuous hangle (1:I) (0:I)
      simp [ψ] at hdiff
      simpa using (sub_eq_zero.mpr hdiff)
  | succ n ih =>
      intro θ hθ
      cases n with
      | zero =>
          have hseg := havoid 0 (by omega)
          have hcurve (u : I) :
              Complex.equivRealProd.symm (continuationPath D e 1 u) =
                (1-u.val : ℂ) * orbitWordSource D e 0 +
                  (u.val : ℂ) * orbitWordTarget D e 0 := by
            simp [continuationPath,continuationArcPath,diagramArcPath_apply,
              Path.cast_coe,orbitWordSource,orbitWordTarget,
              Complex.equivRealProd_symm_apply,affinePoint]
            apply Complex.ext
            · simp [smul_eq_mul] <;> ring
            · simp [smul_eq_mul] <;> ring
          have harg : ∀ u : I,
              (θ u : Real.Angle) =
                ((((1-u.val : ℝ) : ℂ) * (orbitWordSource D e 0-z) +
                    (u.val : ℂ) * (orbitWordTarget D e 0-z)).arg : Real.Angle) := by
            intro u
            have h := hθ u
            have hsub :
                Complex.equivRealProd.symm (continuationPath D e 1 u)-z =
                  (1-u.val : ℂ) * (orbitWordSource D e 0-z) +
                    (u.val : ℂ) * (orbitWordTarget D e 0-z) := by
              rw [hcurve]
              apply Complex.ext <;> simp [smul_eq_mul,Complex.ofReal_sub] <;> ring
            rw [hsub] at h
            simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h
          simpa [Finset.sum_range_succ] using
            zeroFreeChord_lift_increment (orbitWordSource D e 0-z)
              (orbitWordTarget D e 0-z) hseg θ harg
      | succ k =>
          let f := (D.continuation ^ (k+1)) e
          let γ := (continuationPath D e (k+1)).map
            Complex.equivRealProdCLM.symm.continuous
          let η := ((continuationArcPath D f).cast rfl
            (by
              change D.vertexPoint (D.arcSource ((D.continuation ^ (k+2)) e)) =
                D.vertexPoint (D.arcSource (D.continuation f))
              apply congrArg D.vertexPoint
              apply congrArg D.arcSource
              symm
              dsimp [f]
              simp only [pow_succ',Equiv.Perm.mul_apply])).map
            Complex.equivRealProdCLM.symm.continuous
          have hmap : (continuationPath D e (k+2)).map
              Complex.equivRealProdCLM.symm.continuous = γ.trans η := by
            ext u
            simp [continuationPath,γ,η,f,Path.trans_apply,Path.cast_coe,
              Path.map_coe,Function.comp_apply]
            split_ifs <;> rfl
          have hθtrans : ∀ u : I, (θ u : Real.Angle) =
              (((γ.trans η) u-z).arg : Real.Angle) := by
            intro u
            have h := hθ u
            have h' : (θ u : Real.Angle) =
                ((((continuationPath D e (k+2)).map
                  Complex.equivRealProdCLM.symm.continuous) u-z).arg : Real.Angle) := by
              simpa only [Path.map_coe,Function.comp_apply,Nat.add_assoc] using h
            rw [hmap] at h'
            exact h'
          obtain ⟨L,R,hL,hR,hinc⟩ :=
            path_trans_argument_lift_split γ η z θ hθtrans
          have hprefixAvoid : ∀ j : ℕ, j < k+1 →
              (0 : ℂ) ∉ segment ℝ (orbitWordSource D e j-z)
                (orbitWordTarget D e j-z) := by
            intro j hj
            exact havoid j (by omega)
          have hL' : ∀ u : I, (L u : Real.Angle) =
              ((Complex.equivRealProd.symm (continuationPath D e (k+1) u)-z).arg : Real.Angle) := by
            intro u
            simpa only [Path.map_coe,Function.comp_apply] using hL u
          have hprefix := ih hprefixAvoid L hL'
          have hlastSeg := havoid (k+1) (by omega)
          have hlastArg : ∀ u : I,
              (R u : Real.Angle) =
                ((((1-u.val : ℝ) : ℂ) * (orbitWordSource D e (k+1)-z) +
                    (u.val : ℂ) * (orbitWordTarget D e (k+1)-z)).arg : Real.Angle) := by
            intro u
            have hη : η u =
                (1-u.val : ℂ) * orbitWordSource D e (k+1) +
                  (u.val : ℂ) * orbitWordTarget D e (k+1) := by
              apply Complex.ext <;>
                simp [η,f,Path.map_coe,Function.comp_apply,continuationArcPath,
                diagramArcPath_apply,Path.cast_coe,Complex.equivRealProdCLM_symm_apply,
                orbitWordSource,orbitWordTarget,affinePoint,smul_eq_mul] <;> ring
            have h := hR u
            rw [hη] at h
            have hlinear :
                (1-u.val : ℂ) * orbitWordSource D e (k+1) +
                  (u.val : ℂ) * orbitWordTarget D e (k+1) - z =
                (1-u.val : ℂ) * (orbitWordSource D e (k+1)-z) +
                  (u.val : ℂ) * (orbitWordTarget D e (k+1)-z) := by
              push_cast
              ring
            rw [hlinear] at h
            simpa only [Complex.ofReal_sub, Complex.ofReal_one] using h
          have hlast := zeroFreeChord_lift_increment
            (orbitWordSource D e (k+1)-z) (orbitWordTarget D e (k+1)-z)
            hlastSeg R hlastArg
          rw [Finset.sum_range_succ]
          rw [← hprefix, ← hlast]
          exact hinc

end DirectGLSSW.HOMFLY.PrincipalTurning

namespace DirectGLSSW.HOMFLY.PLWinding

open DirectGLSSW.HOMFLY.PrincipalTurning
open DirectGLSSW.HOMFLY
open DirectGLSSW.HOMFLY.PositionalIndex

/-- The literal complex loop's off-trace condition supplies avoidance of each
actual affine edge in the continuation word. -/
theorem actualComponentWord_avoids_of_complexPLLoop_avoids
    (D : PLLinkDiagram) (T : BasedTraversal D) (C : diagramComponent D) (z : ℂ)
    (hloop : ∀ u : I, complexPLLoop D (T.baseArc C).val u ≠ z) :
    AvoidsPolygonEdges (actualComponentWord T C) z := by
  intro i t ht0 ht1 hz
  let e := (T.baseArc C).val
  let f := (D.continuation ^ i.val) e
  let p := D.vertexPoint (D.arcSource f)
  let q := D.vertexPoint (D.arcTarget f)
  have hsource : actualComponentWord T C i = Complex.equivRealProd.symm p := by
    rfl
  have htarget : actualComponentWord T C (cyclicSuccessorPerm
      (componentArcLength D e) i) = Complex.equivRealProd.symm q := by
    simpa [e,f,q] using actualComponentWord_successor T C i
  have hcomplex : actualComponentWord T C i + (t : ℂ) *
      (actualComponentWord T C (cyclicSuccessorPerm (componentArcLength D e) i) -
        actualComponentWord T C i) = Complex.equivRealProd.symm (affinePoint p q t) := by
    rw [hsource,htarget]
    apply Complex.ext <;> simp [Complex.equivRealProd_symm_apply,affinePoint] <;> ring
  have hArc : affinePoint p q t ∈ Set.range (diagramArcPath D f) := by
    refine ⟨⟨t,⟨ht0,ht1⟩⟩,?_⟩
    simp [diagramArcPath_apply,p,q]
  have hTrace : affinePoint p q t ∈ Set.range (componentPLLoop D e) :=
    (componentPLLoop_trace D e (affinePoint p q t)).2
      ⟨f,DirectGLSSW.PermutationOrbits.componentOf_pow_apply _ _ _,hArc⟩
  obtain ⟨u,hu⟩ := hTrace
  have hvalue : complexPLLoop D e u =
      actualComponentWord T C i + (t : ℂ) *
        (actualComponentWord T C (cyclicSuccessorPerm (componentArcLength D e) i) -
          actualComponentWord T C i) := by
    change Complex.equivRealProd.symm (componentPLLoop D e u) = _
    rw [hu,←hcomplex]
  exact hloop u (by rw [hvalue,hz])

/-- The continuous positional index of the literal actual component loop is
the integer index of its finite actual continuation word. -/
theorem complexPLLoop_index_eq_actualComponentWord_windingIndex
    (D : PLLinkDiagram) (T : BasedTraversal D) (C : diagramComponent D) (z : ℂ)
    (hloop : ∀ u : I, complexPLLoop D (T.baseArc C).val u ≠ z) :
    ∃ hAvoid : AvoidsPolygonEdges (actualComponentWord T C) z,
      unitPositionalIndex (complexPLLoop D (T.baseArc C).val)
        (complexPLLoop_endpoint_eq D (T.baseArc C).val).symm z hloop =
      windingIndex (actualComponentWord T C) z hAvoid := by
  let e := (T.baseArc C).val
  let m := componentArcLength D e
  let q := actualComponentWord T C
  have hAvoid := actualComponentWord_avoids_of_complexPLLoop_avoids D T C z hloop
  have hseg : ∀ k : ℕ, k < m →
      (0 : ℂ) ∉ segment ℝ
        (orbitWordSource D e k-z) (orbitWordTarget D e k-z) := by
    intro k hk hmem
    let hkFin : Fin m := ⟨k,hk⟩
    rw [segment_eq_image_lineMap] at hmem
    rcases hmem with ⟨s,hs,hzero⟩
    have hpoint : z = q hkFin + (s : ℂ) *
        (q (cyclicSuccessorPerm m hkFin)-q hkFin) := by
      have hsrc : orbitWordSource D e k = q hkFin := by
        change Complex.equivRealProd.symm
          (D.vertexPoint (D.arcSource ((D.continuation ^ k) e))) =
          actualComponentWord T C hkFin
        have hval : hkFin.val = k := rfl
        rw [← hval]
        rfl
      have htar : orbitWordTarget D e k =
          q (cyclicSuccessorPerm m hkFin) := by
        change Complex.equivRealProd.symm
          (D.vertexPoint (D.arcTarget ((D.continuation ^ k) e))) =
          actualComponentWord T C (cyclicSuccessor hkFin)
        have hval : hkFin.val = k := rfl
        rw [← hval]
        exact (actualComponentWord_successor T C hkFin).symm
      rw [AffineMap.lineMap_apply] at hzero
      rw [hsrc,htar] at hzero
      simp only [vsub_eq_sub,vadd_eq_add,smul_eq_mul] at hzero
      have hdiff : (q (cyclicSuccessorPerm m hkFin)-z) - (q hkFin-z) =
          q (cyclicSuccessorPerm m hkFin)-q hkFin := by ring
      rw [hdiff] at hzero
      have hx : q hkFin + (s : ℂ) *
          (q (cyclicSuccessorPerm m hkFin)-q hkFin)-z = 0 := by
        calc
          _ = (s : ℂ) * (q (cyclicSuccessorPerm m hkFin)-q hkFin) + (q hkFin-z) := by ring
          _ = 0 := hzero
      exact (sub_eq_zero.mp hx).symm
    exact hAvoid hkFin s hs.1 hs.2 hpoint
  obtain ⟨Γ,⟨_hstart,hΓ⟩,hΓinc⟩ :=
    unitPositionalIndex_characterization (complexPLLoop D e)
      (complexPLLoop_endpoint_eq D e).symm z hloop
  have hθ : ∀ u : I, (Γ u : Real.Angle) =
      ((Complex.equivRealProd.symm (continuationPath D e m u)-z).arg : Real.Angle) := by
    intro u
    have h := hΓ u
    simpa [complexPLLoop,componentPLLoop,Path.cast_coe] using h
  have hsum := continuationPath_argument_increment D e m z hseg Γ hθ
  have hfinite : edgeArgSum q z =
      ∑ k ∈ Finset.range m,
        Complex.arg ((orbitWordTarget D e k-z)/(orbitWordSource D e k-z)) := by
    rw [edgeArgSum_eq_finite_principal_args]
    rw [← Fin.sum_univ_eq_sum_range]
    apply Finset.sum_congr rfl
    intro i _
    change Complex.arg ((actualComponentWord T C (cyclicSuccessorPerm m i)-z)/
      (actualComponentWord T C i-z)) = _
    rw [actualComponentWord_successor]
    have hsrc : actualComponentWord T C i = orbitWordSource D e i.val := by
      simp [orbitWordSource,actualComponentWord,e]
    rw [hsrc]
    rfl
  rw [← hsum] at hfinite
  have hindex : edgeArgSum q z =
      (DirectGLSSW.HOMFLY.PositionalIndex.unitPositionalIndex (complexPLLoop D e)
        (complexPLLoop_endpoint_eq D e).symm z hloop : ℝ) * (2*Real.pi) := by
    rw [hfinite,hΓinc]
  refine ⟨hAvoid,?_⟩
  exact (windingIndex_characterization q z hAvoid).2 _ hindex

end DirectGLSSW.HOMFLY.PLWinding
