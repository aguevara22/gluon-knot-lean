import SourceBoundaryOrdinaryLimit
import ParentReindex
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.SourceBoundaryCurrent
open DirectGLSSW EndpointCurrent EndpointEventGeometry
/-- The parent ordinary current uses the literal event point followed by the
vertices after the crossed edge, with no virtual closing vertex. -/
theorem ordinary_parent_reindexed
    (W : ℕ → PlanarPoint ℝ) (K N : ℕ) (hKN : K<N) :
    ordinaryCurrent (fun _ _ _ => -1) (endpointFar K (polygonSignArray W)) K N =
    ordinaryCurrent (fun _ _ _ => -1)
      (polygonSignArray (fun i => if i=0 then W 0 else W (K+i))) 0 (N-K) := by
  let Hparent : TripleArray := EndpointCurrent.endpointFar K (polygonSignArray W)
  let Wlocal : ℕ → PlanarPoint ℝ := fun i => if i = 0 then W 0 else W (K + i)
  have hlocal : ∀ a b c, a < b → b < c →
      CurrentTranslation.translateTriple K Hparent a b c =
        polygonSignArray Wlocal a b c := by
    intro a b c hab hbc
    by_cases ha : a = 0
    · subst a
      have hb : b ≠ 0 := by omega
      have hc : c ≠ 0 := by omega
      simp [CurrentTranslation.translateTriple, Hparent, Wlocal,
        EndpointCurrent.endpointFar, endpointFar, polygonSignArray,
        polygonHDet, hb, hc]
    · have hb : b ≠ 0 := by omega
      have hc : c ≠ 0 := by omega
      have hKa : K + a ≠ K := by omega
      simp [CurrentTranslation.translateTriple, Hparent, Wlocal,
        EndpointCurrent.endpointFar, endpointFar, polygonSignArray,
        polygonHDet, ha, hb, hc, hKa]
  have ht := CurrentTranslation.ordinaryCurrent_translate
    (fun _ _ _ => (-1 : ℚ)) Hparent K 0 (N-K) (by omega)
  have hD : CurrentTranslation.translateTriple K (fun _ _ _ => (-1 : ℚ)) =
      (fun _ _ _ => (-1 : ℚ)) := rfl
  rw [hD, Nat.add_zero, Nat.add_sub_of_le (Nat.le_of_lt hKN)] at ht
  rw [← ht]
  apply ordinaryCurrent_congr_interval_fixed_near _ _ _ (by omega)
  intro a b c ha hab hbc hc
  exact hlocal a b c hab hbc

/-- Physical crossing form, retaining explicit intermediate isolation and
prefix conditions for later discharge from the actual auxiliary domain. -/
theorem exists_physical_ordinary_boundary_jump
    (hRI : GLSSWRootIndependence) (W : ℕ → PlanarPoint ℝ)
    (N k : ℕ) (hKN : k<N) (s : ℝ) (hs0 : 0<s) (hs1 : s<1)
    (hcross : W 0=affinePoint (W k) (W (k+1)) s)
    (htrans : planarDet (W 1-W 0) (W (k+1)-W k)≠0)
    (hisolated : ∀ a b d, a<b → b<d → d≤N →
      (a≠0 ∨ b≠k ∨ d≠k+1) → polygonHDet W a b d≠0)
    (hQ : CyclicGeneric (fun i : Fin (k+1) => W i.val)) :
    ∃ ρ : ℝ, 0<ρ ∧ ρ≤1 ∧ ∀ ε : ℝ, 0<ε → ε<ρ →
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) ε) N ∧
      ShortEdgeSignStability.CoreHGeneric (moveEndpoint W (W 1-W 0) (-ε)) N ∧
      ∀ j, k<j → j≤N →
      ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W (W 1-W 0) ε)) 0 j -
        ordinaryCurrent (fun _ _ _ => -1) (polygonSignArray (moveEndpoint W (W 1-W 0) (-ε))) 0 j =
      scalarSignValue (planarDet (W 1-W 0) (W (k+1)-W k)) *
        polygonAmplitude (fun i : Fin (k+1) => W i.val) hQ *
        ordinaryCurrent (fun _ _ _ => -1)
          (polygonSignArray (fun i => if i=0 then W 0 else W (k+i))) 0 (j-k) := by
  have hd : 0<1-s := by linarith
  have hτ : -s/(1-s)<0 := div_neg_of_neg_of_pos (neg_neg_of_pos hs0) hd
  have hcol : W k=W 0+(-s/(1-s)) • (W (k+1)-W 0) := by
    have hx := congrArg Prod.fst hcross
    have hy := congrArg Prod.snd hcross
    change (W 0).1=(W k).1+s*((W (k+1)).1-(W k).1) at hx
    change (W 0).2=(W k).2+s*((W (k+1)).2-(W k).2) at hy
    apply Prod.ext
    · change (W k).1=(W 0).1+(-s/(1-s))*((W (k+1)).1-(W 0).1)
      field_simp
      nlinarith [hx]
    · change (W k).2=(W 0).2+(-s/(1-s))*((W (k+1)).2-(W 0).2)
      field_simp
      nlinarith [hy]
  have hdet : planarDet (W k-W (k+1)) (W 1-W 0) =
      planarDet (W 1-W 0) (W (k+1)-W k) := by
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
    ring
  have hk : 0<k := by have := hQ.size_ge_three; omega
  obtain ⟨ρ,hρ,hjump⟩ := exists_adjacent_ordinary_row_limit W (W 1-W 0)
    N k hk (by omega) (-s/(1-s)) hcol (by rwa [hdet]) hisolated hτ
  refine ⟨min ρ 1,lt_min hρ (by norm_num),min_le_right _ _,?_⟩
  intro ε he her
  obtain ⟨hp,hm,hrow⟩ := hjump ε he (lt_of_lt_of_le her (min_le_left _ _))
  refine ⟨hp,hm,?_⟩
  intro j hkj hjN
  have H := hrow j (by omega) hjN
  simp only [if_pos hkj] at H
  rw [hdet,markedAmplitude_prefix_polygon hRI W k hQ,
    ordinary_parent_reindexed W k j hkj] at H
  exact H


end DirectGLSSW.SourceBoundaryCurrent
