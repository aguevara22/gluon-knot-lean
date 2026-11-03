import DirectGLSSW.ExtendedReturnArcGeometry
import DirectGLSSW.OrderedCapEvents
import DirectGLSSW.CapEventInterpretation

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnEndpointEvents
open DirectGLSSW ExtendedReturnArcGeometry CapCriticalEventGeometry CapCriticalTimes
open OrderedCapEvents CapCrossingEvent ActualEventGeometry

abbrev Point := PlanarPoint ℝ

/-- Negative adjacent endpoint-height ratio is the exact actual-event criterion. -/
theorem actualPair_mem_of_ratio (q : ℕ → Point) (n k : ℕ)
    (hk : 0 < k) (hkn : k < n) (hratio : (q k).2 / (q (k+1)).2 < 0) :
    (k,k+1) ∈ actualPairs q n := by
  have hy : (q k).2 ≠ (q (k+1)).2 := by
    intro h
    rcases div_neg_iff.mp hratio with hsign | hsign <;> rw [h] at hsign <;> linarith [hsign.1, hsign.2]
  have hslope : planarDet (q k-q (k+1)) (1,0) ≠ 0 := by
    simpa [planarDet] using sub_ne_zero.mpr (Ne.symm hy)
  apply Finset.mem_filter.mpr
  refine ⟨?_, rfl, hratio⟩
  apply Finset.mem_filter.mpr
  refine ⟨?_, hk, by omega, by omega, hslope⟩
  simp only [Finset.mem_product, Finset.mem_range]
  omega

theorem actualPair_bounds (q : ℕ → Point) (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ actualPairs q n) :
    0 < p.1 ∧ p.1 < n ∧ p.2=p.1+1 ∧ (q p.1).2/(q p.2).2 < 0 ∧
      planarDet (q p.1-q p.2) (1,0) ≠ 0 := by
  obtain ⟨hp, hadj, hratio⟩ := Finset.mem_filter.mp hp
  obtain ⟨_, hpos, hlt, hle, hslope⟩ := Finset.mem_filter.mp hp
  exact ⟨hpos, by omega, hadj, hratio, hslope⟩

theorem extendedArc_second {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedArc hn P ε 2 = P (firstIndex hn) := by
  exact extendedArc_interior hn P ε (firstIndex hn) (by norm_num) (by change 2 < n; omega)

theorem extendedArc_penultimate {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point) (ε : ℝ) :
    extendedArc hn P ε (n-1) = P (penultimateIndex hn) := by
  have h := extendedArc_interior hn P ε (penultimateIndex hn)
    (by change 0 < n-2; omega) (by change n-2+1 < n; omega)
  have hi : n-2+1=n-1 := by omega
  simpa only [penultimateIndex, Fin.val_mk, hi] using h

theorem endpoint_height_ratios {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    (extendedArc hn P ε 1).2 / (extendedArc hn P ε 2).2 = -ε ∧
    (extendedArc hn P ε (n-1)).2 / (extendedArc hn P ε n).2 = -1/ε := by
  have hf := original_interior_off_line hn P hP hU hV (firstIndex hn)
    (by norm_num) (by change 2 < n; omega)
  have hz := original_interior_off_line hn P hP hU hV (penultimateIndex hn)
    (by change 0 < n-2; omega) (by change n-2+1 < n; omega)
  rw [extendedArc_first, extendedArc_second, extendedArc_last, extendedArc_penultimate]
  constructor
  · simp [extendBack, hU]
    field_simp [hf]
  · simp [extendBack, hV]
    field_simp [hz, ne_of_gt hε]
    ring

theorem endpoint_pairs_mem {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    (1,2) ∈ actualPairs (extendedArc hn P ε) n ∧
    (n-1,n) ∈ actualPairs (extendedArc hn P ε) n := by
  have hr := endpoint_height_ratios hn P hP hU hV ε hε
  constructor
  · apply actualPair_mem_of_ratio _ _ 1 (by norm_num) (by omega)
    change (extendedArc hn P ε 1).2 / (extendedArc hn P ε 2).2 < 0
    rw [hr.1]
    linarith
  · have hn1 : n-1+1=n := by omega
    have h := actualPair_mem_of_ratio (extendedArc hn P ε) n (n-1) (by omega) (by omega)
    rw [hn1] at h
    apply h
    rw [hr.2]
    exact div_neg_of_neg_of_pos (by norm_num) hε

theorem endpoint_criticalRoots {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (ε : ℝ) (hε : 0 < ε) :
    criticalRoot (extendedArc hn P ε) (1,2) = 0 ∧
    criticalRoot (extendedArc hn P ε) (n-1,n) =
      (P (lastIndex hn)).1-(P (zeroIndex hn)).1 := by
  have hm := endpoint_pairs_mem hn P hP hU hV ε hε
  have hu := (actualPair_bounds _ _ _ hm.1).2.2.2.2
  have hv := (actualPair_bounds _ _ _ hm.2).2.2.2.2
  constructor
  · apply (div_eq_iff hu).mpr
    simp only [polygonHDet, extendedArc_zero, extendedArc_first, extendedArc_second]
    simp [extendBack, planarDet]
    ring
  · apply (div_eq_iff hv).mpr
    simp only [polygonHDet, extendedArc_zero, extendedArc_last, extendedArc_penultimate]
    simp [extendBack, planarDet, hU, hV]
    ring

/-- A raw actual pair gives an open-segment crossing before any choice of ordered index. -/
theorem actualPair_on_segment (q : ℕ → Point) (n : ℕ) (hzero : (q 0).2 = 0)
    (p : ℕ × ℕ) (hp : p ∈ actualPairs q n) :
    OnOpenSegment (q p.1) (q p.2) (horizontalMove q (criticalRoot q p) 0) := by
  rcases p with ⟨k,l⟩
  obtain ⟨hk, hkn, hl, hr, hs⟩ := actualPair_bounds q n (k,l) hp
  dsimp only at hl hr ⊢
  subst l
  have hne : (q k).2 ≠ 0 ∧ (q (k+1)).2 ≠ 0 := by
    rcases div_neg_iff.mp hr with h | h
    · exact ⟨ne_of_gt h.1, ne_of_lt h.2⟩
    · exact ⟨ne_of_lt h.1, ne_of_gt h.2⟩
  exact (criticalRoot_event_onOpenSegment_iff_negative_height_ratio q k hk hzero
    hne.1 hne.2).mpr hr

/-- The root of every actual extended-return pair lies on its original edge carrier. -/
theorem actualPair_original_carrier {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hU : (P (zeroIndex hn)).2 = 0) (ε : ℝ) (p : ℕ × ℕ)
    (hp : p ∈ actualPairs (extendedArc hn P ε) n) :
    let e : Fin n := ⟨p.1-1, by have hb := actualPair_bounds _ _ _ hp; omega⟩
    planarDet (cyclicTangent P e)
      (horizontalMove (extendedArc hn P ε) (criticalRoot (extendedArc hn P ε) p) 0-P e) = 0 := by
  obtain ⟨hk,hkn,hadj,hr,hs⟩ := actualPair_bounds _ _ _ hp
  let e : Fin n := ⟨p.1-1, by omega⟩
  have he : e.val+1 < n := by dsimp [e]; omega
  have hv : e.val+1=p.1 := by dsimp [e]; omega
  have hsuc := return_successor_eq e he
  have hleft : extendedArc hn P ε p.1 = extendedWord hn P ε e := by
    exact arcFromWord_positive _ _ _ hk (by omega)
  have hright : extendedArc hn P ε p.2 = extendedWord hn P ε (cyclicSuccessor e) := by
    rw [hsuc]
    have h := arcFromWord_positive (P (zeroIndex hn)) (extendedWord hn P ε) p.2
      (by omega) (by omega)
    convert h using 1
    apply congrArg (extendedWord hn P ε)
    apply Fin.ext
    dsimp only [Fin.val_mk]
    omega
  have hsegment := actualPair_on_segment (extendedArc hn P ε) n
    (by simpa only [extendedArc_zero] using hU) p hp
  rw [hleft,hright] at hsegment
  exact extended_return_carrier hn P ε e he _ hsegment

/-- G1 isolates each endpoint among actual roots; no injectivity of all secant roots is used. -/
theorem endpoint_actual_root_unique {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (ε : ℝ) (p : ℕ × ℕ) (hp : p ∈ actualPairs (extendedArc hn P ε) n) :
    (criticalRoot (extendedArc hn P ε) p = 0 → p = (1,2)) ∧
    (criticalRoot (extendedArc hn P ε) p =
      (P (lastIndex hn)).1-(P (zeroIndex hn)).1 → p = (n-1,n)) := by
  obtain ⟨hk,hkn,hadj,hr,hs⟩ := actualPair_bounds _ _ _ hp
  let e : Fin n := ⟨p.1-1, by omega⟩
  have he : e.val+1 < n := by dsimp [e]; omega
  have hsuc := return_successor_eq e he
  have hcarrier := actualPair_original_carrier hn P hU ε p hp
  change planarDet (cyclicTangent P e) (_-P e) = 0 at hcarrier
  constructor
  · intro hroot
    rw [hroot] at hcarrier
    simp only [horizontalMove, EndpointEventGeometry.moveEndpoint, if_pos rfl,
      zero_smul, add_zero, extendedArc_zero] at hcarrier
    have heq : e = zeroIndex hn := by
      by_contra hne
      have hvs : zeroIndex hn ≠ cyclicSuccessor e := by
        rw [hsuc]
        intro h
        have hval := congrArg Fin.val h
        simp only [zeroIndex, Fin.val_mk] at hval
        omega
      exact cyclic_vertex_carrier_det_ne_zero hn P hP e (zeroIndex hn) (Ne.symm hne) hvs hcarrier
    have hv := congrArg Fin.val heq
    simp only [e,zeroIndex,Fin.val_mk] at hv
    apply Prod.ext <;> dsimp only <;> omega
  · intro hroot
    have hmove : horizontalMove (extendedArc hn P ε)
        ((P (lastIndex hn)).1-(P (zeroIndex hn)).1) 0 = P (lastIndex hn) := by
      apply Prod.ext <;> simp [horizontalMove, EndpointEventGeometry.moveEndpoint,
        extendedArc_zero, hU, hV]
    rw [hroot,hmove] at hcarrier
    have heq : cyclicSuccessor e = lastIndex hn := by
      by_contra hne
      have hve : lastIndex hn ≠ e := by
        intro h
        have hval := congrArg Fin.val h
        simp only [lastIndex,e,Fin.val_mk] at hval
        omega
      exact cyclic_vertex_carrier_det_ne_zero hn P hP e (lastIndex hn) hve (Ne.symm hne) hcarrier
    rw [hsuc] at heq
    have hv := congrArg Fin.val heq
    simp only [lastIndex,Fin.val_mk] at hv
    dsimp [e] at hv
    apply Prod.ext <;> dsimp only <;> omega

theorem exists_event_of_actualPair (q : ℕ → Point) (n : ℕ) (p : ℕ × ℕ)
    (hp : p ∈ actualPairs q n) :
    ∃ c : EventIndex q n, eventTime q n c = criticalRoot q p := by
  have hmem : criticalRoot q p ∈ actualTimes q n := Finset.mem_image.mpr ⟨p,hp,rfl⟩
  have hmem' : criticalRoot q p ∈ Set.range ((actualTimes q n).orderEmbOfFin rfl) := by
    rw [Finset.range_orderEmbOfFin]
    exact hmem
  exact hmem'

private theorem scalarSignValue_negative_mul (a x : ℝ) (ha : a < 0) :
    scalarSignValue (a*x) = -scalarSignValue x := by
  rcases lt_trichotomy x 0 with hx | hx | hx
  · have hm := mul_pos_of_neg_of_neg ha hx
    simp [scalarSignValue, ne_of_lt hx, ne_of_gt hm, hx, not_lt_of_gt hm]
  · subst x
    simp [scalarSignValue]
  · have hm := mul_neg_of_neg_of_pos ha hx
    simp [scalarSignValue, ne_of_gt hx, ne_of_lt hm, not_lt_of_gt hx, hm]

/-- Exact endpoint event data, with chronological ranks left existential because
other actual crossings may lie outside the chosen edge. -/
theorem endpoint_events {n : ℕ} (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P)
    (hU : (P (zeroIndex hn)).2 = 0) (hV : (P (lastIndex hn)).2 = 0)
    (hleft : (P (zeroIndex hn)).1 < (P (lastIndex hn)).1)
    (ε : ℝ) (hε : 0 < ε) :
    ∃ cU cV : EventIndex (extendedArc hn P ε) n,
      eventTime (extendedArc hn P ε) n cU = 0 ∧
      eventTime (extendedArc hn P ε) n cV = (P (lastIndex hn)).1-(P (zeroIndex hn)).1 ∧
      eventPair (extendedArc hn P ε) n cU = (1,2) ∧
      eventPair (extendedArc hn P ε) n cV = (n-1,n) ∧ cU < cV ∧
      eventSign (extendedArc hn P ε) n cU = scalarSignValue (P (firstIndex hn)).2 ∧
      eventSign (extendedArc hn P ε) n cV = -scalarSignValue (P (penultimateIndex hn)).2 := by
  have hm := endpoint_pairs_mem hn P hP hU hV ε hε
  have hr := endpoint_criticalRoots hn P hP hU hV ε hε
  obtain ⟨cU,hcU⟩ := exists_event_of_actualPair _ _ _ hm.1
  obtain ⟨cV,hcV⟩ := exists_event_of_actualPair _ _ _ hm.2
  rw [hr.1] at hcU
  rw [hr.2] at hcV
  have hsU := eventPair_spec (extendedArc hn P ε) n cU
  have hsV := eventPair_spec (extendedArc hn P ε) n cV
  have hpU := (endpoint_actual_root_unique hn P hP hU hV ε _ hsU.1).1 (hsU.2.trans hcU)
  have hpV := (endpoint_actual_root_unique hn P hP hU hV ε _ hsV.1).2 (hsV.2.trans hcV)
  have horder : cU < cV := by
    apply (Finset.orderEmbOfFin (actualTimes (extendedArc hn P ε) n) rfl).lt_iff_lt.mp
    change eventTime _ _ cU < eventTime _ _ cV
    rw [hcU,hcV]
    exact sub_pos.mpr hleft
  refine ⟨cU,cV,hcU,hcV,hpU,hpV,horder,?_,?_⟩
  · simp only [eventSign,hpU,Prod.snd,extendedArc_second]
  · simp only [eventSign,hpV,Prod.snd,extendedArc_last]
    have hheight : (extendBack (P (lastIndex hn)) (P (penultimateIndex hn)) ε).2 =
        (-ε)*(P (penultimateIndex hn)).2 := by simp [extendBack,hV]
    rw [hheight]
    exact scalarSignValue_negative_mul _ _ (neg_neg_of_pos hε)














end DirectGLSSW.ExtendedReturnEndpointEvents
