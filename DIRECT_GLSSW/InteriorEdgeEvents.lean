import ExtendedReturnEndpointEvents
import DirectGLSSW.MixedConsecutiveCapWord
import DirectGLSSW.ShortEdgeCyclicRelabel

set_option autoImplicit false
namespace DirectGLSSW.InteriorEdgeEvents
open DirectGLSSW ExtendedReturnArcGeometry ExtendedReturnEndpointEvents
open OrderedCapEvents CapCriticalEventGeometry CapCrossingEvent
open MixedEdgeSupportOrder MixedConsecutiveCapWord CyclicAnchorInterval

abbrev Point := PlanarPoint ℝ
variable {n : ℕ}

/-- Inverse to root's immutable public complementary-rank enumeration theorem. -/
theorem index_of_rank (e f : Fin n) :
    cyclicVertexIndex e (complementaryEventRank e f) = f := by
  apply complementaryEventRank_injective e
  exact complementaryRank_cyclicVertexIndex e _ (complementaryRank_lt_size e f)

theorem index_succ (e : Fin n) (k : ℕ) (hk : k+1<n) :
    cyclicVertexIndex e (k+1) = cyclicSuccessor (cyclicVertexIndex e k) := by
  have h := cyclicVertexEquiv_commutes_successor e (⟨k,by omega⟩ : Fin n)
  rw [return_successor_eq _ hk] at h
  exact h

theorem opened_zero (hn : 3 ≤ n) (q : Fin n → Point) (e : Fin n) :
    (q ∘ cyclicVertexEquiv e) (zeroIndex hn) = q (cyclicSuccessor e) := rfl

theorem opened_last (hn : 3 ≤ n) (q : Fin n → Point) (e : Fin n) :
    (q ∘ cyclicVertexEquiv e) (lastIndex hn) = q e := by
  change q (cyclicVertexIndex e (n-1)) = q e
  rw [cyclicVertexIndex_last]

theorem opened_generic (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n) :
    CyclicGeneric (q ∘ cyclicVertexEquiv e) :=
  cyclicGeneric_relabel q (cyclicVertexEquiv e) (cyclicVertexEquiv_commutes_successor e) hq

theorem extended_opened_interior (hn : 3 ≤ n) (q : Fin n → Point) (e : Fin n)
    (ε : ℝ) (k : ℕ) (hk : 1<k) (hkn : k<n) :
    extendedArc hn (q ∘ cyclicVertexEquiv e) ε k = q (cyclicVertexIndex e (k-1)) := by
  have h := extendedArc_interior hn (q ∘ cyclicVertexEquiv e) ε
    (⟨k-1,by omega⟩ : Fin n) (by dsimp; omega) (by dsimp; omega)
  have heq : k-1+1=k := by omega
  simpa only [Fin.val_mk,heq] using h

theorem extended_opened_off_line (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (ε : ℝ) (hε : 0<ε) (k : ℕ) (hk : 0<k) (hkn : k≤n) :
    (extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε k).2 ≠ 0 := by
  rw [extendedArc,arcFromWord_positive _ _ k hk hkn]
  apply extendedWord_off_line _ _ (opened_generic q hq e).g1 _ _ ε hε
  · simpa only [opened_zero] using hU
  · simpa only [opened_last] using hV

/-- Any actual segment incidence with the horizontal moving point identifies
both the raw actual-pair membership and the exact criticalRoot offset. -/
theorem actualPair_of_horizontal_segment (Q : ℕ → Point) (N k : ℕ)
    (hk : 0<k) (hkn : k<N) (hzero : (Q 0).2=0)
    (ha : (Q k).2 ≠ 0) (hb : (Q (k+1)).2 ≠ 0) (t : ℝ)
    (hseg : OnOpenSegment (Q k) (Q (k+1)) (horizontalMove Q t 0)) :
    (k,k+1) ∈ actualPairs Q N ∧ criticalRoot Q (k,k+1)=t := by
  have hyne : (Q k).2 ≠ (Q (k+1)).2 := by
    intro heq
    obtain ⟨s,_,_,hpoint⟩ := hseg
    have hy := congrArg Prod.snd hpoint
    simp [horizontalMove,EndpointEventGeometry.moveEndpoint,affinePoint,hzero,heq] at hy
    exact hb hy.symm
  have hden : planarDet (Q k-Q (k+1)) (1,0) ≠ 0 := by
    simpa [planarDet] using sub_ne_zero.mpr (Ne.symm hyne)
  have hcol := onOpenSegment_carrier_det_zero (onOpenSegment_symm hseg)
  have hid : planarDet (Q k-Q (k+1)) (horizontalMove Q t 0-Q (k+1)) =
      polygonHDet Q 0 k (k+1)+t*planarDet (Q k-Q (k+1)) (1,0) := by
    simp [horizontalMove,EndpointEventGeometry.moveEndpoint,polygonHDet,planarDet]
    ring
  rw [hid] at hcol
  have hroot : criticalRoot Q (k,k+1)=t := by
    apply (div_eq_iff hden).mpr
    linarith
  rw [←hroot] at hseg
  have hratio := (ActualEventGeometry.criticalRoot_event_onOpenSegment_iff_negative_height_ratio
    Q k hk hzero ha hb).mp hseg
  exact ⟨actualPair_mem_of_ratio Q N k hk hkn hratio,hroot⟩

/-- A chosen-edge crossing cannot use either incident neighboring edge. -/
theorem return_edge_nonincident (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (z : DirectGLSSW.EdgeChord q e) :
    crossingVisitEdge q (DirectGLSSW.returnVisit q e z) ≠ cyclicSuccessor e ∧
    cyclicSuccessor (crossingVisitEdge q (DirectGLSSW.returnVisit q e z)) ≠ e := by
  have he := crossingVisitPoint_mem q (DirectGLSSW.edgeVisit q e z)
  rw [(DirectGLSSW.edgeVisitSide_spec q e z).1] at he
  have hf := crossingVisitPoint_mem q (DirectGLSSW.returnVisit q e z)
  constructor
  · intro h
    rw [h] at hf
    exact cyclic_adjacent_interiors_disjoint hq.size_ge_three q hq.g1 e _ he hf
  · intro h
    exact cyclic_adjacent_interiors_disjoint hq.size_ge_three q hq.g1 _ _ hf (by simpa only [h] using he)

theorem return_rank_interior (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (z : DirectGLSSW.EdgeChord q e) :
    0 < complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z)) ∧
    complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2<n := by
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e z)
  have hfe := (DirectGLSSW.edgeVisitSide_spec q e z).2
  have hnon := return_edge_nonincident q hq e z
  have hzero : complementaryEventRank e (cyclicSuccessor e)=0 := by simp [complementaryEventRank]
  change 0 < complementaryEventRank e f ∧ complementaryEventRank e f+2<n
  constructor
  · by_contra h
    have hr : complementaryEventRank e f=0 := by omega
    have hf := complementaryEventRank_injective e (hr.trans hzero.symm)
    exact hnon.1 hf
  · have hlt := complementaryEventRank_lt_self e (cyclicSuccessor f) hnon.2
    rw [complementaryEventRank_cyclicSuccessor e f hfe,complementaryEventRank_self] at hlt
    omega

/-- The chosen-edge incidence fixes both height zero and the strict abscissa interval. -/
theorem edgeChord_point_bounds (q : Fin n → Point) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (z : DirectGLSSW.EdgeChord q e) :
    (crossingPoint q z.val).2=0 ∧
    (q (cyclicSuccessor e)).1 < (crossingPoint q z.val).1 ∧
    (crossingPoint q z.val).1 < (q e).1 := by
  have h := DirectGLSSW.edgeVisit_point_eq_affine q e z
  have hs := crossingVisitParameter_spec q (DirectGLSSW.edgeVisit q e z)
  rw [h]
  dsimp [affinePoint]
  refine ⟨by simp [hU,hV],?_,?_⟩ <;> nlinarith [hs.1,hs.2.1]

theorem edgeChord_actualPair (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (ε : ℝ) (hε : 0<ε) (z : DirectGLSSW.EdgeChord q e) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let r := complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))
    let t := (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1
    (r+1,r+2) ∈ actualPairs Q n ∧ criticalRoot Q (r+1,r+2)=t ∧
      0<t ∧ t<(q e).1-(q (cyclicSuccessor e)).1 := by
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e z)
  let r := complementaryEventRank e f
  let t := (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1
  change (r+1,r+2) ∈ actualPairs Q n ∧ criticalRoot Q (r+1,r+2)=t ∧
    0<t ∧ t<(q e).1-(q (cyclicSuccessor e)).1
  have hb := return_rank_interior q hq e z
  change 0<r ∧ r+2<n at hb
  have hfe := (DirectGLSSW.edgeVisitSide_spec q e z).2
  have hfirst : Q (r+1)=q f := by
    dsimp only [Q]
    rw [extended_opened_interior hq.size_ge_three q e ε (r+1) (by omega) (by omega)]
    simp only [Nat.add_sub_cancel]
    rw [index_of_rank]
  have hlast : Q (r+2)=q (cyclicSuccessor f) := by
    dsimp only [Q]
    rw [extended_opened_interior hq.size_ge_three q e ε (r+2) (by omega) hb.2]
    have heq : r+2-1=r+1 := by omega
    rw [heq]
    change q (cyclicVertexIndex e (complementaryEventRank e f+1))=q (cyclicSuccessor f)
    rw [←complementaryEventRank_cyclicSuccessor e f hfe,index_of_rank]
  have hbounds := edgeChord_point_bounds q e hU hV hleft z
  have hQ0 : Q 0=q (cyclicSuccessor e) := by
    dsimp only [Q]
    rw [extendedArc_zero]
    exact opened_zero _ q e
  have hpoint : horizontalMove Q t 0 = crossingPoint q z.val := by
    apply Prod.ext <;> simp [horizontalMove,EndpointEventGeometry.moveEndpoint,hQ0,t,hU,hbounds.1]
  have hseg : OnOpenSegment (Q (r+1)) (Q (r+1+1)) (horizontalMove Q t 0) := by
    have heq : r+1+1=r+2 := by omega
    rw [heq,hfirst,hlast,hpoint]
    exact crossingVisitPoint_mem q (DirectGLSSW.returnVisit q e z)
  have hzero : (Q 0).2=0 := by simpa only [Q,extendedArc_zero,opened_zero] using hU
  have hh := actualPair_of_horizontal_segment Q n (r+1) (by omega) (by omega) hzero
    (extended_opened_off_line q hq e hU hV ε hε _ (by omega) (by omega))
    (extended_opened_off_line q hq e hU hV ε hε _ (by omega) (by omega)) t hseg
  change (r+1,r+2) ∈ actualPairs Q n ∧ criticalRoot Q (r+1,r+2)=t at hh
  exact ⟨hh.1,hh.2,by dsimp [t]; linarith [hbounds.2.1],by dsimp [t]; linarith [hbounds.2.2]⟩

/-- Strictly interior times exclude both newly extended endpoint segments. -/
theorem actualPair_interior_indices (hn : 3 ≤ n) (P : Fin n → Point)
    (hP : cyclicNoncollinear P) (hU : (P (zeroIndex hn)).2=0) (hV : (P (lastIndex hn)).2=0)
    (ε : ℝ) (hε : 0<ε) (p : ℕ×ℕ) (hp : p ∈ actualPairs (extendedArc hn P ε) n)
    (ht0 : 0<criticalRoot (extendedArc hn P ε) p)
    (htL : criticalRoot (extendedArc hn P ε) p < (P (lastIndex hn)).1-(P (zeroIndex hn)).1) :
    1<p.1 ∧ p.1+1<n := by
  have hb := actualPair_bounds _ _ _ hp
  have hr := endpoint_criticalRoots hn P hP hU hV ε hε
  have hn1 : p.1 ≠ 1 := by
    intro h
    have heq : p=(1,2) := by apply Prod.ext <;> dsimp only <;> omega
    rw [heq,hr.1] at ht0
    exact lt_irrefl _ ht0
  have hnlast : p.1 ≠ n-1 := by
    intro h
    have heq : p=(n-1,n) := by apply Prod.ext <;> dsimp only <;> omega
    rw [heq,hr.2] at htL
    exact lt_irrefl _ htL
  constructor <;> omega

/-- Interior horizontal times are actual points of the chosen leftward edge. -/
theorem linePoint_on_chosen_edge (q : Fin n → Point) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (t : ℝ)
    (ht : 0<t) (htL : t<(q e).1-(q (cyclicSuccessor e)).1) :
    edgeInterior q e ((q (cyclicSuccessor e)).1+t,0) := by
  let L := (q e).1-(q (cyclicSuccessor e)).1
  have hL : 0<L := sub_pos.mpr hleft
  refine ⟨1-t/L,?_,?_,?_⟩
  · have hratio : t/L<1 := (div_lt_one hL).mpr htL
    linarith
  · have hratio := div_pos ht hL
    linarith
  · apply Prod.ext
    · dsimp [affinePoint,L]
      field_simp [ne_of_gt hL]
      ring
    · simp [affinePoint,hU,hV]

/-- Construct the actual chosen-edge crossing from its two open-segment incidences. -/
theorem edgeChord_of_common_point (q : Fin n → Point) (hq : CyclicGeneric q)
    (e f : Fin n) (hfe : f ≠ e) (X : Point) (he : edgeInterior q e X) (hf : edgeInterior q f X) :
    ∃ z : DirectGLSSW.EdgeChord q e, crossingPoint q z.val=X ∧
      crossingVisitEdge q (DirectGLSSW.returnVisit q e z)=f := by
  classical
  rcases lt_or_gt_of_ne hfe with hlt | hlt
  · let c : PolygonCrossing q := ⟨(f,e),hlt,X,hf,he⟩
    let z : DirectGLSSW.EdgeChord q e := ⟨c,Or.inr rfl⟩
    refine ⟨z,(crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 c X hf he).symm,?_⟩
    simp [z,c,DirectGLSSW.returnVisit,DirectGLSSW.edgeVisit,DirectGLSSW.edgeVisitSide,
      crossingVisitFlip,crossingVisitEdge,hfe]
  · let c : PolygonCrossing q := ⟨(e,f),hlt,X,he,hf⟩
    let z : DirectGLSSW.EdgeChord q e := ⟨c,Or.inl rfl⟩
    refine ⟨z,(crossingPoint_eq_of_mem hq.size_ge_three q hq.g1 c X he hf).symm,?_⟩
    simp [z,c,DirectGLSSW.returnVisit,DirectGLSSW.edgeVisit,DirectGLSSW.edgeVisitSide,
      crossingVisitFlip,crossingVisitEdge]

/-- Every raw actual pair whose time lies strictly inside the chosen edge
comes from one unique original chosen-edge crossing. -/
theorem actualPair_inside_unique_edgeChord (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0<ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ p ∈ actualPairs Q n, 0<criticalRoot Q p →
      criticalRoot Q p < (q e).1-(q (cyclicSuccessor e)).1 →
      ∃! z : DirectGLSSW.EdgeChord q e,
        (let r := complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))
         p=(r+1,r+2)) ∧ criticalRoot Q p=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 := by
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  dsimp only
  intro p hp ht0 htL
  have hb := actualPair_bounds _ _ _ hp
  have hidx := actualPair_interior_indices hq.size_ge_three (q ∘ cyclicVertexEquiv e)
    (opened_generic q hq e).g1 (by simpa only [opened_zero] using hU)
    (by simpa only [opened_last] using hV) ε hε p hp ht0
    (by simpa only [opened_last,opened_zero] using htL)
  let f := cyclicVertexIndex e (p.1-1)
  let X := horizontalMove Q (criticalRoot Q p) 0
  have hRankf : complementaryEventRank e f=p.1-1 :=
    complementaryRank_cyclicVertexIndex e _ (by omega)
  have hfe : f ≠ e := by
    intro heq
    rw [heq,complementaryEventRank_self] at hRankf
    omega
  have hfirst : Q p.1=q f := extended_opened_interior _ q e ε p.1 hidx.1 (by omega)
  have hlast : Q p.2=q (cyclicSuccessor f) := by
    rw [hb.2.2.1]
    dsimp only [Q]
    rw [extended_opened_interior hq.size_ge_three q e ε (p.1+1) (by omega) hidx.2]
    have heq : p.1+1-1=p.1 := by omega
    rw [heq]
    have hinc := index_succ e (p.1-1) (by omega)
    have heq' : p.1-1+1=p.1 := by omega
    rw [heq'] at hinc
    rw [hinc]
  have hQ0 : Q 0=q (cyclicSuccessor e) := by
    dsimp only [Q]
    rw [extendedArc_zero]
    exact opened_zero _ q e
  have hX : X=((q (cyclicSuccessor e)).1+criticalRoot Q p,0) := by
    apply Prod.ext <;> simp [X,horizontalMove,EndpointEventGeometry.moveEndpoint,hQ0,hU]
  have hzero : (Q 0).2=0 := by rw [hQ0]; exact hU
  have hf : edgeInterior q f X := by
    have hseg := actualPair_on_segment Q n hzero p hp
    rw [hfirst,hlast] at hseg
    exact hseg
  have he : edgeInterior q e X := by
    rw [hX]
    exact linePoint_on_chosen_edge q e hU hV hleft _ ht0 htL
  obtain ⟨z,hpoint,hedge⟩ := edgeChord_of_common_point q hq e f hfe X he hf
  have hrz : complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))=p.1-1 := by
    rw [hedge]
    exact hRankf
  have hpz : p=(complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
      complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2) := by
    rw [hrz]
    apply Prod.ext <;> dsimp only <;> omega
  have htz : criticalRoot Q p=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 := by
    have hx := congrArg Prod.fst hpoint
    rw [hX] at hx
    dsimp only [Prod.fst] at hx
    linarith
  refine ⟨z,⟨hpz,htz⟩,?_⟩
  intro z' hz'
  apply DirectGLSSW.edgeChord_abscissa_injective q hq.g2 e (hV.trans hU.symm) z' z
  linarith [hz'.2]

/-- G2 gives injectivity only for actual pairs at strictly interior chosen-edge
times. No assertion is made about exterior actual times or virtual secants. -/
theorem actualPair_interior_root_injective (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0<ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    ∀ p r, p ∈ actualPairs Q n → r ∈ actualPairs Q n →
      0<criticalRoot Q p → criticalRoot Q p<(q e).1-(q (cyclicSuccessor e)).1 →
      criticalRoot Q p=criticalRoot Q r → p=r := by
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  dsimp only
  intro p r hp hr ht0 htL heq
  obtain ⟨z,hz,_⟩ := actualPair_inside_unique_edgeChord q hq e hU hV hleft ε hε p hp ht0 htL
  obtain ⟨w,hw,_⟩ := actualPair_inside_unique_edgeChord q hq e hU hV hleft ε hε r hr
    (by rw [←heq]; exact ht0) (by rw [←heq]; exact htL)
  have hzw : z=w := by
    apply DirectGLSSW.edgeChord_abscissa_injective q hq.g2 e (hV.trans hU.symm) z w
    linarith [hz.2,hw.2]
  rw [hz.1,hw.1,hzw]

/-- The ordered event exists at each chosen-edge crossing and its chosen
actual pair is forced by the proved interior-time uniqueness. -/
theorem edgeChord_has_event (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0<ε)
    (z : DirectGLSSW.EdgeChord q e) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let r := complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))
    ∃ c : EventIndex Q n,
      eventTime Q n c=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n c=(r+1,r+2) ∧ 0<eventTime Q n c ∧
      eventTime Q n c<(q e).1-(q (cyclicSuccessor e)).1 := by
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  let r := complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))
  have hh := edgeChord_actualPair q hq e hU hV hleft ε hε z
  change (r+1,r+2) ∈ actualPairs Q n ∧
    criticalRoot Q (r+1,r+2)=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
    0<(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
    (crossingPoint q z.val).1-(q (cyclicSuccessor e)).1<(q e).1-(q (cyclicSuccessor e)).1 at hh
  obtain ⟨c,hc⟩ := exists_event_of_actualPair Q n _ hh.1
  have htime := hc.trans hh.2.1
  have hs := eventPair_spec Q n c
  have hpair := actualPair_interior_root_injective q hq e hU hV hleft ε hε
    (r+1,r+2) (eventPair Q n c) hh.1 hs.1
    (by rw [hh.2.1]; exact hh.2.2.1) (by rw [hh.2.1]; exact hh.2.2.2)
    (hc.symm.trans hs.2.symm)
  exact ⟨c,htime,hpair.symm,by rw [htime]; exact hh.2.2.1,by rw [htime]; exact hh.2.2.2⟩

/-- Exact crossing/event correspondence on the original chosen edge. No global
root injectivity is assumed for exterior actual pairs or nonadjacent secants. -/
theorem edgeChord_equiv_interior_actual_events (q : Fin n → Point) (hq : CyclicGeneric q) (e : Fin n)
    (hU : (q (cyclicSuccessor e)).2=0) (hV : (q e).2=0)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1) (ε : ℝ) (hε : 0<ε) :
    let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
    let L := (q e).1-(q (cyclicSuccessor e)).1
    ∃ E : DirectGLSSW.EdgeChord q e ≃
      {c : EventIndex Q n // 0<eventTime Q n c ∧ eventTime Q n c<L},
      ∀ z : DirectGLSSW.EdgeChord q e,
        eventTime Q n (E z).val=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
        (let r := complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))
         eventPair Q n (E z).val=(r+1,r+2)) := by
  classical
  let Q := extendedArc hq.size_ge_three (q ∘ cyclicVertexEquiv e) ε
  let L := (q e).1-(q (cyclicSuccessor e)).1
  let I := {c : EventIndex Q n // 0<eventTime Q n c ∧ eventTime Q n c<L}
  have hex : ∀ z : DirectGLSSW.EdgeChord q e, ∃ c : I,
      eventTime Q n c.val=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 ∧
      eventPair Q n c.val=(complementaryEventRank e
        (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+1,
        complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e z))+2) := by
    intro z
    obtain ⟨c,ht,hp,ht0,htL⟩ := edgeChord_has_event q hq e hU hV hleft ε hε z
    exact ⟨⟨c,ht0,htL⟩,ht,hp⟩
  let F : DirectGLSSW.EdgeChord q e → I := fun z => Classical.choose (hex z)
  have hF (z : DirectGLSSW.EdgeChord q e) := Classical.choose_spec (hex z)
  have hinj : Function.Injective F := by
    intro z w heq
    have ht := congrArg (fun c : I => eventTime Q n c.val) heq
    have hz : eventTime Q n (F z).val=(crossingPoint q z.val).1-(q (cyclicSuccessor e)).1 := (hF z).1
    have hw : eventTime Q n (F w).val=(crossingPoint q w.val).1-(q (cyclicSuccessor e)).1 := (hF w).1
    apply DirectGLSSW.edgeChord_abscissa_injective q hq.g2 e (hV.trans hU.symm) z w
    linarith
  have hsurj : Function.Surjective F := by
    intro c
    have hs := eventPair_spec Q n c.val
    obtain ⟨z,hz,_⟩ := actualPair_inside_unique_edgeChord q hq e hU hV hleft ε hε
      (eventPair Q n c.val) hs.1 (by rw [hs.2]; exact c.property.1)
      (by rw [hs.2]; exact c.property.2)
    refine ⟨z,Subtype.ext ?_⟩
    apply (eventTime_strictMono Q n).injective
    exact (hF z).1.trans (hz.2.symm.trans hs.2)
  refine ⟨Equiv.ofBijective F ⟨hinj,hsurj⟩,?_⟩
  intro z
  exact hF z




















end DirectGLSSW.InteriorEdgeEvents
