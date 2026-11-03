import DirectGLSSW.CapCriticalTimes
import DirectGLSSW.GlobalCapEntry
import DirectGLSSW.PolygonCrossings

set_option autoImplicit false

namespace DirectGLSSW.ExtendedReturnLocalCaps
open DirectGLSSW CapCriticalTimes CapCrossingEvent GlobalCapEntry
open ShortEdgeSignStability CapSubwordBridge

/-- A finite set has an empty punctured neighborhood at every center. -/
theorem exists_punctured_radius (T : Finset ℝ) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ → t + s ∉ T := by
  classical
  induction T using Finset.induction_on with
  | empty => exact ⟨1, by norm_num, by simp⟩
  | @insert x T hx ih =>
      obtain ⟨δ, hδ, hgood⟩ := ih
      by_cases hxt : x = t
      · refine ⟨δ, hδ, ?_⟩
        intro s hs hsδ hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · have hz : s = 0 := by rw [hxt] at heq; linarith
          simpa [hz] using hs
        · exact hgood s hs hsδ hmem
      · have hd : 0 < |x-t| := abs_pos.mpr (sub_ne_zero.mpr hxt)
        refine ⟨min δ |x-t|, lt_min hδ hd, ?_⟩
        intro s hs hsb hmem
        rcases Finset.mem_insert.mp hmem with heq | hmem
        · have he : s = x-t := by linarith
          have hbad := lt_of_lt_of_le hsb (min_le_right δ |x-t|)
          rw [he] at hbad
          exact (lt_irrefl _) hbad
        · exact hgood s hs (lt_of_lt_of_le hsb (min_le_left δ |x-t|)) hmem

private theorem hdet_rotate (q : ℕ → PlanarPoint ℝ) (a b c : ℕ) :
    polygonHDet q a b c = polygonHDet q b c a := by
  simp only [polygonHDet, planarDet, Prod.fst_sub, Prod.snd_sub]
  ring
private theorem hdet_swap_first (q : ℕ → PlanarPoint ℝ) (a b c : ℕ) :
    polygonHDet q a b c = -polygonHDet q b a c := by
  simp only [polygonHDet, planarDet, Prod.fst_sub, Prod.snd_sub]
  ring
private theorem hdet_swap_last (q : ℕ → PlanarPoint ℝ) (a b c : ℕ) :
    polygonHDet q a b c = -polygonHDet q a c b := by
  simp only [polygonHDet, planarDet, Prod.fst_sub, Prod.snd_sub]
  ring

/-- Generalizes the ordered-triple argument private to ShortEdgeCyclicG1. -/
theorem bounded_hdet_ne_of_distinct
    (q : ℕ → PlanarPoint ℝ) (N : ℕ) (hq : CoreHGeneric q N)
    (i k j : ℕ) (hi : i ≤ N) (hk : k ≤ N) (hj : j ≤ N)
    (hik : i ≠ k) (hkj : k ≠ j) (hij : i ≠ j) :
    polygonHDet q i k j ≠ 0 := by
  by_cases hik' : i < k
  · by_cases hkj' : k < j
    · exact hq i k j hik' hkj' hj
    · have hjk : j < k := by omega
      by_cases hij' : i < j
      · rw [hdet_swap_last]
        exact neg_ne_zero.mpr (hq i j k hij' hjk hk)
      · have hji : j < i := by omega
        rw [hdet_rotate q i k j, hdet_rotate q k j i]
        exact hq j i k hji hik' hk
  · have hki : k < i := by omega
    by_cases hij' : i < j
    · rw [hdet_swap_first]
      exact neg_ne_zero.mpr (hq k i j hki hij' hj)
    · have hji : j < i := by omega
      by_cases hkj' : k < j
      · rw [hdet_rotate]
        exact hq k j i hkj' hji hi
      · have hjk : j < k := by omega
        rw [hdet_rotate q i k j, hdet_swap_first q k j i]
        exact neg_ne_zero.mpr (hq j k i hjk hki hi)

/-- Every actual cap core inherits G1 from the full moving open word. -/
theorem lineCapCore_noncollinear_of_coreHGeneric
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hq : CoreHGeneric q n)
    (a b : Fin n) (hab : a.val < b.val) :
    cyclicNoncollinear (lineCapCore q a b) := by
  let idx : Fin (b.val-a.val+1+1) → ℕ :=
    fun r => if r.val=0 then 0 else a.val+r.val
  have hmono : StrictMono idx := by
    intro x y hxy
    have hv : x.val < y.val := hxy
    have hy : y.val ≠ 0 := by omega
    by_cases hx : x.val=0
    · simp only [idx, if_pos hx, if_neg hy]
      omega
    · simp only [idx, if_neg hx, if_neg hy]
      omega
  have hbound : ∀ r, idx r ≤ n := by
    intro r
    have hr := r.isLt
    have hb := b.isLt
    by_cases hz : r.val=0
    · simp only [idx, if_pos hz]
      exact Nat.zero_le n
    · simp only [idx,if_neg hz]
      omega
  have heval : ∀ r, lineCapCore q a b r = q (idx r) := by
    intro r
    by_cases hz : r.val = 0
    · simp only [lineCapCore, capSubwordFin, idx, if_pos hz]
    · simp only [lineCapCore, capSubwordFin, idx, if_neg hz]
  intro A B C hAB hBC hAC
  change planarDet (lineCapCore q a b B-lineCapCore q a b C)
    (lineCapCore q a b A-lineCapCore q a b C) ≠ 0
  rw [heval A,heval B,heval C]
  exact bounded_hdet_ne_of_distinct q n hq (idx A) (idx B) (idx C)
    (hbound A) (hbound B) (hbound C)
    (fun h => hAB (hmono.injective h))
    (fun h => hBC (hmono.injective h))
    (fun h => hAC (hmono.injective h))

/-- One punctured radius gives G1 for every lineCapCore, even when critical roots
coincide. Neither root injectivity nor selected clipped-cap genericity is used. -/
theorem exists_punctured_lineCap_G1
    (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hzero : (q 0).2=0)
    (hoff : ∀ i, 0 < i → i ≤ n → (q i).2 ≠ 0)
    (hdistinct : ∀ i j, 0 < i → i ≤ n → 0 < j → j ≤ n → i ≠ j → q i ≠ q j)
    (hpositive : ∀ i j k, 0 < i → i < j → j < k → k ≤ n → polygonHDet q i j k ≠ 0)
    (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
      ∀ a b : Fin n, a.val < b.val →
        cyclicNoncollinear (lineCapCore (horizontalMove q (t+s)) a b) := by
  obtain ⟨δ,hδ,hgood⟩ := exists_punctured_radius (criticalTimes q n) t
  refine ⟨δ,hδ,?_⟩
  intro s hs hsδ a b hab
  have hcore : CoreHGeneric (horizontalMove q (t+s)) n :=
    (horizontalMove_coreHGeneric_iff_not_critical q n hzero hoff hdistinct hpositive (t+s)).2
      (hgood s hs hsδ)
  exact lineCapCore_noncollinear_of_coreHGeneric _ n hcore a b hab

/-- Once a concrete finite bad-time set is established, this is exactly the
punctured local-cap hypothesis used by ConcreteCapMatrix, at every center. -/
theorem finite_bad_times_imply_localCaps
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (T : Finset ℝ)
    (hgood : ∀ t : ℝ, t ∉ T → ∀ a b : Fin n, a.val < b.val →
      CyclicGeneric (lineCapCore (horizontalMove q t) a b)) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
      ∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b) := by
  obtain ⟨δ,hδ,havoid⟩ := exists_punctured_radius T t
  exact ⟨δ,hδ,fun s hs hsb => hgood (t+s) (havoid s hs hsb)⟩

/-- The offset at which the horizontal moving point lies on the carrier AX. -/
noncomputable def alignmentTime (b : ℝ) (A X : PlanarPoint ℝ) : ℝ :=
  (A.1*X.2-X.1*A.2)/(X.2-A.2)-b

/-- An off-line anchor and a distinct point can align with the moving point
at at most one time. Horizontal carriers never align. -/
theorem alignment_det_ne (b t : ℝ) (A X : PlanarPoint ℝ)
    (hA : A.2 ≠ 0) (hXA : X ≠ A) (ht : t ≠ alignmentTime b A X) :
    planarDet (X-A) ((b+t,0)-A) ≠ 0 := by
  intro hz
  by_cases hd : X.2-A.2 = 0
  · have hy : X.2=A.2 := sub_eq_zero.mp hd
    have hp : (X.1-A.1)*(-A.2)=0 := by
      simpa [planarDet,hy] using hz
    have hx : X.1=A.1 := sub_eq_zero.mp
      ((mul_eq_zero.mp hp).resolve_right (neg_ne_zero.mpr hA))
    exact hXA (Prod.ext hx hy)
  · apply ht
    unfold alignmentTime
    apply (eq_sub_iff_add_eq).2
    apply (eq_div_iff hd).2
    simp only [planarDet,Prod.fst_sub,Prod.snd_sub] at hz
    nlinarith

/-- The moving edge cannot contain a point that is not on its carrier. -/
theorem moving_segment_avoids_of_alignment_det_ne (b t : ℝ)
    (A X : PlanarPoint ℝ)
    (h : planarDet (X-A) ((b+t,0)-A) ≠ 0) :
    ¬ OnOpenSegment (b+t,0) A X := by
  intro hmem
  have hz := onOpenSegment_carrier_det_zero hmem
  apply h
  calc
    planarDet (X-A) ((b+t,0)-A) = planarDet (A-(b+t,0)) (X-(b+t,0)) := by
      simp only [planarDet,Prod.fst_sub,Prod.snd_sub]
      ring
    _ = 0 := hz

/-- G1 excludes every polygon vertex from every edge's open interior,
including the incident endpoint cases. G2 is not needed. -/
theorem open_edge_point_ne_vertex {n : ℕ} (hn : 3 ≤ n)
    (R : Fin n → PlanarPoint ℝ) (hR : cyclicNoncollinear R)
    (e r : Fin n) (X : PlanarPoint ℝ) (hX : edgeInterior R e X) : X ≠ R r := by
  have hinj := cyclicNoncollinear_injective hn R hR
  have hends : R e ≠ R (cyclicSuccessor e) := by
    intro hh
    exact cyclicSuccessor_ne_self (by omega) e (hinj hh).symm
  intro hEq
  by_cases hr : r=e
  · subst r
    exact onOpenSegment_ne_left hends hX hEq
  · by_cases hrs : r=cyclicSuccessor e
    · subst r
      exact onOpenSegment_ne_right hends hX hEq
    · apply cyclic_vertex_not_in_nonincident_edge hn R hR e r hr hrs
      simpa only [hEq] using hX

/-- A finite over-approximation of every moving-leg/fixed-crossing collision
for a fixed vertex set. The closing edge of R may add harmless extra times. -/
noncomputable def crossingAlignmentTimes {n : ℕ}
    (R : Fin n → PlanarPoint ℝ) (b : ℝ) : Finset ℝ := by
  classical
  exact Finset.univ.image (fun z : Fin n × PolygonCrossing R =>
    alignmentTime b (R z.1) (crossingPoint R z.2))

/-- Away from the finite times, no moving edge meets any fixed double crossing. -/
theorem moving_edge_avoids_crossing {n : ℕ} (hn : 3 ≤ n)
    (R : Fin n → PlanarPoint ℝ) (hR : cyclicNoncollinear R)
    (hoff : ∀ r, (R r).2 ≠ 0) (b t : ℝ)
    (ht : t ∉ crossingAlignmentTimes R b) (r : Fin n) (c : PolygonCrossing R) :
    ¬ OnOpenSegment (b+t,0) (R r) (crossingPoint R c) := by
  apply moving_segment_avoids_of_alignment_det_ne
  apply alignment_det_ne b t (R r) (crossingPoint R c) (hoff r)
  · exact open_edge_point_ne_vertex hn R hR c.val.1 r _ (crossingPoint_mem_left R c)
  · intro heq
    apply ht
    classical
    unfold crossingAlignmentTimes
    exact Finset.mem_image.mpr ⟨(r,c),Finset.mem_univ _,heq.symm⟩

/-- This is the substantive G2 collision case: one moving leg and two
arbitrary distinct fixed polygon edges. No fixed-polygon G2 is assumed. -/
theorem no_triple_with_moving_edge {n : ℕ} (hn : 3 ≤ n)
    (R : Fin n → PlanarPoint ℝ) (hR : cyclicNoncollinear R)
    (hoff : ∀ r, (R r).2 ≠ 0) (b t : ℝ)
    (ht : t ∉ crossingAlignmentTimes R b)
    (r e f : Fin n) (X : PlanarPoint ℝ) (hef : e ≠ f)
    (hm : OnOpenSegment (b+t,0) (R r) X)
    (he : edgeInterior R e X) (hf : edgeInterior R f X) : False := by
  rcases lt_or_gt_of_ne hef with hlt | hgt
  · let c : PolygonCrossing R := ⟨(e,f),hlt,⟨X,he,hf⟩⟩
    have hpoint : X=crossingPoint R c := crossingPoint_eq_of_mem hn R hR c X he hf
    exact moving_edge_avoids_crossing hn R hR hoff b t ht r c (hpoint ▸ hm)
  · let c : PolygonCrossing R := ⟨(f,e),hgt,⟨X,hf,he⟩⟩
    have hpoint : X=crossingPoint R c := crossingPoint_eq_of_mem hn R hR c X hf he
    exact moving_edge_avoids_crossing hn R hR hoff b t ht r c (hpoint ▸ hm)

/-- A uniform punctured neighborhood excludes the complete one-moving-leg
G2 obstruction for every anchor and every pair of fixed edges. -/
theorem exists_punctured_no_moving_triples {n : ℕ} (hn : 3 ≤ n)
    (R : Fin n → PlanarPoint ℝ) (hR : cyclicNoncollinear R)
    (hoff : ∀ r, (R r).2 ≠ 0) (b t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
      ∀ r e f : Fin n, ∀ X : PlanarPoint ℝ, e ≠ f →
      ¬ (OnOpenSegment (b+(t+s),0) (R r) X ∧
        edgeInterior R e X ∧ edgeInterior R f X) := by
  obtain ⟨δ,hδ,havoid⟩ := exists_punctured_radius (crossingAlignmentTimes R b) t
  refine ⟨δ,hδ,?_⟩
  intro s hs hsb r e f X hef ⟨hm,he,hf⟩
  exact no_triple_with_moving_edge hn R hR hoff b (t+s)
    (havoid s hs hsb) r e f X hef hm he hf

/-- The actual positive-index fixed vertices, without the moving base point. -/
def positiveWord (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Fin n → PlanarPoint ℝ :=
  fun i => q (i.val+1)

/-- G2 for only the actual consecutive fixed edges; the artificial closing
edge of positiveWord is deliberately excluded. -/
def OpenArcG2 (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Prop :=
  ∀ i j k : Fin n, i.val+1 < n → j.val+1 < n → k.val+1 < n →
    i ≠ j → j ≠ k → i ≠ k → ∀ X : PlanarPoint ℝ,
      ¬ (edgeInterior (positiveWord q n) i X ∧
         edgeInterior (positiveWord q n) j X ∧
         edgeInterior (positiveWord q n) k X)

theorem positiveWord_noncollinear (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (hp : ∀ i j k, 0 < i → i < j → j < k → k ≤ n → polygonHDet q i j k ≠ 0) :
    cyclicNoncollinear (positiveWord q n) := by
  let w : ℕ → PlanarPoint ℝ := fun i => q (i+1)
  have hw : CoreHGeneric w (n-1) := by
    intro i j k hij hjk hkn
    have hn : 0 < n := by omega
    exact hp (i+1) (j+1) (k+1) (by omega) (by omega) (by omega) (by omega)
  intro A B C hAB hBC hAC
  exact bounded_hdet_ne_of_distinct w (n-1) hw A.val B.val C.val
    (by have := A.isLt; omega) (by have := B.isLt; omega) (by have := C.isLt; omega)
    (fun h => hAB (Fin.ext h)) (fun h => hBC (Fin.ext h)) (fun h => hAC (Fin.ext h))

private theorem successor_val_of_not_last {N : ℕ} (i : Fin N) (hi : i.val+1 < N) :
    (cyclicSuccessor i).val=i.val+1 := by
  simp [cyclicSuccessor,cyclicVertexIndex,Nat.mod_eq_of_lt hi]

private theorem successor_val_of_last {N : ℕ} (i : Fin N) (hi : i.val+1=N) :
    (cyclicSuccessor i).val=0 := by
  simp [cyclicSuccessor,cyclicVertexIndex,hi]

private theorem cap_vertex_positive (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (t : ℝ) (r : Fin (b.val-a.val+1+1)) (hr : 0 < r.val) :
    lineCapCore (horizontalMove q t) a b r = q (a.val+r.val) := by
  have hr0 : r.val ≠ 0 := by omega
  have ha : a.val+r.val ≠ 0 := by omega
  simp only [lineCapCore,capSubwordFin,if_neg hr0,horizontalMove,
    EndpointEventGeometry.moveEndpoint,if_neg ha]

private theorem cap_vertex_zero (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (t : ℝ) (hzero : (q 0).2=0)
    (r : Fin (b.val-a.val+1+1)) (hr : r.val=0) :
    lineCapCore (horizontalMove q t) a b r = ((q 0).1+t,0) := by
  simp only [lineCapCore,capSubwordFin,if_pos hr,horizontalMove,
    EndpointEventGeometry.moveEndpoint,if_pos rfl]
  apply Prod.ext <;> simp [hzero]

/-- A moving cap edge is one of the two legs at its distinguished vertex. -/
def IsMovingCapEdge {n : ℕ} (a b : Fin n)
    (e : Fin (b.val-a.val+1+1)) : Prop :=
  e.val=0 ∨ e.val=b.val-a.val+1

theorem moving_cap_edge_mem (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (hab : a.val < b.val) (t : ℝ) (hzero : (q 0).2=0)
    (e : Fin (b.val-a.val+1+1)) (X : PlanarPoint ℝ)
    (hm : IsMovingCapEdge a b e)
    (he : edgeInterior (lineCapCore (horizontalMove q t) a b) e X) :
    ∃ r : Fin n, OnOpenSegment ((q 0).1+t,0) (positiveWord q n r) X := by
  rcases hm with he0 | hem
  · have hs : (cyclicSuccessor e).val=1 := by
      rw [successor_val_of_not_last e (by omega),he0]
    refine ⟨a,?_⟩
    change OnOpenSegment _ _ X at he
    rw [cap_vertex_zero q n a b t hzero e he0,
      cap_vertex_positive q n a b t (cyclicSuccessor e) (by omega)] at he
    simpa only [hs,positiveWord] using he
  · have hs : (cyclicSuccessor e).val=0 :=
      successor_val_of_last e (by omega)
    have hp : 0 < e.val := by omega
    refine ⟨b,?_⟩
    change OnOpenSegment _ _ X at he
    rw [cap_vertex_positive q n a b t e hp,
      cap_vertex_zero q n a b t hzero (cyclicSuccessor e) hs] at he
    have hadd : a.val+e.val=b.val+1 := by omega
    simpa only [hadd,positiveWord] using onOpenSegment_symm he

theorem fixed_cap_edge_mem (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (hab : a.val < b.val) (t : ℝ)
    (e : Fin (b.val-a.val+1+1)) (X : PlanarPoint ℝ)
    (hm : ¬ IsMovingCapEdge a b e)
    (he : edgeInterior (lineCapCore (horizontalMove q t) a b) e X) :
    ∃ i : Fin n, 0 < e.val ∧ i.val=a.val+e.val-1 ∧ i.val+1 < n ∧
      edgeInterior (positiveWord q n) i X := by
  have he0 : e.val ≠ 0 := fun h => hm (Or.inl h)
  have hel : e.val ≠ b.val-a.val+1 := fun h => hm (Or.inr h)
  have heb := e.isLt
  have hp : 0 < e.val := by omega
  have hs : (cyclicSuccessor e).val=e.val+1 := successor_val_of_not_last e (by omega)
  have hb := b.isLt
  let i : Fin n := ⟨a.val+e.val-1,by omega⟩
  have hi : i.val+1 < n := by dsimp [i];omega
  have his : (cyclicSuccessor i).val=i.val+1 := successor_val_of_not_last i hi
  refine ⟨i,hp,rfl,hi,?_⟩
  change OnOpenSegment _ _ X at he ⊢
  rw [cap_vertex_positive q n a b t e hp,
    cap_vertex_positive q n a b t (cyclicSuccessor e) (by omega)] at he
  have hfirst : i.val+1=a.val+e.val := by dsimp [i];omega
  have hnext : (cyclicSuccessor i).val+1=a.val+(cyclicSuccessor e).val := by omega
  simpa only [positiveWord,hfirst,hnext] using he

private theorem moving_cap_edges_disjoint (q : ℕ → PlanarPoint ℝ) (n : ℕ)
    (a b : Fin n) (hab : a.val < b.val) (t : ℝ)
    (hg : cyclicNoncollinear (lineCapCore (horizontalMove q t) a b))
    (e f : Fin (b.val-a.val+1+1)) (X : PlanarPoint ℝ)
    (he : IsMovingCapEdge a b e) (hf : IsMovingCapEdge a b f) (hef : e ≠ f)
    (hem : edgeInterior (lineCapCore (horizontalMove q t) a b) e X)
    (hfm : edgeInterior (lineCapCore (horizontalMove q t) a b) f X) : False := by
  have hne : e.val ≠ f.val := fun h => hef (Fin.ext h)
  rcases he with he0 | hel <;> rcases hf with hf0 | hfl
  · omega
  · have hs : cyclicSuccessor f=e := by
      apply Fin.ext
      rw [successor_val_of_last f (by omega),he0]
    exact cyclic_adjacent_interiors_disjoint (by omega)
      (lineCapCore (horizontalMove q t) a b) hg f X hfm (hs ▸ hem)
  · have hs : cyclicSuccessor e=f := by
      apply Fin.ext
      rw [successor_val_of_last e (by omega),hf0]
    exact cyclic_adjacent_interiors_disjoint (by omega)
      (lineCapCore (horizontalMove q t) a b) hg e X hem (hs ▸ hfm)
  · omega

/-- The finite alignment exclusion plus fixed-open-arc G2 gives the exact
cyclic G2 condition of each cap core. -/
theorem lineCapCore_G2_of_avoids_alignment
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hR : cyclicNoncollinear (positiveWord q n))
    (hoff : ∀ r : Fin n, (positiveWord q n r).2 ≠ 0)
    (hopen : OpenArcG2 q n) (hzero : (q 0).2=0)
    (a b : Fin n) (hab : a.val < b.val) (t : ℝ)
    (hg : cyclicNoncollinear (lineCapCore (horizontalMove q t) a b))
    (ht : t ∉ crossingAlignmentTimes (positiveWord q n) (q 0).1) :
    cyclicNoTripleIntersections (lineCapCore (horizontalMove q t) a b) := by
  intro e f g X hef hfg heg ⟨he,hf,hgmem⟩
  have hone : ∀ E F G : Fin (b.val-a.val+1+1),
      IsMovingCapEdge a b E → ¬ IsMovingCapEdge a b F → ¬ IsMovingCapEdge a b G →
      F ≠ G →
      edgeInterior (lineCapCore (horizontalMove q t) a b) E X →
      edgeInterior (lineCapCore (horizontalMove q t) a b) F X →
      edgeInterior (lineCapCore (horizontalMove q t) a b) G X → False := by
    intro E F G hE hF hG hFG hEm hFm hGm
    obtain ⟨r,hr⟩ := moving_cap_edge_mem q n a b hab t hzero E X hE hEm
    obtain ⟨i,hFp,hiv,hi,him⟩ := fixed_cap_edge_mem q n a b hab t F X hF hFm
    obtain ⟨j,hGp,hjv,hj,hjm⟩ := fixed_cap_edge_mem q n a b hab t G X hG hGm
    have hij : i ≠ j := by
      intro hh
      have hv := congrArg Fin.val hh
      have hFGv : F.val ≠ G.val := fun h => hFG (Fin.ext h)
      omega
    exact no_triple_with_moving_edge hn (positiveWord q n) hR hoff (q 0).1 t ht
      r i j X hij hr him hjm
  by_cases hem : IsMovingCapEdge a b e
  · by_cases hfm : IsMovingCapEdge a b f
    · exact moving_cap_edges_disjoint q n a b hab t hg e f X hem hfm hef he hf
    · by_cases hgm : IsMovingCapEdge a b g
      · exact moving_cap_edges_disjoint q n a b hab t hg e g X hem hgm heg he hgmem
      · exact hone e f g hem hfm hgm hfg he hf hgmem
  · by_cases hfm : IsMovingCapEdge a b f
    · by_cases hgm : IsMovingCapEdge a b g
      · exact moving_cap_edges_disjoint q n a b hab t hg f g X hfm hgm hfg hf hgmem
      · exact hone f e g hfm hem hgm heg hf he hgmem
    · by_cases hgm : IsMovingCapEdge a b g
      · exact hone g e f hgm hem hfm hef hgmem he hf
      · obtain ⟨i,hep,hiv,hi,him⟩ := fixed_cap_edge_mem q n a b hab t e X hem he
        obtain ⟨j,hfp,hjv,hj,hjm⟩ := fixed_cap_edge_mem q n a b hab t f X hfm hf
        obtain ⟨k,hgp,hkv,hk,hkm⟩ := fixed_cap_edge_mem q n a b hab t g X hgm hgmem
        have hij : i ≠ j := by
          intro hh
          have hv := congrArg Fin.val hh
          have hnev : e.val ≠ f.val := fun h => hef (Fin.ext h)
          omega
        have hjk : j ≠ k := by
          intro hh
          have hv := congrArg Fin.val hh
          have hnev : f.val ≠ g.val := fun h => hfg (Fin.ext h)
          omega
        have hik : i ≠ k := by
          intro hh
          have hv := congrArg Fin.val hh
          have hnev : e.val ≠ g.val := fun h => heg (Fin.ext h)
          omega
        exact hopen i j k hi hj hk hij hjk hik X ⟨him,hjm,hkm⟩

/-- Concrete finite bad times for all cap cores of a fixed arc. -/
noncomputable def localCapBadTimes (q : ℕ → PlanarPoint ℝ) (n : ℕ) : Finset ℝ :=
  criticalTimes q n ∪ crossingAlignmentTimes (positiveWord q n) (q 0).1

/-- Every cap core is generic away from the explicitly defined finite bad times.
No distinct-root hypothesis and no genericity of selected clipped caps is used. -/
theorem lineCapCore_generic_of_not_bad
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hzero : (q 0).2=0)
    (hoff : ∀ i, 0 < i → i ≤ n → (q i).2 ≠ 0)
    (hdistinct : ∀ i j, 0 < i → i ≤ n → 0 < j → j ≤ n → i ≠ j → q i ≠ q j)
    (hpositive : ∀ i j k, 0 < i → i < j → j < k → k ≤ n → polygonHDet q i j k ≠ 0)
    (hopen : OpenArcG2 q n) (t : ℝ) (ht : t ∉ localCapBadTimes q n)
    (a b : Fin n) (hab : a.val < b.val) :
    CyclicGeneric (lineCapCore (horizontalMove q t) a b) := by
  have htc : t ∉ criticalTimes q n := by
    intro hh
    exact ht (Finset.mem_union_left _ hh)
  have hta : t ∉ crossingAlignmentTimes (positiveWord q n) (q 0).1 := by
    intro hh
    exact ht (Finset.mem_union_right _ hh)
  have hcore := (horizontalMove_coreHGeneric_iff_not_critical q n hzero hoff
    hdistinct hpositive t).2 htc
  have hG1 := lineCapCore_noncollinear_of_coreHGeneric _ n hcore a b hab
  refine ⟨by omega,hG1,?_⟩
  apply lineCapCore_G2_of_avoids_alignment q n hn
    (positiveWord_noncollinear q n hpositive) _ hopen hzero a b hab t hG1 hta
  intro r
  exact hoff (r.val+1) (by omega) (by have := r.isLt;omega)

/-- The finite bad-time argument proves the actual hlocalCaps conclusion
from the fixed arc's geometric hypotheses, at every real center. -/
theorem localCaps_of_openArcG2
    (q : ℕ → PlanarPoint ℝ) (n : ℕ) (hn : 3 ≤ n)
    (hzero : (q 0).2=0)
    (hoff : ∀ i, 0 < i → i ≤ n → (q i).2 ≠ 0)
    (hdistinct : ∀ i j, 0 < i → i ≤ n → 0 < j → j ≤ n → i ≠ j → q i ≠ q j)
    (hpositive : ∀ i j k, 0 < i → i < j → j < k → k ≤ n → polygonHDet q i j k ≠ 0)
    (hopen : OpenArcG2 q n) (t : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ s : ℝ, 0 < |s| → |s| < δ →
      ∀ a b : Fin n, a.val < b.val →
        CyclicGeneric (lineCapCore (horizontalMove q (t+s)) a b) := by
  apply finite_bad_times_imply_localCaps q n (localCapBadTimes q n)
  intro v hv a b hab
  exact lineCapCore_generic_of_not_bad q n hn hzero hoff hdistinct hpositive hopen
    v hv a b hab






















end DirectGLSSW.ExtendedReturnLocalCaps
