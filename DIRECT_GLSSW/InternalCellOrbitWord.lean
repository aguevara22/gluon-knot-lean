import CellAnchorInterval
import OrbitWordListChain

set_option autoImplicit false
namespace DirectGLSSW.InternalCellOrbitWord
open MixedConsecutiveCapWord MixedEdgeSupportOrder MixedEdgeRetainedWord
open DaughterFirstReturn CyclicAnchorInterval

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/-- The public two label-order routes combine into a wrap-independent return successor. -/
theorem retained_return_next (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q)
    (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (c : DirectGLSSW.EdgeChord q e) (hc : c ∈ L) :
    (retainedDartPermutation q hq.g2 (supportOfList q e L)
      ⟨Sum.inr (DirectGLSSW.returnVisit q e c), by
        classical
        change c.val ∈ supportOfList q e L
        exact Finset.mem_image.mpr ⟨c,List.mem_toFinset.mpr hc,rfl⟩⟩).val =
      Sum.inl (cyclicSuccessor (crossingVisitEdge q (DirectGLSSW.returnVisit q e c))) := by
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e c)
  by_cases hn : f.val+1 < n
  · exact retainedDart_returnVisit_to_nextAnchor q hq e L c hc hn
  · have hf : f.val+1=n := by have := f.isLt; omega
    have hs : cyclicSuccessor f = (⟨0,by omega⟩ : Fin n) := by
      apply Fin.ext
      rw [cyclicSuccessor,cyclicVertexIndex_val f (k:=0) (by omega)]
      simp only [Nat.add_zero]
      simp [hf]
    change _ = Sum.inl (cyclicSuccessor f)
    rw [hs]
    exact retainedDart_returnVisit_to_zeroAnchor q hq e L c hc hf

private theorem index_of_rank (e f : Fin n) :
    cyclicVertexIndex e (complementaryEventRank e f) = f := by
  apply complementaryEventRank_injective e
  exact complementaryRank_cyclicVertexIndex e _ (complementaryRank_lt_size e f)

private theorem index_next (e : Fin n) (k : ℕ) (hk : k+1<n) :
    cyclicSuccessor (cyclicVertexIndex e k) = cyclicVertexIndex e (k+1) := by
  have ha : cyclicVertexIndex e k ≠ e := by
    intro h
    have hr := congrArg (complementaryEventRank e) h
    rw [complementaryRank_cyclicVertexIndex e k (by omega),complementaryEventRank_self] at hr
    omega
  apply complementaryEventRank_injective e
  rw [complementaryEventRank_cyclicSuccessor e _ ha,
    complementaryRank_cyclicVertexIndex e k (by omega),
    complementaryRank_cyclicVertexIndex e (k+1) hk]

/-- Local list bookkeeping for the nonempty internal anchor interval. -/
private theorem closed_interval_chain {α : Type*} (p : α → α) (root left : α)
    {m : ℕ} (hm : 0<m) (f : Fin m → α)
    (hr : p root = left) (hl : p left = f ⟨0,hm⟩)
    (hs : ∀ j : ℕ, ∀ hj : j+1<m, p (f ⟨j,by omega⟩) = f ⟨j+1,hj⟩)
    (he : p (f ⟨m-1,by omega⟩) = root) :
    List.Chain' (fun a b => p a = b) ((root::left::List.ofFn f) ++ [root]) := by
  simp only [List.cons_append,List.chain'_cons]
  refine ⟨hr,?_⟩
  apply List.chain'_iff_get.mpr
  intro j hj
  simp only [List.length_cons,List.length_append,List.length_ofFn,List.length_singleton,List.length_nil] at hj
  cases j with
  | zero => simpa [List.get_eq_getElem, List.getElem_append, hm] using hl
  | succ j =>
    simp only [List.get_eq_getElem,List.getElem_cons_succ]
    have hjm : j<m := by omega
    by_cases hn : j+1<m
    · simpa [List.get_eq_getElem,List.getElem_append,hjm,hn] using hs j hn
    · have hlast : j=m-1 := by omega
      have hend : j+1=m := by omega
      have hrj : p (f ⟨j,hjm⟩) = root := by simpa only [hlast] using he
      simpa [List.get_eq_getElem,List.getElem_append,hjm,hn,hend] using hrj


/-- An internal cell's actual retained orbit has exactly its proposed point word.
The horizontal leftward chosen-edge geometry is used for root-to-previous-return routing. -/
theorem daughterPointList_internal_eq_cellEventWord
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (i : Fin (L.length+1)) (hi0 : 0 < i.val) (hiL : i.val < L.length) :
    daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q) := by
  classical
  let c := L.get (⟨i.val-1,by omega⟩ : Fin L.length)
  let d := L.get (⟨i.val,hiL⟩ : Fin L.length)
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e c)
  let g := crossingVisitEdge q (DirectGLSSW.returnVisit q e d)
  let r := complementaryEventRank e f
  let s := complementaryEventRank e g
  have hrs : r<s := CellAnchorRanks.internal_return_ranks_strict q hq e L hL i hi0 hiL
  have hsn : s<n := complementaryRank_lt_size e g
  let m := s-r
  have hm : 0<m := by dsimp [m]; omega
  let a : Fin m → Fin n := fun j => cyclicVertexIndex e (r+1+j.val)
  have har : ∀ j : Fin m, complementaryEventRank e (a j) = r+1+j.val := by
    intro j
    apply complementaryRank_cyclicVertexIndex
    have := j.isLt
    dsimp [m] at this
    omega
  have ha : cellInteriorAnchors q hq e L i = List.ofFn a :=
    CellAnchorInterval.cellInteriorAnchors_internal_eq_interval q hq e L hL i hi0 hiL
  have ham : ∀ j, a j ∈ cellInteriorAnchors q hq e L i := by
    intro j
    rw [ha]
    exact List.mem_ofFn.mpr ⟨j,rfl⟩
  let S := supportOfList q e L
  let p := retainedDartPermutation q hq.g2 S
  let R : RetainedEvent q S := ⟨cellRootEvent q e L i,cellRootEvent_retained q e L i⟩
  let U : RetainedEvent q S := ⟨cellLeftEvent q e L i,cellLeftEvent_retained q e L i⟩
  let A : Fin m → RetainedEvent q S := fun j => ⟨Sum.inl (a j),by trivial⟩
  have hroot : cellRootEvent q e L i = Sum.inr (DirectGLSSW.edgeVisit q e d) := by
    simp only [cellRootEvent,dif_pos hiL,d]
  have hleftEvent : cellLeftEvent q e L i = Sum.inr (DirectGLSSW.returnVisit q e c) := by
    simp only [cellLeftEvent,dif_neg (ne_of_gt hi0),c]
  have hr : p R=U := by
    apply Subtype.ext
    have hroute := retainedDart_cellRoot_to_left q hq hq.size_ge_three e hflat hleft L hL
      (⟨i.val,hiL⟩ : Fin L.length) hi0
    have hieq : Fin.castSucc (⟨i.val,hiL⟩ : Fin L.length) = i := Fin.ext rfl
    simp only [hieq] at hroute
    dsimp only [p,R,U,S]
    simp only [hroot]
    exact hroute
  have hl : p U = A ⟨0,hm⟩ := by
    apply Subtype.ext
    have hc : c ∈ L := List.get_mem L _
    have hroute := retained_return_next q hq e L c hc
    have ha0 : a ⟨0,hm⟩ = cyclicSuccessor f := by
      change cyclicVertexIndex e (r+1+0) = cyclicSuccessor f
      simp only [Nat.add_zero]
      rw [← index_next e r (by omega)]
      change cyclicSuccessor (cyclicVertexIndex e (complementaryEventRank e f)) = _
      rw [index_of_rank]
    change (retainedDartPermutation q hq.g2 S ⟨cellLeftEvent q e L i,_⟩).val = Sum.inl (a ⟨0,hm⟩)
    simp only [hleftEvent,ha0]
    exact hroute
  have hs : ∀ j : ℕ, ∀ hj : j+1<m, p (A ⟨j,by omega⟩) = A ⟨j+1,hj⟩ := by
    intro j hj
    apply Subtype.ext
    have hroute := retainedDart_interiorAnchor_successor q hq e L hL i hi0 hiL
      (a ⟨j,by omega⟩) (ham _)
    have hne : g ≠ a ⟨j,by omega⟩ := by
      intro heq
      have hh := congrArg (complementaryEventRank e) heq
      rw [har] at hh
      change s=r+1+j at hh
      dsimp [m] at hj
      omega
    have hne' : crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get ⟨i.val,hiL⟩)) ≠
        a ⟨j,by omega⟩ := hne
    rw [if_neg hne'] at hroute
    have hanext : cyclicSuccessor (a ⟨j,by omega⟩) = a ⟨j+1,hj⟩ := by
      change cyclicSuccessor (cyclicVertexIndex e (r+1+j)) = cyclicVertexIndex e (r+1+(j+1))
      rw [index_next e (r+1+j) (by dsimp [m] at hj; omega)]
      congr 1
    rw [hanext] at hroute
    exact hroute
  have he : p (A ⟨m-1,by omega⟩) = R := by
    apply Subtype.ext
    have hroute := retainedDart_interiorAnchor_successor q hq e L hL i hi0 hiL
      (a ⟨m-1,by omega⟩) (ham _)
    have heq : g = a ⟨m-1,by omega⟩ := by
      apply complementaryEventRank_injective e
      rw [har]
      change s=r+1+(m-1)
      dsimp [m]
      omega
    have heq' : crossingVisitEdge q (DirectGLSSW.returnVisit q e (L.get ⟨i.val,hiL⟩)) =
        a ⟨m-1,by omega⟩ := heq
    rw [if_pos heq'] at hroute
    change _ = cellRootEvent q e L i
    simp only [hroot]
    exact hroute
  have hmap : (R::U::List.ofFn A).map Subtype.val = cellEventWord q hq e L i := by
    rw [cellEventWord,ha]
    simp only [List.map_cons,List.map_ofFn,R,U,A]
    rfl
  have hnodup : (R::U::List.ofFn A).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hmap]
    exact cellEventWord_nodup q hq e L i
  have hchain := closed_interval_chain p R U hm A hr hl hs he
  have hword := orbitWord_eq_list_of_closed_chain p R (U::List.ofFn A) hnodup hchain
  rw [daughterPointList_eq_retainedOrbitWord q hq.g2 S _ (cellRootEvent_retained q e L i)]
  change (PermutationOrbits.orbitWord p R).map (fun x => polygonEventPoint q x.val) = _
  rw [hword]
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map (polygonEventPoint q)) hmap

end DirectGLSSW.InternalCellOrbitWord



