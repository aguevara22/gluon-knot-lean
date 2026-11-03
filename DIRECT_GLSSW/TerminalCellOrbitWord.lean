import FirstCellOrbitWord

set_option autoImplicit false
namespace DirectGLSSW.TerminalCellOrbitWord
open MixedConsecutiveCapWord MixedEdgeSupportOrder MixedEdgeRetainedWord
open DaughterFirstReturn CyclicAnchorInterval FirstCellOrbitWord
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/- Own helpers copied from immutable InternalCellOrbitWord with recorded provenance; recompiled against178. -/
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



/-- Actual list order bounds every selected return rank by the final selected return rank. -/
theorem last_return_rank_ge (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q)
    (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (hlen : 0 < L.length)
    (d : DirectGLSSW.EdgeChord q e) (hd : d ∈ L) :
    complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e d)) ≤
    complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨L.length-1,by omega⟩))) := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hd
  by_cases hj : j.val=L.length-1
  · have heq : j = ⟨L.length-1,by omega⟩ := Fin.ext hj
    simp only [heq]
    exact le_rfl
  · have hlt : j < (⟨L.length-1,by omega⟩ : Fin L.length) := by
      change j.val < L.length-1
      have := j.isLt
      omega
    have hp := (List.pairwise_iff_get.mp hL.2) j ⟨L.length-1,by omega⟩ hlt
    exact le_of_lt ((returnVisitBefore_iff_rank_lt q hq e _ _).mp hp.2)

/-- The terminal nonempty cell's actual daughter word is precisely its proposed cell word. -/
theorem daughterPointList_terminal_eq_cellEventWord
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (hlen : 0 < L.length) (i : Fin (L.length+1)) (hiLast : i.val=L.length) :
    daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q) := by
  classical
  rcases i with ⟨iv,hiv⟩
  change iv=L.length at hiLast
  subst iv
  let i : Fin (L.length+1) := Fin.last L.length
  let c := L.get (⟨L.length-1,by omega⟩ : Fin L.length)
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e c)
  let r := complementaryEventRank e f
  have hri := return_rank_interior q hq e c
  have hrn : r+2<n := hri.2
  let m := n-1-(r+1)
  have hm : 0 < m := by dsimp [m]; omega
  let a : Fin m → Fin n := fun j => cyclicVertexIndex e (r+1+j.val)
  have har : ∀ j : Fin m, complementaryEventRank e (a j) = r+1+j.val := by
    intro j
    apply complementaryRank_cyclicVertexIndex
    have := j.isLt
    dsimp [m] at this
    omega
  have ha : cellInteriorAnchors q hq e L i = List.ofFn a :=
    cellInteriorAnchors_terminal_eq_interval q hq e L hL hlen
  let S := supportOfList q e L
  let p := retainedDartPermutation q hq.g2 S
  let R : RetainedEvent q S := ⟨cellRootEvent q e L i,cellRootEvent_retained q e L i⟩
  let U : RetainedEvent q S := ⟨cellLeftEvent q e L i,cellLeftEvent_retained q e L i⟩
  let A : Fin m → RetainedEvent q S := fun j => ⟨Sum.inl (a j),by trivial⟩
  have hroot : cellRootEvent q e L i = Sum.inl e := by
    simp only [cellRootEvent,i,Fin.val_last,dif_neg (Nat.lt_irrefl L.length)]
  have hleftEvent : cellLeftEvent q e L i = Sum.inr (DirectGLSSW.returnVisit q e c) := by
    simp only [cellLeftEvent,i,Fin.val_last,dif_neg (ne_of_gt hlen),c]
  have hr : p R = U := by
    apply Subtype.ext
    dsimp only [p,R,U,S]
    simp only [hroot]
    exact retainedDart_cellRoot_terminal_to_left q hq e hflat hleft L hL hlen
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
    have hne : a ⟨j,by omega⟩ ≠ e := by
      intro heq
      have hh := congrArg (complementaryEventRank e) heq
      rw [har,complementaryEventRank_self] at hh
      change r+1+j=n-1 at hh
      dsimp [m] at hj
      omega
    have hno : ∀ d, d ∈ L → crossingVisitEdge q (DirectGLSSW.returnVisit q e d) ≠ a ⟨j,by omega⟩ := by
      intro d hd heq
      have hmax := last_return_rank_ge q hq e L hL hlen d hd
      have hh := congrArg (complementaryEventRank e) heq
      rw [har] at hh
      change complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e d)) ≤ r at hmax
      rw [hh] at hmax
      change r+1+j ≤ r at hmax
      omega
    have hroute := FirstCellOrbitWord.retained_anchor_next q hq e (a ⟨j,by omega⟩) L hne hno
    have hanext : cyclicSuccessor (a ⟨j,by omega⟩) = a ⟨j+1,hj⟩ := by
      change cyclicSuccessor (cyclicVertexIndex e (r+1+j)) = cyclicVertexIndex e (r+1+(j+1))
      rw [index_next e (r+1+j) (by dsimp [m] at hj; omega)]
      congr 1
    rw [hanext] at hroute
    exact hroute
  have he : p (A ⟨m-1,by omega⟩) = R := by
    apply Subtype.ext
    have hidx : r+1+(m-1)=n-2 := by dsimp [m]; omega
    have hlast : a ⟨m-1,by omega⟩ = cyclicVertexIndex e (n-2) := by
      change cyclicVertexIndex e (r+1+(m-1)) = _
      rw [hidx]
    change (retainedDartPermutation q hq.g2 S ⟨Sum.inl (a ⟨m-1,by omega⟩),_⟩).val = cellRootEvent q e L i
    simp only [hlast,hroot]
    exact retainedDart_terminal_last_interior_to_root q hq e L hL hlen
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
  change daughterPointList q hq.g2 S (cellRootEvent q e L i) =
    (cellEventWord q hq e L i).map (polygonEventPoint q)
  rw [daughterPointList_eq_retainedOrbitWord q hq.g2 S _ (cellRootEvent_retained q e L i)]
  change (PermutationOrbits.orbitWord p R).map (fun x => polygonEventPoint q x.val) = _
  rw [hword]
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map (polygonEventPoint q)) hmap

end DirectGLSSW.TerminalCellOrbitWord




