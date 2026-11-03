import DirectGLSSW.MixedConsecutiveCapWord
import OrbitWordListChain

set_option autoImplicit false
namespace DirectGLSSW.FirstCellOrbitWord
open MixedConsecutiveCapWord MixedEdgeSupportOrder MixedEdgeRetainedWord
open DaughterFirstReturn CyclicAnchorInterval
variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K] {n : ℕ}

/- Own index_next and closed_interval_chain helpers copied with provenance from immutable InternalCellOrbitWord. -/
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



/-- List order makes the first selected return rank minimal among the actual selected returns. -/
theorem first_return_rank_le (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q)
    (e : Fin n) (L : List (DirectGLSSW.EdgeChord q e))
    (hL : OrderedEdgeSupport q hq e L) (hlen : 0 < L.length)
    (d : DirectGLSSW.EdgeChord q e) (hd : d ∈ L) :
    complementaryEventRank e (crossingVisitEdge q
      (DirectGLSSW.returnVisit q e (L.get ⟨0,hlen⟩))) ≤
    complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e d)) := by
  obtain ⟨j,rfl⟩ := List.mem_iff_get.mp hd
  by_cases hj : j.val=0
  · have heq : j = ⟨0,hlen⟩ := Fin.ext hj
    subst j
    exact le_rfl
  · have hlt : (⟨0,hlen⟩ : Fin L.length) < j := by change 0 < j.val; omega
    have hp := (List.pairwise_iff_get.mp hL.2) ⟨0,hlen⟩ j hlt
    exact le_of_lt ((returnVisitBefore_iff_rank_lt q hq e _ _).mp hp.2)

/-- The public anchor routes combine without restricting the original label at wrap. -/
theorem retained_anchor_next (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q)
    (e a : Fin n) (L : List (DirectGLSSW.EdgeChord q e)) (hae : a ≠ e)
    (hno : ∀ d, d ∈ L → crossingVisitEdge q (DirectGLSSW.returnVisit q e d) ≠ a) :
    (retainedDartPermutation q hq.g2 (supportOfList q e L) ⟨Sum.inl a,by trivial⟩).val =
      Sum.inl (cyclicSuccessor a) := by
  by_cases hnext : a.val+1<n
  · exact retainedDart_anchor_to_nextAnchor q hq e a L hae hno hnext
  · have hf : a.val+1=n := by have := a.isLt; omega
    have hs : cyclicSuccessor a = (⟨0,by omega⟩ : Fin n) := by
      apply Fin.ext
      rw [cyclicSuccessor,cyclicVertexIndex_val a (k:=0) (by omega)]
      simp only [Nat.add_zero]
      simp [hf]
    rw [hs]
    exact retainedDart_anchor_to_nextAnchor_wrap q hq e a L hae hno hf

/-- The first nonempty cell's actual daughter word is precisely its proposed cell word. -/
theorem daughterPointList_first_eq_cellEventWord
    (q : Fin n → PlanarPoint K) (hq : CyclicGeneric q) (e : Fin n)
    (hflat : (q e).2 = (q (cyclicSuccessor e)).2)
    (hleft : (q (cyclicSuccessor e)).1 < (q e).1)
    (L : List (DirectGLSSW.EdgeChord q e)) (hL : OrderedEdgeSupport q hq e L)
    (hlen : 0 < L.length) (i : Fin (L.length+1)) (hi0 : i.val=0) :
    daughterPointList q hq.g2 (supportOfList q e L) (cellRootEvent q e L i) =
      (cellEventWord q hq e L i).map (polygonEventPoint q) := by
  classical
  rcases i with ⟨iv,hiv⟩
  change iv=0 at hi0
  subst iv
  let i : Fin (L.length+1) := ⟨0,by omega⟩
  let c := L.get (⟨0,hlen⟩ : Fin L.length)
  let f := crossingVisitEdge q (DirectGLSSW.returnVisit q e c)
  let r := complementaryEventRank e f
  have hri := return_rank_interior q hq e c
  have hrpos : 0 < r := hri.1
  have hrn : r+2<n := hri.2
  let a : Fin r → Fin n := fun j => cyclicVertexIndex e (1+j.val)
  have har : ∀ j : Fin r, complementaryEventRank e (a j) = 1+j.val := by
    intro j
    apply complementaryRank_cyclicVertexIndex
    have := j.isLt
    omega
  have ha : cellInteriorAnchors q hq e L i = List.ofFn a :=
    cellInteriorAnchors_first_eq_interval q hq e L hL hlen
  let S := supportOfList q e L
  let p := retainedDartPermutation q hq.g2 S
  let R : RetainedEvent q S := ⟨cellRootEvent q e L i,cellRootEvent_retained q e L i⟩
  let U : RetainedEvent q S := ⟨cellLeftEvent q e L i,cellLeftEvent_retained q e L i⟩
  let A : Fin r → RetainedEvent q S := fun j => ⟨Sum.inl (a j),by trivial⟩
  have hroot : cellRootEvent q e L i = Sum.inr (DirectGLSSW.edgeVisit q e c) := by
    simp only [cellRootEvent,i,Fin.val_mk,dif_pos hlen,c]
  have hr : p R = U := by
    apply Subtype.ext
    dsimp only [p,R,U,S]
    simp only [hroot]
    by_cases hnext : e.val+1<n
    · exact retainedDart_cellRoot_first_to_left q hq e hflat hleft hnext L hL hlen
    · have hlast : e.val+1=n := by have := e.isLt; omega
      exact retainedDart_cellRoot_first_to_left_lastEdge q hq hq.size_ge_three e
        hflat hleft hlast L hL hlen
  have hl : p U = A ⟨0,hrpos⟩ := by
    apply Subtype.ext
    have hroute := retainedDart_first_left_to_firstInteriorAnchor q hq e hq.size_ge_three L hL hlen
    simpa only [p,U,A,S,i,cellLeftEvent,Fin.val_mk,dif_pos rfl,a,Nat.add_zero] using hroute
  have hs : ∀ j : ℕ, ∀ hj : j+1<r, p (A ⟨j,by omega⟩) = A ⟨j+1,hj⟩ := by
    intro j hj
    apply Subtype.ext
    have hne : a ⟨j,by omega⟩ ≠ e := by
      intro heq
      have hh := congrArg (complementaryEventRank e) heq
      rw [har,complementaryEventRank_self] at hh
      change 1+j=n-1 at hh
      omega
    have hno : ∀ d, d ∈ L → crossingVisitEdge q (DirectGLSSW.returnVisit q e d) ≠ a ⟨j,by omega⟩ := by
      intro d hd heq
      have hmin := first_return_rank_le q hq e L hL hlen d hd
      have hh := congrArg (complementaryEventRank e) heq
      rw [har] at hh
      change r ≤ complementaryEventRank e (crossingVisitEdge q (DirectGLSSW.returnVisit q e d)) at hmin
      rw [hh] at hmin
      change r ≤ 1+j at hmin
      omega
    have hroute := retained_anchor_next q hq e (a ⟨j,by omega⟩) L hne hno
    have hanext : cyclicSuccessor (a ⟨j,by omega⟩) = a ⟨j+1,hj⟩ := by
      change cyclicSuccessor (cyclicVertexIndex e (1+j)) = cyclicVertexIndex e (1+(j+1))
      rw [index_next e (1+j) (by omega)]
      congr 1
    rw [hanext] at hroute
    exact hroute
  have he : p (A ⟨r-1,by omega⟩) = R := by
    apply Subtype.ext
    have heq : f = a ⟨r-1,by omega⟩ := by
      apply complementaryEventRank_injective e
      rw [har]
      change r=1+(r-1)
      omega
    have hne : a ⟨r-1,by omega⟩ ≠ e := by
      rw [← heq]
      exact (DirectGLSSW.edgeVisitSide_spec q e c).2
    have hroute := retainedDart_anchor_to_selectedRoot q hq e (a ⟨r-1,by omega⟩) L c
      (List.get_mem L _) hne heq
    change _ = cellRootEvent q e L i
    rw [hroot]
    exact hroute
  have hmap : (R::U::List.ofFn A).map Subtype.val = cellEventWord q hq e L i := by
    rw [cellEventWord,ha]
    simp only [List.map_cons,List.map_ofFn,R,U,A]
    rfl
  have hnodup : (R::U::List.ofFn A).Nodup := by
    apply List.Nodup.of_map Subtype.val
    rw [hmap]
    exact cellEventWord_nodup q hq e L i
  have hchain := closed_interval_chain p R U hrpos A hr hl hs he
  have hword := orbitWord_eq_list_of_closed_chain p R (U::List.ofFn A) hnodup hchain
  rw [daughterPointList_eq_retainedOrbitWord q hq.g2 S _ (cellRootEvent_retained q e L i)]
  change (PermutationOrbits.orbitWord p R).map (fun x => polygonEventPoint q x.val) = _
  rw [hword]
  simpa only [List.map_map,Function.comp_def] using congrArg (List.map (polygonEventPoint q)) hmap

end DirectGLSSW.FirstCellOrbitWord




