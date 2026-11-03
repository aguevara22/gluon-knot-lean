import PhysicalEverySuffixDomain
set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.OpenCarrier
open DirectGLSSW ActiveArc Cursor RetainedWords Primitive AuxiliaryCarrierChart
open EventCarrierPairClassification CarrierTriplePairProperness
attribute [local instance] Classical.propDecidable

def precedingLabel {N M d : ℕ} (h : N=d+M) : Fin (N+1) ⊕ Unit :=
  Sum.inl ⟨d-1,by omega⟩
def cornerCarrierChain {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val)) :
    Fin (N+1) ⊕ Unit :=
  (eventCarrierChain (dropWord q h) (dropWord_regular q h hQ) U i).map (dropEdge h) id

def cornerCarrierPair {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val)) :
    (Fin (N+1) ⊕ Unit) × (Fin (N+1) ⊕ Unit) :=
  if i.val=0 then (cornerCarrierChain q h hQ U (openFirst _ _ U.val),precedingLabel h)
  else (cornerCarrierChain q h hQ U ⟨i.val-1,by have := i.isLt;omega⟩,
    cornerCarrierChain q h hQ U i)

lemma cornerCarrierChain_injective {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ)) :
    Function.Injective (cornerCarrierChain q h hQ U) := by
  have hm : Function.Injective (Sum.map (dropEdge h) (id : Unit→Unit)) := by
    intro x y he
    cases x <;> cases y
    · simp only [Sum.map_inl,Sum.inl.injEq] at he
      exact congrArg Sum.inl (dropEdge_injective h he)
    · simp only [Sum.map_inl,Sum.map_inr,Sum.inl_ne_inr] at he
    · simp only [Sum.map_inl,Sum.map_inr,Sum.inr_ne_inl] at he
    · simp only [Sum.map_inr,Sum.inr.injEq] at he
      exact congrArg Sum.inr (Subsingleton.elim _ _)
  exact hm.comp (eventCarrierChain_injective _ _ U)

lemma precedingLabel_ne_chain {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hd : 0<d) (hQ : Regular q)
    (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val)) :
    precedingLabel h≠cornerCarrierChain q h hQ U i := by
  unfold cornerCarrierChain eventCarrierChain
  split_ifs
  · simp only [Sum.map_inl,precedingLabel,Sum.inl.injEq]
    intro he
    have hv := congrArg Fin.val (Sum.inl.inj he)
    dsimp [dropEdge] at hv
    omega
  · intro he
    exact Sum.noConfusion he

lemma cornerCarrierPair_data {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hd : 0<d) (hQ : Regular q)
    (U : Support (dropWord q h) (dropWord_regular q h hQ)) :
    let P := fun i => ({(cornerCarrierPair q h hQ U i).1,(cornerCarrierPair q h hQ U i).2} :
      Finset (Fin (N+1) ⊕ Unit))
    (∀ i, (P i).card=2) ∧ Function.Injective P ∧
      ∀ i j k, i.val<j.val → j.val<k.val → ¬∃ x,x∈P i ∧ x∈P j ∧ x∈P k := by
  intro P
  let n := openCount (dropWord q h) (dropWord_regular q h hQ) U.val
  have hn : n-2+2=n := Nat.sub_add_cancel (open_count_ge_two _ _ U.val)
  let inv := fun i : Fin n => Fin.cast hn.symm i
  let f := fun i : Fin (n-2+2) => cornerCarrierChain q h hQ U (Fin.cast hn i)
  let r := precedingLabel h
  have hf : Function.Injective f := (cornerCarrierChain_injective q h hQ U).comp (Fin.cast_injective hn)
  have hr (i : Fin (n-2+2)) : r≠f i := precedingLabel_ne_chain q h hd hQ U _
  have hp (i : Fin n) : P i=eventPair f r (inv i) := by
    by_cases hi : i.val=0
    · simp only [P,cornerCarrierPair,hi,if_pos rfl,eventPair,inv,Fin.coe_cast]
      rfl
    · simp only [P,cornerCarrierPair,if_neg hi,eventPair,inv,Fin.coe_cast]
      rfl
  refine ⟨?_,?_,?_⟩
  · intro i
    rw [hp]
    exact eventPair_card f r hf (hr 0) _
  · intro i j he
    rw [hp,hp] at he
    have hh := eventPair_injective f r hf (hr 0) (hr 1) he
    exact Fin.ext (congrArg (fun z : Fin (n-2+2) => z.val) hh)
  · intro i j k hij hjk hx
    simp only [hp] at hx
    have hh := (eventPair_common_iff f r hf _ _ _ hij hjk).mp hx
    exact hr (inv j) hh.2.2.symm

def cornerTripleNumerator {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hQ : Regular q) (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i j k : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val))
    (L : Fin (N+1) ⊕ Unit → CarrierLine) : ℝ :=
  let p := cornerCarrierPair q h hQ U
  carrierTripleNumerator (L (p i).1) (L (p i).2) (L (p j).1) (L (p j).2)
    (L (p k).1) (L (p k).2)

lemma cornerTripleNumerator_nonzero_witness {N M d : ℕ} (q : Fin (N+2) → PlanarPoint ℝ)
    (h : N=d+M) (hd : 0<d) (hQ : Regular q)
    (U : Support (dropWord q h) (dropWord_regular q h hQ))
    (i j k : Fin (openCount (dropWord q h) (dropWord_regular q h hQ) U.val))
    (hij : i.val<j.val) (hjk : j.val<k.val) :
    ∃ L, cornerTripleNumerator q h hQ U i j k L≠0 := by
  let p := cornerCarrierPair q h hQ U
  let P := fun i => ({(p i).1,(p i).2} : Finset (Fin (N+1) ⊕ Unit))
  obtain ⟨hcard,hinj,hcommon⟩ := cornerCarrierPair_data q h hd hQ U
  have hne (i) : (p i).1≠(p i).2 := by
    intro he
    have hc := hcard i
    change ({(p i).1,(p i).2} : Finset (Fin (N+1) ⊕ Unit)).card=2 at hc
    simp only [he,Finset.pair_eq_singleton,Finset.card_singleton] at hc
    omega
  exact triple_pairs_numerator_nonzero_witness (p i).1 (p i).2 (p j).1 (p j).2 (p k).1 (p k).2
    (hne i) (hne j) (hne k)
    (fun he => (ne_of_lt hij) (congrArg Fin.val (hinj he)))
    (fun he => (ne_of_lt hjk) (congrArg Fin.val (hinj he)))
    (fun he => (ne_of_lt (lt_trans hij hjk)) (congrArg Fin.val (hinj he)))
    (hcommon i j k hij hjk)
end DirectGLSSW.ActiveArc.OpenCarrier
