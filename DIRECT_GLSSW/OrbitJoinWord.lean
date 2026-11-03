import DirectGLSSW.OrbitWordPrerequisite
import DirectGLSSW.PermutationSplitJoin

set_option autoImplicit false

namespace DirectGLSSW.PermutationOrbits

open Equiv

universe u
variable {α : Type u} [Fintype α] [DecidableEq α]

private noncomputable def joinEndpointFibresEquiv (p : Perm α) (a b : α)
    (hab : ¬p.SameCycle a b) :
    Fibre p (componentOf p a) ⊕ Fibre p (componentOf p b) ≃
      Fibre (p * swap a b) (componentOf (p * swap a b) a) := by
  classical
  let q := p * swap a b
  let f : Fibre p (componentOf p a) ⊕ Fibre p (componentOf p b) →
      Fibre q (componentOf q a) := fun x =>
    match x with
    | Sum.inl x => ⟨x.val, ((componentOf_eq_iff q a x.val).mpr
        ((sameCycle_join_iff p hab x.val).2 (Or.inl
          ((componentOf_eq_iff p a x.val).mp x.property.symm)))).symm⟩
    | Sum.inr x => ⟨x.val, ((componentOf_eq_iff q a x.val).mpr
        ((sameCycle_join_iff p hab x.val).2 (Or.inr
          ((componentOf_eq_iff p b x.val).mp x.property.symm)))).symm⟩
  refine Equiv.ofBijective f ?_
  constructor
  · intro x y hxy
    cases x with
    | inl x =>
      cases y with
      | inl y =>
        change (⟨x.val, _⟩ : Fibre q (componentOf q a)) = ⟨y.val, _⟩ at hxy
        have hv : x.val = y.val :=
          congrArg (fun z : Fibre q (componentOf q a) => z.val) hxy
        exact congrArg Sum.inl (Subtype.ext hv)
      | inr y =>
        change (⟨x.val, _⟩ : Fibre q (componentOf q a)) = ⟨y.val, _⟩ at hxy
        have hv : x.val = y.val :=
          congrArg (fun z : Fibre q (componentOf q a) => z.val) hxy
        have hba : p.SameCycle a b := by
          apply (componentOf_eq_iff p a b).mp
          exact x.property.symm.trans ((congrArg (fun z => componentOf p z) hv).trans y.property)
        exact False.elim (hab hba)
    | inr x =>
      cases y with
      | inl y =>
        change (⟨x.val, _⟩ : Fibre q (componentOf q a)) = ⟨y.val, _⟩ at hxy
        have hv : x.val = y.val :=
          congrArg (fun z : Fibre q (componentOf q a) => z.val) hxy
        have hba : p.SameCycle a b := by
          apply (componentOf_eq_iff p a b).mp
          exact y.property.symm.trans
            ((congrArg (fun z => componentOf p z) hv.symm).trans x.property)
        exact False.elim (hab hba)
      | inr y =>
        change (⟨x.val, _⟩ : Fibre q (componentOf q a)) = ⟨y.val, _⟩ at hxy
        have hv : x.val = y.val :=
          congrArg (fun z : Fibre q (componentOf q a) => z.val) hxy
        exact congrArg Sum.inr (Subtype.ext hv)
  · intro y
    have hqy : q.SameCycle a y.val :=
      (componentOf_eq_iff q a y.val).mp y.property.symm
    rcases (sameCycle_join_iff p hab y.val).1 hqy with ha | hb
    · exact ⟨Sum.inl ⟨y.val, ((componentOf_eq_iff p a y.val).mpr ha).symm⟩,
        Subtype.ext rfl⟩
    · exact ⟨Sum.inr ⟨y.val, ((componentOf_eq_iff p b y.val).mpr hb).symm⟩,
        Subtype.ext rfl⟩

private theorem join_pow_after_b (p : Perm α) {a b : α}
    (hab : ¬p.SameCycle a b) (j : ℕ) (hj0 : 0 < j)
    (hj : j < Fintype.card (Fibre p (componentOf p a))) :
    ((p * swap a b) ^ (Fintype.card (Fibre p (componentOf p b)) + j)) a =
      (p ^ j) a := by
  classical
  let q := p * swap a b
  let da := Fintype.card (Fibre p (componentOf p a))
  let db := Fintype.card (Fibre p (componentOf p b))
  have hdb : 0 < db := Fintype.card_pos
  have hclose : (p ^ db) b = b :=
    (pow_apply_eq_self_iff_fibre_card_dvd p b db).2 dvd_rfl
  have hfirst : (q ^ db) a = b := by
    rw [join_traversal p hab db hdb (le_rfl), hclose]
  induction j with
  | zero => omega
  | succ j ih =>
    have hj' : j < da := by omega
    by_cases hzero : j = 0
    · subst j
      have hbase : (q ^ (db + 1)) a = p a := by
        calc
          (q ^ (db + 1)) a = q ((q ^ db) a) := by
            rw [pow_succ', Perm.mul_apply]
          _ = q b := by rw [hfirst]
          _ = p a := mul_swap_apply_right p a b
      simpa using hbase
    · have hjpos : 0 < j := Nat.pos_of_ne_zero hzero
      have ih' := ih hjpos hj'
      have hstep : q ((p ^ j) a) = p ((p ^ j) a) := by
        have hnotA : (p ^ j) a ≠ a := by
          intro hret
          have hdvd := (pow_apply_eq_self_iff_fibre_card_dvd p a j).mp hret
          have hlt : j < Fintype.card (Fibre p (componentOf p a)) := hj'
          exact (Nat.not_dvd_of_pos_of_lt hjpos hlt) hdvd
        have hnotB : (p ^ j) a ≠ b := by
          intro hab'
          apply hab
          exact ⟨(j : ℤ), by simpa using hab'⟩
        exact mul_swap_apply_of_ne p hnotA hnotB
      calc
        (q ^ (db + (j + 1))) a = q ((q ^ (db + j)) a) := by
          rw [show db + (j + 1) = db + j + 1 by omega, pow_succ', Perm.mul_apply]
        _ = q ((p ^ j) a) := by rw [ih']
        _ = p ((p ^ j) a) := hstep
        _ = (p ^ (j + 1)) a := by rw [pow_succ', Perm.mul_apply]

theorem orbitWord_mul_swap_join [Fintype α] (p : Perm α) {a b : α}
    (hab : ¬p.SameCycle a b) :
    orbitWord (p * swap a b) a =
      (a :: (orbitWord p b).tail) ++ (b :: (orbitWord p a).tail) := by
  classical
  let q := p * swap a b
  let da := Fintype.card (Fibre p (componentOf p a))
  let db := Fintype.card (Fibre p (componentOf p b))
  have hda : 0 < da := Fintype.card_pos
  have hdb : 0 < db := Fintype.card_pos
  have hcard : Fintype.card (Fibre q (componentOf q a)) = da + db := by
    have hc := Fintype.card_congr (joinEndpointFibresEquiv p a b hab)
    simpa [da, db, Fintype.card_sum] using hc.symm
  have hget (r : Perm α) (x : α) (i : ℕ)
      (hi : i < Fintype.card (Fibre r (componentOf r x))) :
      (orbitWord r x)[i]'(by simpa [orbitWord_length] using hi) = (r ^ i) x := by
    have hi' : i < (orbitWord r x).length := by simpa [orbitWord_length] using hi
    simpa [orbitWord, orbitEnumeration_apply_val]
  have hlenRight : ((a :: (orbitWord p b).tail) ++
      (b :: (orbitWord p a).tail)).length = db + da := by
    simp [List.length_append, List.length_cons, List.length_tail,
      orbitWord_length, hdb, hda]
    omega
  have hprefix : (a :: (orbitWord p b).tail).length = db := by
    simp [List.length_cons, List.length_tail, orbitWord_length, hdb]
    omega
  have hwordlen : (orbitWord q a).length =
      ((a :: (orbitWord p b).tail) ++ (b :: (orbitWord p a).tail)).length := by
    calc
      (orbitWord q a).length = da + db := by
        simpa [orbitWord_length, q] using hcard
      _ = db + da := by omega
      _ = ((a :: (orbitWord p b).tail) ++ (b :: (orbitWord p a).tail)).length :=
        hlenRight.symm
  apply List.ext_getElem
  · exact hwordlen
  · intro i hi hbound
    by_cases hi0 : i = 0
    · subst i
      simp [orbitWord]
    · by_cases hib : i < db
      · have hipos : 0 < i := Nat.pos_of_ne_zero hi0
        have hqbound : i < Fintype.card (Fibre q (componentOf q a)) := by
          rw [hcard]
          omega
        have hjoin := join_traversal p hab i hipos (by omega)
        have hiBlen : i < (orbitWord p b).length := by
          simpa [orbitWord_length] using hib
        have htailB : i - 1 < (orbitWord p b).tail.length := by
          simp [orbitWord_length, hdb]
          omega
        have hR : ((a :: (orbitWord p b).tail) ++
            (b :: (orbitWord p a).tail))[i]'hbound =
              (orbitWord p b)[i]'hiBlen := by
          calc
            _ = (a :: (orbitWord p b).tail)[i]'(by rw [hprefix]; exact hib) :=
              List.getElem_append_left (by rw [hprefix]; exact hib)
            _ = (orbitWord p b)[i]'hiBlen := by
              rw [List.getElem_cons (by rw [hprefix]; exact hib)]
              rw [dif_neg hi0]
              rw [List.getElem_tail htailB]
              congr 1 <;> omega
        calc
          (orbitWord q a)[i] = (q ^ i) a := hget q a i hqbound
          _ = (p ^ i) b := hjoin
          _ = (orbitWord p b)[i] := (hget p b i hib).symm
          _ = ((a :: (orbitWord p b).tail) ++
              (b :: (orbitWord p a).tail))[i] := hR.symm
      · by_cases hibEq : i = db
        · subst i
          have hqbound : db < Fintype.card (Fibre q (componentOf q a)) := by
            rw [hcard]
            omega
          have hjoin := join_traversal p hab db hdb (le_rfl)
          have hclose : (p ^ db) b = b :=
            (pow_apply_eq_self_iff_fibre_card_dvd p b db).2 dvd_rfl
          have hidx : db - (a :: (orbitWord p b).tail).length = 0 := by
            rw [hprefix]
            omega
          have hRemainder : (b :: (orbitWord p a).tail)[0]'(by simp) = b := rfl
          have hR : ((a :: (orbitWord p b).tail) ++
              (b :: (orbitWord p a).tail))[db]'(by rw [hlenRight]; omega) = b := by
            rw [List.getElem_append_right (by omega)]
            simpa only [hprefix, Nat.sub_self] using hRemainder
          calc
            (orbitWord q a)[db] = (q ^ db) a := hget q a db hqbound
            _ = (p ^ db) b := hjoin
            _ = b := hclose
            _ = ((a :: (orbitWord p b).tail) ++
                (b :: (orbitWord p a).tail))[db] := hR.symm
        · have hieq : i = db + (i - db) := by omega
          have hipos : 0 < i - db := by omega
          have hiA : i - db < da := by rw [hlenRight] at hbound; omega
          have hqbound : i < Fintype.card (Fibre q (componentOf q a)) := by
            rw [hcard]
            omega
          have hAblen : i - db < (orbitWord p a).length := by
            simpa [orbitWord_length] using hiA
          have htailA : i - db < (b :: (orbitWord p a).tail).length := by
            simp [List.length_cons, List.length_tail, orbitWord_length, hda]
            omega
          have hidx : i - (a :: (orbitWord p b).tail).length = i - db := by
            rw [hprefix]
          have hR : ((a :: (orbitWord p b).tail) ++
              (b :: (orbitWord p a).tail))[i]'hbound =
                (orbitWord p a)[i - db]'(by simp [orbitWord_length]; omega) := by
            rw [List.getElem_append_right (by omega)]
            have htail : (b :: (orbitWord p a).tail)[i - db]'
                htailA =
                (orbitWord p a)[i - db]'hAblen := by
              rw [List.getElem_cons htailA]
              rw [dif_neg (Nat.ne_of_gt hipos)]
              have htailBound : i - db - 1 < (orbitWord p a).tail.length := by
                simp only [List.length_tail]
                omega
              rw [List.getElem_tail htailBound]
              congr 1 <;> omega
            simpa only [hprefix] using htail
          have hpow := join_pow_after_b p hab (i - db) hipos hiA
          calc
            (orbitWord q a)[i] = (q ^ i) a := hget q a i hqbound
            _ = (q ^ (db + (i - db))) a := by rw [← hieq]
            _ = (p ^ (i - db)) a := hpow
            _ = (orbitWord p a)[i - db] := (hget p a (i - db) hiA).symm
            _ = ((a :: (orbitWord p b).tail) ++
                (b :: (orbitWord p a).tail))[i] := hR.symm



end DirectGLSSW.PermutationOrbits
