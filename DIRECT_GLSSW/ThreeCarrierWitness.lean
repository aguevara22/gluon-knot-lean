import SixLineWitness
import DaughterCarrierPairs

set_option autoImplicit false

noncomputable section

namespace DirectGLSSW.ThreeCarrierWitness

open DirectGLSSW.AuxiliaryDeterminants
open DirectGLSSW.AuxiliaryCarrierPairs

private theorem image_eq_witnessPair {α : Type*} [DecidableEq α]
    (f : α → Fin 6) (s : Finset α) (hs : s.card = 2)
    (hf : Set.InjOn f (s : Set α)) :
    ∃ e : Fin 15,
      s.image f = {(witnessPair e).1, (witnessPair e).2} := by
  have hcard : (s.image f).card = 2 := by
    rw [Finset.card_image_of_injOn hf]
    exact hs
  obtain ⟨x, y, hxy, himage⟩ := Finset.card_eq_two.mp hcard
  rcases lt_or_gt_of_ne hxy with hlt | hgt
  · obtain ⟨e, he⟩ := witnessPair_enumerates x y hlt
    refine ⟨e, ?_⟩
    rw [he]
    exact himage
  · have hswap : ({x, y} : Finset (Fin 6)) = {y, x} := by
      ext z
      simp [or_comm]
    obtain ⟨e, he⟩ := witnessPair_enumerates y x hgt
    refine ⟨e, ?_⟩
    rw [he]
    exact himage.trans hswap

theorem three_carrier_witness {α : Type*} [DecidableEq α]
    (s t u : Finset α)
    (hs : s.card = 2) (ht : t.card = 2) (hu : u.card = 2)
    (hst : s ≠ t) (htu : t ≠ u) (hsu : s ≠ u)
    (hno : ¬ ∃ x : α, x ∈ s ∧ x ∈ t ∧ x ∈ u) :
    ∃ f : α → Fin 6,
      Set.InjOn f (↑(s ∪ t ∪ u) : Set α) ∧
      ∃ a b c : Fin 15,
        s.image f = {(witnessPair a).1, (witnessPair a).2} ∧
        t.image f = {(witnessPair b).1, (witnessPair b).2} ∧
        u.image f = {(witnessPair c).1, (witnessPair c).2} ∧
        witnessTripleDet a b c ≠ 0 := by
  classical
  let U : Finset α := s ∪ t ∪ u
  have hUcard : U.card ≤ 6 := by
    calc
      U.card ≤ (s ∪ t).card + u.card := Finset.card_union_le _ _
      _ ≤ s.card + t.card + u.card := by
        have hstcard := Finset.card_union_le s t
        omega
      _ = 6 := by omega
  let enc : {x : α // x ∈ U} → Fin 6 :=
    fun x => Fin.castLE hUcard ((Finset.equivFin U) x)
  have henc : Function.Injective enc := by
    intro x y hxy
    have hxy' : (Finset.equivFin U) x = (Finset.equivFin U) y :=
      Fin.castLE_injective hUcard hxy
    exact (Finset.equivFin U).injective hxy'
  let f : α → Fin 6 := fun x => if hx : x ∈ U then enc ⟨x, hx⟩ else 0
  have f_eq_on (x : α) (hx : x ∈ U) : f x = enc ⟨x,hx⟩ := by
    dsimp only [f]
    split_ifs with h
    · rfl
  have hfU : Set.InjOn f (U : Set α) := by
    intro x hx y hy hxy
    have hencxy : enc ⟨x, hx⟩ = enc ⟨y, hy⟩ := by
      exact (f_eq_on x hx).symm.trans (hxy.trans (f_eq_on y hy))
    have hsub : (⟨x, hx⟩ : {x : α // x ∈ U}) = ⟨y, hy⟩ := henc hencxy
    exact congrArg Subtype.val hsub
  have hsU : s ⊆ U := by
    intro x hx
    simp [U, hx]
  have htU : t ⊆ U := by
    intro x hx
    simp [U, hx]
  have huU : u ⊆ U := by
    intro x hx
    simp [U, hx]
  have hfs : Set.InjOn f (s : Set α) := by
    intro x hx y hy hxy
    exact hfU (hsU hx) (hsU hy) hxy
  have hft : Set.InjOn f (t : Set α) := by
    intro x hx y hy hxy
    exact hfU (htU hx) (htU hy) hxy
  have hfu : Set.InjOn f (u : Set α) := by
    intro x hx y hy hxy
    exact hfU (huU hx) (huU hy) hxy
  obtain ⟨a, hsa⟩ := image_eq_witnessPair f s hs hfs
  obtain ⟨b, htb⟩ := image_eq_witnessPair f t ht hft
  obtain ⟨c, huc⟩ := image_eq_witnessPair f u hu hfu
  have image_inj {v w : Finset α} (hv : v ⊆ U) (hw : w ⊆ U)
      (hvw : v.image f = w.image f) : v = w := by
    apply Finset.ext
    intro x
    constructor
    · intro hx
      have hfx : f x ∈ w.image f := by
        rw [← hvw]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hfx with ⟨y, hy, hxy⟩
      have hxy' : x = y := hfU (hv hx) (hw hy) hxy.symm
      simpa [hxy'] using hy
    · intro hx
      have hfx : f x ∈ v.image f := by
        rw [hvw]
        exact Finset.mem_image.mpr ⟨x, hx, rfl⟩
      rcases Finset.mem_image.mp hfx with ⟨y, hy, hxy⟩
      have hxy' : y = x := hfU (hv hy) (hw hx) hxy
      simpa [hxy'] using hy
  have hab : a ≠ b := by
    intro hab
    have himg : s.image f = t.image f := by
      rw [hsa, htb, hab]
    exact hst (image_inj hsU htU himg)
  have hbc : b ≠ c := by
    intro hbc
    have himg : t.image f = u.image f := by
      rw [htb, huc, hbc]
    exact htu (image_inj htU huU himg)
  have hac : a ≠ c := by
    intro hac
    have himg : s.image f = u.image f := by
      rw [hsa, huc, hac]
    exact hsu (image_inj hsU huU himg)
  have hnoIncident :
      ¬ ∃ i : Fin 6, witnessIncident a i ∧ witnessIncident b i ∧ witnessIncident c i := by
    rintro ⟨i, hai, hbi, hci⟩
    have his : i ∈ s.image f := by
      rw [hsa]
      simpa [witnessIncident] using hai
    have hit : i ∈ t.image f := by
      rw [htb]
      simpa [witnessIncident] using hbi
    have hiu : i ∈ u.image f := by
      rw [huc]
      simpa [witnessIncident] using hci
    rcases Finset.mem_image.mp his with ⟨x, hxs, hfx⟩
    rcases Finset.mem_image.mp hit with ⟨y, hyt, hfy⟩
    rcases Finset.mem_image.mp hiu with ⟨z, hzu, hfz⟩
    have hxy : x = y := hfU (hsU hxs) (htU hyt) (hfx.trans hfy.symm)
    have hxz : x = z := hfU (hsU hxs) (huU hzu) (hfx.trans hfz.symm)
    subst y
    subst z
    exact hno ⟨x, hxs, hyt, hzu⟩
  have hdet : witnessTripleDet a b c ≠ 0 := by
    intro hz
    apply hnoIncident
    exact (witnessTripleDet_zero_iff a b c hab hbc hac).mp hz
  exact ⟨f, hfU, a, b, c, hsa, htb, huc, hdet⟩

theorem daughter_three_carrier_witness {K : Type*}
    [Field K] [LinearOrder K] [IsStrictOrderedRing K]
    {n : ℕ} (q : Fin n → PlanarPoint K)
    (hG2 : cyclicNoTripleIntersections q)
    (S : Finset (PolygonCrossing q))
    (hn : 3 ≤ n) (hG1 : cyclicNoncollinear q)
    (hNA : PolygonNonalternation.polygonNonalternating q hG2 S)
    (root : PolygonEvent q) (hroot : DaughterFirstReturn.retainedCorner q S root)
    (i j k : Fin (Fintype.card (DaughterFirstReturn.CornerCoord q hG2 S root)))
    (hij : i ≠ j) (hjk : j ≠ k) (hik : i ≠ k) :
    ∃ f : Fin n → Fin 6,
      Set.InjOn f (↑(daughterCarrierPair q hG2 S root i ∪
        daughterCarrierPair q hG2 S root j ∪ daughterCarrierPair q hG2 S root k) : Set (Fin n)) ∧
      ∃ a b c : Fin 15,
        (daughterCarrierPair q hG2 S root i).image f =
          {(witnessPair a).1, (witnessPair a).2} ∧
        (daughterCarrierPair q hG2 S root j).image f =
          {(witnessPair b).1, (witnessPair b).2} ∧
        (daughterCarrierPair q hG2 S root k).image f =
          {(witnessPair c).1, (witnessPair c).2} ∧
        witnessTripleDet a b c ≠ 0 := by
  let s := daughterCarrierPair q hG2 S root i
  let t := daughterCarrierPair q hG2 S root j
  let u := daughterCarrierPair q hG2 S root k
  have hs : s.card = 2 :=
    daughterCarrierPair_card q hG2 S hn hG1 hNA root hroot i
  have ht : t.card = 2 :=
    daughterCarrierPair_card q hG2 S hn hG1 hNA root hroot j
  have hu : u.card = 2 :=
    daughterCarrierPair_card q hG2 S hn hG1 hNA root hroot k
  have hinj := daughterCarrierPair_injective q hG2 S hn hG1 hNA root hroot
  have hst : s ≠ t := fun h => hij (hinj h)
  have htu : t ≠ u := fun h => hjk (hinj h)
  have hsu : s ≠ u := fun h => hik (hinj h)
  have hno : ¬ ∃ x : Fin n, x ∈ s ∧ x ∈ t ∧ x ∈ u :=
    daughterCarrierPair_no_three_common q hG2 S hn hG1 hNA root hroot
      i j k hij hjk hik
  exact three_carrier_witness s t u hs ht hu hst htu hsu hno

end DirectGLSSW.ThreeCarrierWitness



