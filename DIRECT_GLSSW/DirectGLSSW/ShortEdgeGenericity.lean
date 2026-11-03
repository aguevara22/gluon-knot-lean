import DirectGLSSW.RealPolygons

namespace DirectGLSSW.ShortEdgeGenericity

def edgeClosed {n : ℕ} (q : Fin n → PlanarPoint ℝ) (e : Fin n)
    (x : PlanarPoint ℝ) : Prop :=
  ∃ t : ℝ, 0 ≤ t ∧ t ≤ 1 ∧ x = affinePoint (q e) (q (cyclicSuccessor e)) t

theorem edgeClosed_vertex_incident {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e v : Fin n) (h : edgeClosed q e (q v)) :
    v = e ∨ v = cyclicSuccessor e := by
  by_contra hv
  have hve : v ≠ e := fun he => hv (Or.inl he)
  have hvs : v ≠ cyclicSuccessor e := fun he => hv (Or.inr he)
  obtain ⟨t, _, _, ht⟩ := h
  apply cyclic_vertex_carrier_det_ne_zero hq.size_ge_three q hq.g1 e v hve hvs
  rw [ht]
  exact affinePoint_carrier_det_zero (q e) (q (cyclicSuccessor e)) t

theorem edgeClosed_open_of_not_vertex {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (e : Fin n) (x : PlanarPoint ℝ) (h : edgeClosed q e x)
    (hv : ∀ v : Fin n, x ≠ q v) : edgeInterior q e x := by
  obtain ⟨t, ht0, ht1, hx⟩ := h
  have hn0 : t ≠ 0 := by
    intro ht
    apply hv e
    simpa [ht, affinePoint_zero] using hx
  have hn1 : t ≠ 1 := by
    intro ht
    apply hv (cyclicSuccessor e)
    simpa [ht, affinePoint_one] using hx
  exact ⟨t, lt_of_le_of_ne ht0 (Ne.symm hn0), lt_of_le_of_ne ht1 hn1, hx⟩

theorem cyclic_no_three_closed_edges {n : ℕ} (q : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (e f g : Fin n) (x : PlanarPoint ℝ)
    (hef : e ≠ f) (hfg : f ≠ g) (heg : e ≠ g) :
    ¬ (edgeClosed q e x ∧ edgeClosed q f x ∧ edgeClosed q g x) := by
  rintro ⟨he, hf, hg⟩
  have hv : ∀ v : Fin n, x ≠ q v := by
    intro v hx
    have hie := edgeClosed_vertex_incident q hq e v (hx ▸ he)
    have hif := edgeClosed_vertex_incident q hq f v (hx ▸ hf)
    have hig := edgeClosed_vertex_incident q hq g v (hx ▸ hg)
    have hinj := (cyclicSuccessor_bijective (n := n)).injective
    rcases hie with hie | hie <;> rcases hif with hif | hif <;>
      rcases hig with hig | hig
    all_goals first
      | exact hef (hie.symm.trans hif)
      | exact hfg (hif.symm.trans hig)
      | exact heg (hie.symm.trans hig)
      | exact hef (hinj (hie.symm.trans hif))
      | exact hfg (hinj (hif.symm.trans hig))
      | exact heg (hinj (hie.symm.trans hig))
  exact hq.g2 e f g x hef hfg heg
    ⟨edgeClosed_open_of_not_vertex q e x he hv,
      edgeClosed_open_of_not_vertex q f x hf hv,
      edgeClosed_open_of_not_vertex q g x hg hv⟩

end DirectGLSSW.ShortEdgeGenericity
