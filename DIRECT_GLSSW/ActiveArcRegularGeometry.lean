import ActiveArcEvents
import DirectGLSSW.AffineSegments

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc

variable {n : ℕ} (q : Fin (n+2) → PlanarPoint ℝ)

/-- Under physical regularity, each represented pair has exactly one common
interior point. The determinant used in the proof comes from the actual
intersection and `Regular.transverse`. -/
theorem regular_crossing_unique_point (hR : Regular q) (c : Crossing q) :
    ∃! x : PlanarPoint ℝ,
      edgeInterior q c.val.1 x ∧ edgeInterior q c.val.2 x := by
  obtain ⟨x₀, hpair₀⟩ := c.property.2
  have hdet := hR.transverse c.val.1 c.val.2 (ne_of_lt c.property.1)
    x₀ hpair₀.1 hpair₀.2
  refine ⟨x₀, hpair₀, ?_⟩
  intro y hy
  obtain ⟨s, hs0, hs1, hsx⟩ := hpair₀.1
  obtain ⟨t, ht0, ht1, htx⟩ := hpair₀.2
  obtain ⟨s', hs'0, hs'1, hsy⟩ := hy.1
  obtain ⟨t', ht'0, ht'1, hty⟩ := hy.2
  have hxy :
      affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s =
        affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t :=
    hsx.symm.trans htx
  have hyy :
      affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s' =
        affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t' :=
    hsy.symm.trans hty
  obtain ⟨hss, htt⟩ := affinePoint_intersection_parameters_unique
    (q c.val.1.castSucc) (q c.val.1.succ)
    (q c.val.2.castSucc) (q c.val.2.succ) s t s' t'
    hdet hxy hyy
  calc
    y = affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s' := hsy
    _ = affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s :=
      congrArg (affinePoint (q c.val.1.castSucc) (q c.val.1.succ)) hss.symm
    _ = x₀ := hsx.symm

/-- The chosen point attached to a crossing is its unique physical
intersection point. -/
theorem crossingPoint_eq_of_mem_regular (hR : Regular q) (c : Crossing q)
    (x : PlanarPoint ℝ) (hl : edgeInterior q c.val.1 x)
    (hr : edgeInterior q c.val.2 x) : crossingPoint q c = x := by
  obtain ⟨x₀, hx₀, huniq⟩ := regular_crossing_unique_point q hR c
  have hchosen : crossingPoint q c = x₀ :=
    huniq (crossingPoint q c) (crossingPoint_mem q c)
  have hx : x = x₀ := huniq x ⟨hl, hr⟩
  exact hchosen.trans hx.symm

/-- A physical edge with nonzero direction has an injective affine
parameterization, so any two real parameters representing the same point
are equal. No interval bounds are needed for the comparison parameters. -/
theorem edge_parameter_unique (hR : Regular q) (e : Fin (n+1))
    (s t : ℝ)
    (h : affinePoint (q e.castSucc) (q e.succ) s =
      affinePoint (q e.castSucc) (q e.succ) t) : s = t := by
  have hne : q e.castSucc ≠ q e.succ := by
    intro heq
    apply hR.edge_nonzero e
    rw [heq]
    exact sub_self _
  exact affinePoint_injective (q e.castSucc) (q e.succ) hne h

/-- The left and right parameters of a represented physical crossing are
unique among all real parameters for their respective edge equations. -/
theorem crossing_parameters_unique_regular (hR : Regular q) (c : Crossing q)
    (s₁ s₂ t₁ t₂ : ℝ)
    (hl : affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s₁ =
      affinePoint (q c.val.1.castSucc) (q c.val.1.succ) s₂)
    (hr : affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t₁ =
      affinePoint (q c.val.2.castSucc) (q c.val.2.succ) t₂) :
    s₁ = s₂ ∧ t₁ = t₂ := by
  exact ⟨edge_parameter_unique q hR c.val.1 s₁ s₂ hl,
    edge_parameter_unique q hR c.val.2 t₁ t₂ hr⟩

/-- Every actual common interior point of two ordered physical edges determines
the unique crossing label, whose chosen point is that same point. -/
theorem existsUnique_crossing_of_mem_regular (hR : Regular q)
    (e f : Fin (n+1)) (hef : e < f) (x : PlanarPoint ℝ)
    (hl : edgeInterior q e x) (hr : edgeInterior q f x) :
    ∃! c : Crossing q, c.val = (e, f) ∧ crossingPoint q c = x := by
  let c₀ : Crossing q := ⟨(e, f), ⟨hef, ⟨x, hl, hr⟩⟩⟩
  refine ⟨c₀, ?_, ?_⟩
  · exact ⟨rfl, crossingPoint_eq_of_mem_regular q hR c₀ x hl hr⟩
  · intro c hc
    apply Subtype.ext
    exact hc.1

end DirectGLSSW.ActiveArc
