import DirectGLSSW.RealPolygons

namespace DirectGLSSW

variable {K : Type*} [Field K] [LinearOrder K] {n : ℕ}

theorem cyclicNoncollinear_relabel (q : Fin n → PlanarPoint K)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (hq : cyclicNoncollinear q) : cyclicNoncollinear (q ∘ ρ) := by
  intro a b c hab hbc hac
  apply hq (ρ a) (ρ b) (ρ c)
  · exact fun h => hab (ρ.injective h)
  · exact fun h => hbc (ρ.injective h)
  · exact fun h => hac (ρ.injective h)

theorem cyclicNoTripleIntersections_relabel (q : Fin n → PlanarPoint K)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (hq : cyclicNoTripleIntersections q) : cyclicNoTripleIntersections (q ∘ ρ) := by
  intro e f g x hef hfg heg ⟨he, hf, hg⟩
  apply hq (ρ e) (ρ f) (ρ g) x
  · exact fun h => hef (ρ.injective h)
  · exact fun h => hfg (ρ.injective h)
  · exact fun h => heg (ρ.injective h)
  · exact ⟨by simpa [edgeInterior, hρ e] using he,
      by simpa [edgeInterior, hρ f] using hf,
      by simpa [edgeInterior, hρ g] using hg⟩

theorem cyclicGeneric_relabel (q : Fin n → PlanarPoint K)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (hq : CyclicGeneric q) : CyclicGeneric (q ∘ ρ) := by
  refine ⟨hq.size_ge_three, cyclicNoncollinear_relabel q ρ hρ hq.g1,
    cyclicNoTripleIntersections_relabel q ρ hρ hq.g2⟩

private theorem cyclicVertexIndex_succ {n : ℕ} (root : Fin n) (k : ℕ) :
    cyclicVertexIndex root (k + 1) = cyclicSuccessor (cyclicVertexIndex root k) := by
  by_cases hn : n = 1
  · subst n
    exact Subsingleton.elim _ _
  have hnpos : 0 < n := by have := root.isLt; omega
  have hn2 : 1 < n := by omega
  apply Fin.ext
  change (root.val + 1 + (k + 1)) % n = ((root.val + 1 + k) % n + 1) % n
  calc
    (root.val + 1 + (k + 1)) % n = (root.val + 1 + k + 1) % n := by congr 1 <;> omega
    _ = ((root.val + 1 + k) % n + (1 % n)) % n := Nat.add_mod _ _ _
    _ = ((root.val + 1 + k) % n + 1) % n := by rw [Nat.mod_eq_of_lt hn2]

theorem cyclicVertexIndex_relabel (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (root : Fin n) (k : ℕ) :
    ρ (cyclicVertexIndex root k) = cyclicVertexIndex (ρ root) k := by
  induction k with
  | zero =>
      simpa [cyclicVertexIndex, cyclicSuccessor] using hρ root
  | succ k ih =>
      change ρ (cyclicVertexIndex root (k + 1)) = cyclicVertexIndex (ρ root) (k + 1)
      rw [cyclicVertexIndex_succ, hρ, ih, cyclicVertexIndex_succ]

theorem cyclicVertexEquiv_commutes_successor (root : Fin n) (e : Fin n) :
    cyclicVertexEquiv root (cyclicSuccessor e) =
      cyclicSuccessor (cyclicVertexEquiv root e) := by
  change cyclicVertexIndex root (cyclicSuccessor e).val =
    cyclicSuccessor (cyclicVertexIndex root e.val)
  have hs : (cyclicSuccessor e).val = (e.val + 1) % n := by
    simp [cyclicSuccessor, cyclicVertexIndex]
  rw [hs]
  by_cases h : e.val + 1 < n
  · have heq : (e.val + 1) % n = e.val + 1 := Nat.mod_eq_of_lt h
    rw [heq, cyclicVertexIndex_succ]
  · have hn : e.val + 1 = n := by have := e.isLt; omega
    rw [hn, Nat.mod_self]
    rw [← cyclicVertexIndex_succ root e.val, hn]
    have hp := cyclicVertexIndex_periodic root 0
    simpa using hp.symm

theorem rootedSpinorAmplitude_relabel {q : Fin n → PlanarPoint K}
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e))
    (root : Fin n) :
    rootedSpinorAmplitude (q ∘ ρ) root = rootedSpinorAmplitude q (ρ root) := by
  unfold rootedSpinorAmplitude
  congr 1
  funext k
  exact congrArg q (cyclicVertexIndex_relabel ρ hρ root k)

theorem polygonAmplitude_relabel (hRI : GLSSWRootIndependence)
    {q : Fin n → PlanarPoint ℝ} (hq : CyclicGeneric q)
    (ρ : Fin n ≃ Fin n)
    (hρ : ∀ e, ρ (cyclicSuccessor e) = cyclicSuccessor (ρ e)) :
    polygonAmplitude (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) = polygonAmplitude q hq := by
  rw [show polygonAmplitude (q ∘ ρ) (cyclicGeneric_relabel q ρ hρ hq) =
      rootedSpinorAmplitude (q ∘ ρ) ⟨0, by have := hq.size_ge_three; omega⟩ by rfl]
  rw [rootedSpinorAmplitude_relabel (q := q) ρ hρ]
  exact (hRI n q hq ⟨0, by have := hq.size_ge_three; omega⟩ (ρ ⟨0, by have := hq.size_ge_three; omega⟩)).symm

end DirectGLSSW
