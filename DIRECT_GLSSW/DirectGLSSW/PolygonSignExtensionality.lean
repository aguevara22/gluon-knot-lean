import DirectGLSSW.RealPolygons
import DirectGLSSW.ShortEdgeBoundedCongruence

namespace DirectGLSSW

theorem polygonAmplitude_eq_of_rooted_signs
    {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (hsign : ∀ i k j, 0 ≤ i → i < k → k < j → j ≤ n - 1 →
      polygonSignArray (rootedPolygonWord q
        ⟨0, by have := hq.size_ge_three; omega⟩) i k j =
      polygonSignArray (rootedPolygonWord q'
        ⟨0, by have := hq'.size_ge_three; omega⟩) i k j) :
    polygonAmplitude q hq = polygonAmplitude q' hq' := by
  let r : Fin n := ⟨0, by have := hq.size_ge_three; omega⟩
  let r' : Fin n := ⟨0, by have := hq'.size_ge_three; omega⟩
  have hqMark : polygonAmplitude q hq =
      markedAmplitude (polygonSignArray (rootedPolygonWord q r))
        (polygonSignArray (rootedPolygonWord q r)) 0 (n - 1) := by
    calc
      polygonAmplitude q hq =
          markedTreeSum (polygonSignArray (rootedPolygonWord q r))
            (polygonSignArray (rootedPolygonWord q r)) 0 (n - 1) := by
        simpa [r] using polygonAmplitude_eq_markedTreeSum q hq
      _ = markedAmplitude (polygonSignArray (rootedPolygonWord q r))
            (polygonSignArray (rootedPolygonWord q r)) 0 (n - 1) :=
        markedTreeSum_eq_markedAmplitude _ _ (by have := hq.size_ge_three; omega)
  have hq'Mark : polygonAmplitude q' hq' =
      markedAmplitude (polygonSignArray (rootedPolygonWord q' r'))
        (polygonSignArray (rootedPolygonWord q' r')) 0 (n - 1) := by
    calc
      polygonAmplitude q' hq' =
          markedTreeSum (polygonSignArray (rootedPolygonWord q' r'))
            (polygonSignArray (rootedPolygonWord q' r')) 0 (n - 1) := by
        simpa [r'] using polygonAmplitude_eq_markedTreeSum q' hq'
      _ = markedAmplitude (polygonSignArray (rootedPolygonWord q' r'))
            (polygonSignArray (rootedPolygonWord q' r')) 0 (n - 1) :=
        markedTreeSum_eq_markedAmplitude _ _ (by have := hq'.size_ge_three; omega)
  calc
    polygonAmplitude q hq =
        markedAmplitude (polygonSignArray (rootedPolygonWord q r))
          (polygonSignArray (rootedPolygonWord q r)) 0 (n - 1) := hqMark
    _ = markedAmplitude (polygonSignArray (rootedPolygonWord q' r'))
          (polygonSignArray (rootedPolygonWord q' r')) 0 (n - 1) := by
      apply markedAmplitude_congr_interval
      · have hn : 3 ≤ n := hq.size_ge_three
        omega
      · intro i k j hi hik hkj hj
        exact hsign i k j hi hik hkj hj
    _ = polygonAmplitude q' hq' := hq'Mark.symm

theorem polygonAmplitude_eq_of_oriented_triple_signs
    {n : ℕ} (q q' : Fin n → PlanarPoint ℝ)
    (hq : CyclicGeneric q) (hq' : CyclicGeneric q')
    (hsign : ∀ a b c : Fin n, a ≠ b → b ≠ c → a ≠ c →
      scalarSignValue (planarDet (q b - q c) (q a - q c)) =
      scalarSignValue (planarDet (q' b - q' c) (q' a - q' c))) :
    polygonAmplitude q hq = polygonAmplitude q' hq' := by
  apply polygonAmplitude_eq_of_rooted_signs q q' hq hq'
  intro i k j hi hik hkj hj
  let r : Fin n := ⟨0, by have := hq.size_ge_three; omega⟩
  let x : Fin n := cyclicVertexIndex r i
  let y : Fin n := cyclicVertexIndex r k
  let z : Fin n := cyclicVertexIndex r j
  have hiN : i < n := by omega
  have hkN : k < n := by omega
  have hjN : j < n := by omega
  have hxy : x ≠ y := by
    intro h
    have hidx := cyclicVertexIndex_injective r hiN hkN h
    omega
  have hyz : y ≠ z := by
    intro h
    have hidx := cyclicVertexIndex_injective r hkN hjN h
    omega
  have hxz : x ≠ z := by
    intro h
    have hidx := cyclicVertexIndex_injective r hiN hjN h
    omega
  have h := hsign x y z hxy hyz hxz
  simpa [polygonSignArray, polygonHDet, rootedPolygonWord, r, x, y, z] using h

end DirectGLSSW
