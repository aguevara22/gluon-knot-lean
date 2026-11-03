import ActiveArcNonalternatingRefinement
import ActiveArcParentWordTransport
import ActiveArcGammaM

set_option autoImplicit false
noncomputable section
namespace DirectGLSSW.ActiveArc.CompatibleWords
open DirectGLSSW ActiveArc Primitive RetainedWords Split Cursor
open DirectGLSSW.OpenMarkedCurrent
attribute [local instance] Classical.propDecidable

/-- The selected original open current is the literal current of the point
word with q[0] prefixed to the actual shortened-parent open word. -/
theorem parent_openCurrent_eq_prefixedParentWord
    {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
    (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
    (S : {S : Finset (PolygonCrossing (child q hR c hc.1 hcut)) //
      PolygonNonalternation.polygonNonalternating (child q hR c hc.1 hcut)
        (child_noTriple q hR c hc.1 hcut) S})
    (T : Primitive.Support (parent q c hcut) (regular_parent q hR c hcut)) :
    let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
    let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
    Primitive.openCurrent q hR U =
      OpenMarkedCurrent.entry
        (polygonSignArray (fun k => if k=0 then q ⟨0,by omega⟩ else
          rootedPolygonWord (Primitive.OpenVertex (parent q c hcut)
            (regular_parent q hR c hcut) T)
            (RetainedWords.openLast (parent q c hcut)
              (regular_parent q hR c hcut) T.val) (k-1)))
        0 (RetainedWords.openCount (parent q c hcut)
          (regular_parent q hR c hcut) T.val) := by
  let V := nonalternatingSelectionEquiv q hR c hc hcut (S,T)
  let U : Primitive.Support q hR := ⟨insert c V.val,V.property.2⟩
  let p := parent q c hcut
  let hp := regular_parent q hR c hcut
  let m := RetainedWords.openCount p hp T.val
  let H₀ := polygonSignArray
    (rootedPolygonWord (Primitive.OpenVertex q hR U)
      (RetainedWords.openLast q hR U.val))
  let H₁ := polygonSignArray (fun k => if k=0 then q ⟨0,by omega⟩ else
    rootedPolygonWord (Primitive.OpenVertex p hp T)
      (RetainedWords.openLast p hp T.val) (k-1))
  have hword := parent_open_word q hR c hc hcut S.val T.val
  have hU : U.val = insert c (pieceSelections q hR c hc hcut S.val T.val) := by
    simp [U, V, nonalternatingSelectionEquiv]
  have hcount : RetainedWords.openCount q hR U.val = m+1 := by
    have hlen := congrArg List.length hword
    simpa [Primitive.OpenVertex, RetainedWords.openCount, m, p, hp, U, V,
      nonalternatingSelectionEquiv] using hlen
  have hpoint (k : ℕ) (hk : k ≤ m) :
      rootedPolygonWord (Primitive.OpenVertex q hR U)
          (RetainedWords.openLast q hR U.val) k =
        (if k=0 then q ⟨0,by omega⟩ else
          rootedPolygonWord (Primitive.OpenVertex p hp T)
            (RetainedWords.openLast p hp T.val) (k-1)) := by
    have hkorig : k < RetainedWords.openCount q hR U.val := by omega
    have hidx := List.get_of_eq hword ⟨k,by
      simpa [RetainedWords.openCount, Primitive.OpenVertex] using hkorig⟩
    cases k with
    | zero =>
        have hvertexRaw : RetainedWords.vertex q hR
            (insert c (pieceSelections q hR c hc hcut S.val T.val)) (start q)
            ⟨0,hkorig⟩=q ⟨0,by omega⟩ := by
          simpa only [List.get_ofFn, List.get_cons_zero] using hidx
        have hvertex : Primitive.OpenVertex q hR U ⟨0,hkorig⟩=q ⟨0,by omega⟩ := by
          simpa only [Primitive.OpenVertex, hU] using hvertexRaw
        rw [Primitive.openCurrent_word q hR U 0 hkorig, hvertex]
        simp
    | succ k =>
        have hkparent : k < RetainedWords.openCount p hp T.val := by
          change k+1 ≤ RetainedWords.openCount p hp T.val at hk
          omega
        have hvertexRaw : RetainedWords.vertex q hR
            (insert c (pieceSelections q hR c hc hcut S.val T.val)) (start q)
            ⟨k+1,hkorig⟩=RetainedWords.vertex p hp T.val (start p) ⟨k,hkparent⟩ := by
          simpa only [List.get_ofFn, List.get_cons_succ] using hidx
        have hvertex : Primitive.OpenVertex q hR U ⟨k+1,hkorig⟩=
            Primitive.OpenVertex p hp T ⟨k,hkparent⟩ := by
          simpa only [Primitive.OpenVertex, hU] using hvertexRaw
        rw [Primitive.openCurrent_word q hR U (k+1) hkorig, hvertex,
          ← Primitive.openCurrent_word p hp T k (by omega)]
        simp
  have hsign (x y z : ℕ) (hx : x ≤ m) (hy : y ≤ m) (hz : z ≤ m) :
      H₀ x y z = H₁ x y z := by
    simp only [H₀, H₁, polygonSignArray, polygonHDet]
    rw [hpoint x hx, hpoint y hy, hpoint z hz]
  have hmpos : 0 < m := by
    have h := RetainedWords.open_count_ge_two p hp T.val
    omega
  change OpenMarkedCurrent.entry H₀ 0 (RetainedWords.openCount q hR U.val-1) =
    OpenMarkedCurrent.entry H₁ 0 m
  rw [hcount]
  have hend : m+1-1=m := by omega
  rw [hend]
  unfold OpenMarkedCurrent.entry
  apply EndpointCurrent.weightedCutSum_congr_of_branch_eq (fun _ : ℕ => -1) hmpos
  intro i j hi hij hj
  apply ordinaryCurrent_congr_interval_fixed_near (fun _ _ _ => -1) H₀ H₁ hij
  intro x y z hix hxy hyz hzy
  exact hsign x y z (by omega) (by omega) (by omega)

end DirectGLSSW.ActiveArc.CompatibleWords
