import ActiveArcTinyParentPointWord

set_option autoImplicit false
set_option maxHeartbeats 1000000
noncomputable section
namespace DirectGLSSW.ActiveArc.LiteralTinyParent
open Cursor Split Primitive OpenFirstEdgeGeometry Nonalternation RetainedWords PhysicalSegments PermutationOrbits
attribute [local instance] Classical.propDecidable

variable {a b : ℕ} (q : Fin (a+b+2) → PlanarPoint ℝ) (hR : Regular q)
variable (c : Crossing q) (hc : FirstCrossing q c) (hcut : c.val.2.val=a)
variable (η : ℝ) (hη : 0<η) (hη1 : η<1)

/-- The canonical retained vertex with positive tiny index is the parent vertex. -/
theorem tinyParent_openVertex_shift (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (k : ℕ)
    (hk : k<openCount (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val)
    (hkt : k+1<openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val)) :
    OpenVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (tinySupportOfParent q hR c hc hcut η hη hη1 T) ⟨k+1,hkt⟩ =
    OpenVertex (ParentArc q c hcut) (ParentRegular q hR c hcut) T ⟨k,hk⟩ := by
  have hw := tinyParent_openPointWord q hR c hc hcut η hη hη1 T
  have he := congrArg (fun l : List (PlanarPoint ℝ) => l[k+1]?) hw
  simpa [List.getElem?_ofFn,hkt,hk,OpenVertex,tinySupportOfParent] using he

theorem tinyParent_rootedWord_zero (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) :
    rootedPolygonWord
      (OpenVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T))
      (openLast (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (parentTinySelection q c hcut η T.val)) 0 =
      affinePoint (crossingPoint q c) (q 0) η := by
  have hz : 0<openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) := by
    have hh := open_count_ge_two (TinyArc q c hcut η)
      (TinyRegular q hR c hc hcut η hη hη1) (parentTinySelection q c hcut η T.val)
    omega
  exact (openCurrent_word (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
    (tinySupportOfParent q hR c hc hcut η hη hη1 T) 0 hz).trans
    (open_vertex_first (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val))

/-- Exact total-word alignment throughout the finite parent range. -/
theorem tinyParent_rootedWord_shift (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (k : ℕ)
    (hk : k<openCount (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val) :
    rootedPolygonWord
      (OpenVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T))
      (openLast (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (parentTinySelection q c hcut η T.val)) (k+1) =
    rootedPolygonWord (OpenVertex (ParentArc q c hcut) (ParentRegular q hR c hcut) T)
      (openLast (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val) k := by
  have hkt : k+1<openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val) := by
    rw [tinyParent_openCount q hR c hc hcut η hη hη1 T]
    omega
  exact (openCurrent_word (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
    (tinySupportOfParent q hR c hc hcut η hη hη1 T) (k+1) hkt).trans
    ((tinyParent_openVertex_shift q hR c hc hcut η hη hη1 T k hk hkt).trans
      (openCurrent_word (ParentArc q c hcut) (ParentRegular q hR c hcut) T k hk).symm)

/-- The literal tiny-parent retained word used by the short-edge projector,
with no assertion about the unused periodic extension. -/
theorem tinyParent_rootedWord_prefix (T : Nonalternation.Support (ParentArc q c hcut)
    (ParentRegular q hR c hcut)) (k : ℕ)
    (hk : k<openCount (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
      (parentTinySelection q c hcut η T.val)) :
    rootedPolygonWord
      (OpenVertex (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (tinySupportOfParent q hR c hc hcut η hη hη1 T))
      (openLast (TinyArc q c hcut η) (TinyRegular q hR c hc hcut η hη hη1)
        (parentTinySelection q c hcut η T.val)) k =
    if k=0 then affinePoint (crossingPoint q c) (q 0) η else
      rootedPolygonWord (OpenVertex (ParentArc q c hcut) (ParentRegular q hR c hcut) T)
        (openLast (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val) (k-1) := by
  by_cases hz : k=0
  · subst k
    simpa only [ite_true] using tinyParent_rootedWord_zero q hR c hc hcut η hη hη1 T
  · have hcount := tinyParent_openCount q hR c hc hcut η hη hη1 T
    have hp : k-1<openCount (ParentArc q c hcut) (ParentRegular q hR c hcut) T.val := by omega
    have he := tinyParent_rootedWord_shift q hR c hc hcut η hη hη1 T (k-1) hp
    have hsucc : k-1+1=k := by omega
    simpa only [hsucc,if_neg hz] using he

end DirectGLSSW.ActiveArc.LiteralTinyParent
