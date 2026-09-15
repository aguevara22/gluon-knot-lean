from pathlib import Path
base=Path(__file__).resolve().parents[2]
for f in ['root-boundary-review-types.lean','root-boundary-review-types.log','root-boundary-review-examples.lean']:
 p=base/'work/checks'/f;q=p.with_name(p.stem+'-initial'+p.suffix)
 if not q.exists():q.write_bytes(p.read_bytes())
p=base/'work/checks/root-boundary-review-examples.lean';s=p.read_text()
s=s.replace('  refine ⟨?_, fun k => (π.part k).leaves_pos⟩','  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩\n  refine ⟨?_, fun k => (π.part k).leaves_pos⟩')
s=s.replace('  refine ⟨{ parts := s, parts_pos := hs,\n    cut := fun k => ⟨r k, lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩,\n    strict := fun a b h => hr h,\n    first := Fin.ext hfirst,\n    last := Fin.ext hlast }, rfl, HEq.rfl⟩','  let π : IntervalComposition I := {\n    parts := s\n    parts_pos := hs\n    cut := fun k => ⟨r k, lt_of_le_of_lt (by rw [← hlast]; exact hr.monotone (Fin.le_last k)) I.right.isLt⟩\n    strict := fun a b h => hr h\n    first := Fin.ext hfirst\n    last := Fin.ext hlast }\n  exact ⟨π, rfl, HEq.rfl⟩')
s=s.replace('  let f : IntervalComposition I →','  letI : NeZero n := ⟨by have := I.left.isLt; omega⟩\n  let f : IntervalComposition I →')
s=s.replace('π.parts = 1 ∧ π.part 0 = I','π.parts = 1 ∧ π.part ⟨0, π.parts_pos⟩ = I')
s=s.replace('end RootBoundaryIndependentReview','''-- The root denotes the actual placed segment and both placed endpoints,
-- not only an edge vector shared by possibly different geometric edges.
theorem root_segment_and_endpoints_shift {n : ℕ} [NeZero n]
    (P : LabelledTuple n) (g a : ZMod n) :
    edgeSegment (shift a P) (g - a) = edgeSegment P g ∧
      (shift a P) (g - a) = P g ∧
      (shift a P) (g - a + 1) = P (g + 1) := by
  refine ⟨?_, ?_, ?_⟩
  · rw [edgeSegment_shift]
    simp
  · simp [shift]
  · change P (g - a + 1 + a) = P (g + 1)
    congr 1
    ring

end RootBoundaryIndependentReview''')
p.write_text(s)
t=base/'work/checks/root-boundary-review-types.lean';full=t.read_text();prefix=full.split('namespace RootBoundaryIndependentReview')[0]
names=['simultaneous_root_shift','leaf_index_exhaustion','boundary_vertices_distinct','cut_containment','raw_composition_admitted','all_compositions_finite','one_part_exists','root_segment_and_endpoints_shift']
t.write_text(prefix+s+'\n'+'\n'.join('#print axioms RootBoundaryIndependentReview.'+n for n in names)+'\n')
print('Independent auxiliary-only fixes; frozen implementation unchanged; added actual placed root segment check')
