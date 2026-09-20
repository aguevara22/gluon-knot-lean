"""Assembler connections for W3B_Assembled.lean (read by assemble_W3B.py).  Connects REAL's black box
`w3bi_hrec_general` (three non-`ST/ST` orientation cases, `sorry` in W3B_REAL.lean) to unit H: `B.keep` is
symmetric in `B.y, B.z`, so unit H's bridge `w3bh_reduced_to_smooth` and `w3h_hrec` hold with the disjunction
`(B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)`; the two general forms `w3ba_reduced_to_smooth_gen` /
`w3ba_hrec_gen` are derived HERE from the text of W3B_H.lean (one `and_comm` is the only proof change)."""
import re
H = open('W3B_H.lean', encoding='utf-8').read()
def block(start_pat, end_pat):
    i = H.index(start_pat); j = H.index(end_pat, i)
    return H[i:j].rstrip('\n') + '\n'
red = block('theorem w3bh_reduced_to_smooth (D : Diagram)', '\n/-- **(h) THE reduced-smoothed-record lemma')
hrec = block('theorem w3h_hrec (D_H D_L : Diagram)', '\nend Row177_6')
def sub1(s, old, new):
    assert s.count(old) == 1, (old[:60], s.count(old)); return s.replace(old, new)
# --- the general bridge
red = sub1(red, 'theorem w3bh_reduced_to_smooth (D : Diagram)', 'theorem w3ba_reduced_to_smooth_gen (D : Diagram)')
red = sub1(red, '(B : BigonData ((smoothDiagram D x ε hε).switch y₀)) (hBy : B.y = y₀) (hBz : B.z = z₀) :',
           '(B : BigonData ((smoothDiagram D x ε hε).switch y₀))\n    (hB : (B.y = y₀ ∧ B.z = z₀) ∨ (B.y = z₀ ∧ B.z = y₀)) :')
red = sub1(red, '      Diagram.overVisit_fst, hBy, hBz]\n    exact (hX₁ u).symm)',
           '      Diagram.overVisit_fst]\n    rcases hB with ⟨hBy, hBz⟩ | ⟨hBy, hBz⟩\n'
           '    · rw [hBy, hBz]; exact (hX₁ u).symm\n    · rw [hBy, hBz]; exact and_comm.trans (hX₁ u).symm)')
# --- the general hrec
hrec = sub1(hrec, 'theorem w3h_hrec (D_H D_L : Diagram)', 'theorem w3ba_hrec_gen (D_H D_L : Diagram)')
hrec = sub1(hrec, '(B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0)) (hBHy : B_H.y = yH0) (hBHz : B_H.z = zH0)\n'
                  '    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0)) (hBLy : B_L.y = yL0) (hBLz : B_L.z = zL0) :',
           '(B_H : BigonData ((smoothDiagram D_H x_H εH hεH).switch yH0))\n'
           '    (hBH : (B_H.y = yH0 ∧ B_H.z = zH0) ∨ (B_H.y = zH0 ∧ B_H.z = yH0))\n'
           '    (B_L : BigonData ((smoothDiagram D_L x_L εL hεL).switch yL0))\n'
           '    (hBL : (B_L.y = yL0 ∧ B_L.z = zL0) ∨ (B_L.y = zL0 ∧ B_L.z = yL0)) :')
hrec = sub1(hrec, 'obtain ⟨ιH⟩ := w3bh_reduced_to_smooth D_H', 'obtain ⟨ιH⟩ := w3ba_reduced_to_smooth_gen D_H')
hrec = sub1(hrec, 'yH0 zH0 hyH0 hzH0 B_H hBHy hBHz', 'yH0 zH0 hyH0 hzH0 B_H hBH')
hrec = sub1(hrec, 'obtain ⟨ιL⟩ := w3bh_reduced_to_smooth D_L', 'obtain ⟨ιL⟩ := w3ba_reduced_to_smooth_gen D_L')
hrec = sub1(hrec, 'hεL yL0 zL0 hyL0 hzL0 B_L hBLy hBLz', 'hεL yL0 zL0 hyL0 hzL0 B_L hBL')
INSERT = ('/-! ### Assembler connections (prefix `w3ba_`, W3B_ASSEMBLY_REPORT.md): unit H\'s bridge and `w3h_hrec` in the\n'
          'orientation-general form REAL\'s `w3bi_hrec_general` needs.  `BigonData.keep` is symmetric in `B.y, B.z`, so the\n'
          'text of `w3bh_reduced_to_smooth` proves the disjunctive form with one `and_comm`; `w3ba_hrec_gen` is the text of\n'
          '`w3h_hrec` calling it (derived from W3B_H.lean by `assemble_W3B_connect.py`). -/\n\n'
          '/-- `w3bh_reduced_to_smooth` with `{B.y, B.z} = {y₀, z₀}` in either order (assembler copy). -/\n'
          + red + '\n'
          '/-- `w3h_hrec` with either orientation on either side (assembler copy of unit H\'s proof). -/\n'
          + hrec + '\n')
ARGS = ('D_H D_L hH hL x_H y_H z_H x_L y_L z_L Ψ a₁ a₂ b₁ b₂ c₁ c₂ ha₁ hb₁ ha₂ hc₁ hb₂ hc₂ hxy hxz hyz\n'
        '      hadj_e hadj_f hadj_g htw hbit hsgn hcyc hxL hyL hzL hεH hεL yH0 zH0 hyH0 hzH0 yL0 zL0 hyL0 hzL0')
CONNECT = [
  ('/-- **`w3h_hrec` in the form the (6) realiser needs (rule (3), corrected form)**',
   INSERT + '/-- **`w3h_hrec` in the form the (6) realiser needs (rule (3), corrected form)**',
   'insert w3ba_reduced_to_smooth_gen + w3ba_hrec_gen before w3bi_hrec_general'),
  ('      B_L hBLy hBLz\n  · sorry\n  · sorry\n  · sorry\n',
   '      B_L hBLy hBLz\n'
   f'  · exact w3ba_hrec_gen {ARGS}\n      B_H (Or.inl ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)\n'
   f'  · exact w3ba_hrec_gen {ARGS}\n      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inl ⟨hBLy, hBLz⟩)\n'
   f'  · exact w3ba_hrec_gen {ARGS}\n      B_H (Or.inr ⟨hBHy, hBHz⟩) B_L (Or.inr ⟨hBLy, hBLz⟩)\n',
   'close the three non-ST/ST cases of w3bi_hrec_general'),
  ('the\nthree other orientation pairs are unit H\'s content (same proof with `B.y, B.z` renamed). -/',
   'the\nthree other orientation pairs are closed by the assembler\'s `w3ba_hrec_gen` (unit H\'s proof, `and_comm`). -/',
   'reword w3bi_hrec_general docstring'),
]
