#!/usr/bin/env python3
"""CV-DOM unit U2a: mechanical part of the port of CarrierCrossings (§1, §3, §5, §6),
CarrierNeighborSeparation and CarrierNoncrossing onto the accepted geo layer.

Runs work/drafts/cvdom/port_lane.py on the three sources, then applies the residue rules the
transformer lacks (binder of `hS`, the N(S)/U(S) sets, the interlacement names, the names outside
DEFMAP, hypothesis-free duplicates dropped because SM.CarrierCrossings / SM.CarrierNoncrossing are in
the import closure of SM.GeoCarrierOrder).  Output: two bodies (no header, no namespace wrapper) that
the hand-written headers/targets in GeoCarrierCrossings.lean / GeoCarrierNoncrossing.lean wrap.
Run from work/:  python3 drafts/cvdom/U2a/port_u2a.py  →  /tmp/u2a/{crossings,noncrossing}_body.lean"""
import re, subprocess, sys, os

os.makedirs('/tmp/u2a', exist_ok=True)

def port(src):
    return subprocess.run([sys.executable, 'drafts/cvdom/port_lane.py', src],
                          capture_output=True, text=True).stdout

RENAME = {  # names outside port_lane.py's DEFMAP (source → geo), applied on word boundaries
 'geo_mem_carrierCrossings_iff_fiber': 'mem_geoCarrierCrossings_iff_fiber',
 'geo_mem_carrierCrossings': 'mem_geoCarrierCrossings',
 'geo_carrierCrossingCount_eq_card': 'geoCarrierCrossingCount_eq_card',
 'geo_carrierCrossingCount': 'geoCarrierCrossingCount',
 'geo_sum_carrierCrossingCount': 'sum_geoCarrierCrossingCount',
 'geo_insert_unselected_mem_independentSupports': 'geoIndependent_insert_unselected',
 'geo_supportUnselected_subset_biUnion_carrierCrossings':
     'geoSupportUnselected_subset_biUnion_geoCarrierCrossings',
 'geo_IsCrossingOf': 'GeoIsCrossingOf',
 'geo_NoncrossingOwners': 'GeoNoncrossingOwners',
 'geo_noncrossingOwners_empty': 'geoNoncrossingOwners_empty',
 'geo_noncrossingOwners_insert': 'geoNoncrossingOwners_insert',
 'geo_independent_noncrossingOwners_partial': 'geoIndependent_noncrossingOwners_partial',
 'geo_independent_noncrossingOwners': 'geoIndependent_noncrossingOwners',
 # accepted / U1a names for the lane lemmas the proofs consume (`X hn hP` → `geoX hP` done below)
 'mem_supportUnselected': 'mem_geoSupportUnselected',
 'mem_supportNeighbors': 'mem_geoSupportNeighbors',
 'supportUnselected': 'geoSupportUnselected',
 'supportNeighbors': 'geoSupportNeighbors',
 'Interlaces': 'GeometricInterlaces',
 'interlaces_symm': 'geometricInterlaces_symm',
 'not_interlaces_iff_twin_same_arc': 'geo_not_interlaces_iff_twin_same_arc',
 'mem_markList': 'mem_geoMarkList',
 'InheritsMarkOrder': 'GeoInheritsMarkOrder',
 'inheritsMarkOrder_empty': 'geoInheritsMarkOrder_empty',
 'component_empty_subsingleton': 'geoComponent_empty_subsingleton',
 'independent_remaining_pair_owners': 'geoIndependent_remaining_pair_owners',
 'independent_partial_invariants': 'geoIndependent_partial_invariants',
 'owner_insert_ne_of_ne': 'geoOwner_insert_ne_of_ne',
 'owner_insert_eq_imp': 'geoOwner_insert_eq_imp',
 'owner_insert_iff_of_unaffected': 'geoOwner_insert_iff_of_unaffected',
 'smoothingSuccessor_insert_child_data': 'geoSmoothingSuccessor_insert_child_data',
}
# hypothesis-free declarations already in the import closure (SM.Carrier, shared as they are)
DROP = ['geo_visitTwin_snd_ne', 'geo_visitTwin_edge_ne', 'geo_visit_crossing_val_eq_pair',
        'geo_ncx_mem_cons_of_mem_cons_filter', 'geo_ncx_traversalBetween_ne', 'geo_ncx_cyclic_four_iff']
SHARED_REF = {  # references to shared hypothesis-free lemmas: back to the SM.Carrier name
 'geo_visitTwin_snd_ne': 'visitTwin_snd_ne', 'geo_visitTwin_edge_ne': 'visitTwin_edge_ne',
 'geo_visit_crossing_val_eq_pair': 'visit_crossing_val_eq_pair',
 'geo_ncx_sorted_rotate_getElem_cyclic_iff': 'ncx_sorted_rotate_getElem_cyclic_iff',
 'geo_ncx_mem_cons_of_mem_cons_filter': 'ncx_mem_cons_of_mem_cons_filter',
 'geo_ncx_traversalBetween_ne': 'ncx_traversalBetween_ne', 'geo_ncx_cyclic_four_iff': 'ncx_cyclic_four_iff',
 'owner_predecessor': 'geoOwner_predecessor', 'owner_successor': 'geoOwner_successor'}

def drop_decl(s, name):
    """Drop the blank-line-separated block (docstring + `omit … in` + declaration + proof) that declares `name`."""
    blocks = s.split('\n\n')
    out = []
    for b in blocks:
        if re.search(r'^(theorem|def|noncomputable def) ' + re.escape(name) + r'\b', b, re.M):
            out.append('-- [shared] `' + name + '` is hypothesis-free and already in scope (SM.Carrier); not re-declared')
        else:
            out.append(b)
    return '\n\n'.join(out)

def fix(s):
    s = re.sub(r'\(hS : S ∈ independentSupports hn hP\)', '(hS : GeoIndependent hP S)', s)
    s = re.sub(r'\(mem_independentSupports_iff hn hP S\)\.mp hS', 'hS', s)
    s = re.sub(r'insert x S ∈ independentSupports hn hP', 'GeoIndependent hP (insert x S)', s)
    s = re.sub(r'rw \[mem_independentSupports_iff\] at hS ⊢\n', '', s)
    s = re.sub(r'\(hn : 3 ≤ n\) \{P : LabelledTuple n\} \(hP : G1 P\)', '{P : LabelledTuple n} (hP : CrossingGeometry P)', s)
    s = re.sub(r'visitPosition hn hP\b', 'geometricVisitPosition hP', s)
    for old in sorted(RENAME, key=len, reverse=True):
        s = re.sub(r'\b' + re.escape(old) + r'\b', RENAME[old], s)
    # `X hn hP` → `X hP` for every remaining lemma application (the geo lemmas take no `hn`);
    # the FlatCarriers §2/§4 lemmas that DO take `hn` are restored by hand (see REPORT).
    s = re.sub(r'\b([Gg]eo[A-Za-z_]*|mem_geo[A-Za-z_]*|geometricInterlaces_symm) hn hP\b', r'\1 hP', s)
    for nm in DROP:
        s = drop_decl(s, nm)
    for old, new in SHARED_REF.items():
        s = re.sub(r'\b' + re.escape(old) + r'\b', new, s)
    # `IsDecomposition` is `SM.Generic`-bound (ruling R2): its lemma is not ported
    s = drop_decl(s, 'geo_carriers_noncrossing_of_isDecomposition')
    s = s.replace('-- [shared] `geo_carriers_noncrossing_of_isDecomposition` is hypothesis-free and already in scope (SM.Carrier); not re-declared',
                  '-- [not ported] `carriers_noncrossing_of_isDecomposition`: `IsDecomposition` is `SM.Generic`-bound (ruling R2)')
    s = hand(s)
    s = s.replace('omit [NeZero n] in\n/-- Adjoining to an independent', '/-- Adjoining to an independent')
    s = s.replace('omit [NeZero n] in\n/-- A neighbour of an independent support is unselected', '/-- A neighbour of an independent support is unselected')
    return s

def hand(s):
    """The hand edits (all listed in REPORT.md).  (a) `hn : 3 ≤ n` restored where the accepted
    FlatCarriers §2/§4 lemmas take it; (b) the accepted `geoSmoothingSegment_mem_edgeSegment` has `u`
    explicit; (c) an indentation slip left by removing `rw [mem_independentSupports_iff] at hS ⊢`."""
    HN = ['geo_visit_incoming_mem_edgeSegment', 'geo_vertex_incoming_mem_edgeSegment',
          'geo_smoothing_corner_directions', 'geo_vertex_corner_directions']
    for nm in HN:   # declaration binder
        s = re.sub(r'theorem ' + nm + r' \{P : LabelledTuple n\} \(hP : CrossingGeometry P\)',
                   'theorem ' + nm + ' (hn : 3 ≤ n) {P : LabelledTuple n} (hP : CrossingGeometry P)', s)
    for nm in HN + ['geoMarkSuccessor_symm_visit_edge', 'geoMarkSuccessor_symm_vertex_edge',
                    'geo_visit_incoming_direction', 'geo_selected_visit_outgoing_direction',
                    'geo_vertex_incoming_direction', 'geo_vertex_outgoing_direction']:   # call sites
        s = re.sub(r'(?<!theorem )\b' + nm + r' hP\b', nm + ' hn hP', s)
    s = re.sub(r'geoSmoothingSegment_mem_edgeSegment hP S\n(\s*)\(\(geoSmoothingSuccessor hP S\)\.symm a\) hu0 hu1',
               r'geoSmoothingSegment_mem_edgeSegment hP S\n\1((geoSmoothingSuccessor hP S).symm a) u hu0 hu1', s)
    s = s.replace('geoSmoothingSegment_mem_edgeSegment hP S (Sum.inr v) hu0 hu1',
                  'geoSmoothingSegment_mem_edgeSegment hP S (Sum.inr v) u hu0 hu1')
    s = s.replace('geoSmoothingSegment_mem_edgeSegment hP S (Sum.inl i) hu0 hu1',
                  'geoSmoothingSegment_mem_edgeSegment hP S (Sum.inl i) u hu0 hu1')
    s = s.replace('  rw [mem_geoSupportNeighbors] at hxN\n    intro a ha b hb hab hI',
                  '  rw [mem_geoSupportNeighbors] at hxN\n  intro a ha b hb hab hI')
    return s

def body(s):
    # strip everything up to and including `variable {n : ℕ} [NeZero n]`, and the trailing `end`s
    i = s.index('variable {n : ℕ} [NeZero n]')
    s = s[i + len('variable {n : ℕ} [NeZero n]'):]
    s = re.sub(r'\nend\nend SM\.GeoCarrier\s*$', '\n', s)
    return s.strip('\n') + '\n'

cross = fix(port('lean/SM/CarrierCrossings.lean'))
nbr   = fix(port('lean/SM/CarrierNeighborSeparation.lean'))
ncx   = fix(port('lean/SM/CarrierNoncrossing.lean'))
open('/tmp/u2a/crossings_body.lean', 'w').write(body(cross) + '\n' + body(nbr))
# CarrierNoncrossing declares two generic lemmas BEFORE `noncomputable section`; both are shared
# (dropped), so the body starts at the variable line as for the others.
open('/tmp/u2a/noncrossing_body.lean', 'w').write(body(ncx))
print('written /tmp/u2a/crossings_body.lean, /tmp/u2a/noncrossing_body.lean')
