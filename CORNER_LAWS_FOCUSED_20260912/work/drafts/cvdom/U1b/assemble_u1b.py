import re, sys
SRC = '/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912/work/lean/SM/'
GEO = '/tmp/u1b/'
order = ['CarrierCycleList','CarrierFilteredCycles','CarrierSingleSupport','CarrierCurrentCycle',
         'CarrierInheritedOrder','CarrierInsertOrbits','CarrierInheritedInsert','CarrierSameArc',
         'CarrierMarkedArcLists','CarrierPendingPairs','CarrierIndependentOrder',
         'CarrierAffineSegments','CarrierSegmentGeometry','CarrierClosedTrace']
# identifier renames (word boundary), applied after the transformer
REN = {
 'componentCycle':'geoComponentCycle','geo_InheritsMarkOrder':'GeoInheritsMarkOrder',
 'InheritsMarkOrder':'GeoInheritsMarkOrder','geo_inheritsMarkOrder_iff_formPerm':'geoInheritsMarkOrder_iff_formPerm',
 'geo_inheritsMarkOrder_empty':'geoInheritsMarkOrder_empty','geo_inheritsMarkOrder_singleton':'geoInheritsMarkOrder_singleton',
 'geo_inheritsMarkOrder_insert':'geoInheritsMarkOrder_insert','inheritsMarkOrder_iff_formPerm':'geoInheritsMarkOrder_iff_formPerm',
 'inheritsMarkOrder_empty':'geoInheritsMarkOrder_empty','inheritsMarkOrder_singleton':'geoInheritsMarkOrder_singleton',
 'inheritsMarkOrder_insert':'geoInheritsMarkOrder_insert',
 'geo_PendingPairsTogether':'GeoPendingPairsTogether','PendingPairsTogether':'GeoPendingPairsTogether',
 'geo_pendingPairsTogether_empty':'geoPendingPairsTogether_empty','geo_pendingPairsTogether_insert':'geoPendingPairsTogether_insert',
 'pendingPairsTogether_empty':'geoPendingPairsTogether_empty','pendingPairsTogether_insert':'geoPendingPairsTogether_insert',
 'mem_markCycle':'mem_geoMarkCycle','mem_markList':'mem_geoMarkList','markList_nodup':'geoMarkList_nodup','markCycle_nodup':'geoMarkCycle_nodup',
 'smoothingSuccessor_empty':'geoSmoothingSuccessor_empty','smoothingSuccessor_insert':'geoSmoothingSuccessor_insert',
 'smoothingSuccessor_insert_child_data':'geoSmoothingSuccessor_insert_child_data','smoothingSuccessor_insert_eqOn_owner':'geoSmoothingSuccessor_insert_eqOn_owner',
 'smoothingSuccessor_bijOn_owner':'geoSmoothingSuccessor_bijOn_owner','component_empty_subsingleton':'geoComponent_empty_subsingleton',
 'owner_singleton_exhaust':'geoOwner_singleton_exhaust','owner_singleton_ne':'geoOwner_singleton_ne','owner_eq_iff':'geoOwner_eq_iff','owner_surjective':'geoOwner_surjective',
 'geo_owner_singleton_exhaust':'geoOwner_singleton_exhaust','geo_owner_singleton_ne':'geoOwner_singleton_ne','geo_owner_insert_iff_of_unaffected':'geoOwner_insert_iff_of_unaffected',
 'owner_insert_iff_of_unaffected':'geoOwner_insert_iff_of_unaffected','geo_component_card_singleton':'geoComponent_card_singleton',
 'Interlaces':'GeometricInterlaces','crossingVisitBetween':'geometricCrossingVisitBetween',
 'crossingVisitBetween_complement':'geo_crossingVisitBetween_complement','interlaces_iff_unique':'geo_interlaces_iff_unique',
 'independent_inheritsMarkOrder':'geo_independent_inheritsMarkOrder','geo_independent_inheritsMarkOrder':'geo_independent_inheritsMarkOrder',
 'geo_filter_splitList_left':'filter_splitList_left','geo_filter_splitList_right':'filter_splitList_right',
 'componentMarkList_data':'geoComponentMarkList_data','componentMarkList_getElem_successor':'geoComponentMarkList_getElem_successor',
 'componentTraceEdge':'geoComponentTraceEdge','componentTraceEdge_data':'geoComponentTraceEdge_data',
 'geo_componentTraceEdge':'geoComponentTraceEdge','geo_componentTraceEdge_data':'geoComponentTraceEdge_data',
 'continuous_smoothingSegment':'continuous_geoSmoothingSegment','geo_continuous_smoothingSegment':'continuous_geoSmoothingSegment',
 'geo_edgePoint_sub_edgePoint':'edgePoint_sub_edgePoint','geo_edgePoint_affine':'edgePoint_affine',
 'selectedMarkPerm_evaluation':'geoSelectedMarkPerm_evaluation',
}
out = []
for f in order:
    s = open(GEO+f+'.geo.lean').read()
    # strip imports, module docstring, namespace header/footer
    s = re.sub(r'^import .*\n', '', s, flags=re.M)
    s = re.sub(r'/-! Ported verbatim.*?-/\n', '', s, flags=re.S)
    s = re.sub(r'^namespace SM\.GeoCarrier\nopen Carrier\n', '', s, flags=re.M)
    s = re.sub(r'^noncomputable section\n', '', s, flags=re.M)
    s = re.sub(r'^attribute \[local instance\] Classical\.propDecidable\n', '', s, flags=re.M)
    s = re.sub(r'^variable \{n : ℕ\}.*\n', '', s, flags=re.M)
    s = re.sub(r'^end\nend SM\.GeoCarrier\n', '', s, flags=re.M)
    # binder patterns the transformer missed
    s = re.sub(r'\(hn : 3 ≤ n\) \(hP : Generic P\)', '(hP : CrossingGeometry P)', s)
    s = re.sub(r'\(hn : 3 ≤ n\) \{P : LabelledTuple n\}\s*\n?\s*\(hP : Generic P\)', '{P : LabelledTuple n} (hP : CrossingGeometry P)', s)
    s = re.sub(r'\{S : Finset \(Crossing P\)\} \(hS : S ∈ independentSupports hn hP\)', '{S : Finset (Crossing P)} (hS : GeoIndependent hP S)', s)
    s = re.sub(r'\(mem_independentSupports_iff hn hP S\)\.mp hS', 'hS', s)
    s = s.replace(' hn hP.1', ' hP').replace(' hn hP', ' hP').replace('(hn hP)', '(hP)')
    for k in sorted(REN, key=len, reverse=True):
        s = re.sub(r'(?<![A-Za-z0-9_.\'])' + re.escape(k) + r'(?![A-Za-z0-9_\'])', REN[k], s)
    out.append(f'/-! ### Port of SM/{f}.lean -/\n' + s.strip('\n') + '\n')
sys.stdout.write('\n'.join(out))
