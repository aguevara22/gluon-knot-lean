from pathlib import Path
from hashlib import sha256
import json, re
base = Path(__file__).resolve().parents[2]
def sha(p): return sha256((base / p).read_bytes()).hexdigest()
groups = {
 'TreeCoefficient': ['openTreeRec', 'rootedTreeRec', 'openTreeRec_one', 'openTreeRec_many',
   'fullBoundaryInterval', 'openTreeSum', 'treeCoefficient', 'mainTreeCoefficient',
   'openTreeSum_one', 'openTreeSum_many', 'treeCoefficient_eq', 'treesumData'],
 'TreeCoefficientTransport': ['IntervalComposition.nearSign_eq_of_chi', 'IntervalComposition.farSign_eq_of_chi',
   'IntervalComposition.ordinaryWeight_eq_of_chi', 'IntervalComposition.rootWeight_eq_of_chi',
   'openTreeSum_eq_of_chi', 'treeCoefficient_eq_of_chi', 'openTreeSum_shift', 'treeCoefficient_shift',
   'mainTreeCoefficient_shift', 'treesumData_shift'],
 'TreeChamber': ['tree_data_eq_of_chi', 'labelled_chamber_chi_constant', 'tree_data_labelled_chamber_constant',
   'tree_data_G1_path_constant', 'treeCoefficient_quotient_chamber_transport'],
 'PlaneTreeShape': ['OpenPlaneTree', 'openPlaneTreeUngraft', 'openPlaneTree_finite', 'RootedPlaneTree'],
 'PlaneTreeWeights': ['OpenPlaneTree.weight', 'OpenPlaneTree.ordinaryCount', 'OpenPlaneTree.ordinaryProduct',
   'OpenPlaneTree.weight_eq_signed_product', 'RootedPlaneTree.weight', 'RootedPlaneTree.ordinaryCount',
   'RootedPlaneTree.ordinaryProduct', 'RootedPlaneTree.weight_eq_signed_product'],
 'PlaneTreeExpansion': ['openPlaneTreeSum', 'OpenPlaneTree.eq_leaf', 'openPlaneTreeSum_one',
   'openPlaneTreeSum_many', 'openTreeRec_eq_planeTreeSum', 'rootedTreeRec_eq_planeTreeSum',
   'rootedTreeRec_eq_signed_planeTreeSum'],
 'PlaneTreeFormal': ['OpenPlaneTree.map_weight', 'RootedPlaneTree.map_weight', 'map_rootedTreeRec',
   'TreeWeightIndex', 'formalOrdinaryWeight', 'formalRootWeight', 'planeTree_formal_identity',
   'planeTree_formal_evaluation', 'treeCoefficient_eq_signed_planeTreeSum', 'treesum_trees']
}
expected = {
 'TreeCoefficient': 'd4e251f9b331f12bb5a9625c661928639d3606c3f253a94ef21144ea8b73f8c6',
 'TreeCoefficientTransport': '922287e0a90987f2d5f0206e5198512c4d62beb8a7e4aa48f620a149af580c7f',
 'TreeChamber': 'ffd49c183bf6509f56bd10cbd7e87a775d6caa4e86080f814fbbb0ddce6cc52b',
 'PlaneTreeShape': '73a8c3488fef9e80ce7e5b654698ac6fa24c405a5f7eaa8620b676de2aadab6e',
 'PlaneTreeWeights': '99c8f8c1d0bcbed0b713a70d392e49a4ea8e3eb0a920f44846c176fbde2343c3',
 'PlaneTreeExpansion': '7097e3e53ca86b3407969f958cba9dec68d5f6f508117e0648914780b24ed2ad',
 'PlaneTreeFormal': '1d91dac2558d1b76cd0624e0fb94e393f394f6cf6235990d98bf1f3156dddecf'
}
roots = ['SM.Gates', 'SM.FiniteCompositions', 'SM.CyclicChambers']
trace = ''.join('import ' + m + '\n' for m in roots) + 'import Mathlib.Tactic\nimport Mathlib.Algebra.MvPolynomial.Eval\n\n'
trace += 'set_option pp.fullNames true\nset_option pp.universes false\n\n'
files = {}; names = []
for module, decls in groups.items():
    p = 'work/checks/' + module + '.body.lean'
    assert sha(p) == expected[module]
    s = (base / p).read_text()
    files[p] = sha(p); trace += s + '\n'
    new = ['SM.' + d for d in decls]; names += new
    trace += '\n'.join('#check ' + n + '\n#print axioms ' + n for n in new) + '\n\n'
transparent = ['SM.openTreeRec', 'SM.rootedTreeRec', 'SM.fullBoundaryInterval',
    'SM.openTreeSum', 'SM.treeCoefficient', 'SM.mainTreeCoefficient', 'SM.treesumData',
    'SM.OpenPlaneTree', 'SM.openPlaneTreeUngraft', 'SM.RootedPlaneTree',
    'SM.OpenPlaneTree.weight', 'SM.OpenPlaneTree.ordinaryCount', 'SM.OpenPlaneTree.ordinaryProduct',
    'SM.RootedPlaneTree.weight', 'SM.RootedPlaneTree.ordinaryCount', 'SM.RootedPlaneTree.ordinaryProduct',
    'SM.TreeWeightIndex', 'SM.formalOrdinaryWeight', 'SM.formalRootWeight']
trace += '\n'.join('#print ' + n for n in transparent) + '\n\n'
exfile = 'work/checks/tree-definition-and-shape-review-examples.lean'
ex = (base / exfile).read_text(); examples = ['TreeDefinitionIndependentReview.' + n for n in re.findall(r'^theorem (\w+)', ex, re.M)]
trace += ex + '\n' + '\n'.join('#print axioms ' + n for n in examples) + '\n'
tracefile = 'work/checks/tree-definition-and-shape-review-types.lean'
(base / tracefile).write_text(trace)
seen = {}
def visit(m):
    if m in seen: return
    p = 'work/lean/' + m.replace('.', '/') + '.lean'; seen[m] = p
    for q in re.findall(r'^import (\S+)', (base / p).read_text(), re.M):
        if q.startswith('SM.'): visit(q)
for m in roots: visit(m)
d = {'state': 'prepared; independent kernel not yet run', 'frozen_bodies_sha256': files,
    'checked_declarations': names, 'named_declaration_count': len(names),
    'additional_examples': examples, 'additional_example_count': len(examples),
    'transparent_definitions_printed': transparent, 'SM_import_roots': roots,
    'SM_closure_files_sha256': {seen[m]: sha(seen[m]) for m in sorted(seen)},
    'canonical_SM_files_sha256': {str(p.relative_to(base)): sha(str(p.relative_to(base))) for p in sorted((base / 'work/lean/SM').glob('*.lean'))},
    'trace': tracefile, 'trace_sha256': sha(tracefile), 'examples': exfile, 'examples_sha256': sha(exfile),
    'source': 'reference/SM/sm-2-amplitude.tex', 'source_sha256': sha('reference/SM/sm-2-amplitude.tex'),
    'scope': 'Full def:treesum and lem:treesum-trees; TreeChamber remains supporting transport helper scope. Canonical port and source acceptance remain pending.'}
(base / 'work/checks/tree-definition-and-shape-review-closure.json').write_text(json.dumps(d, indent=2) + '\n')
print('Prepared', len(names), 'named declarations and', len(examples), 'consumer checks; SM import closure', len(seen))
