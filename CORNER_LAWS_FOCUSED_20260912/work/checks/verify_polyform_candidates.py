"""Verify exact candidate evidence; this grants no mathematical fidelity approval."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
CHECKS = ROOT / 'work/checks'
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
GROUPS = {
 'FormalNearFarRecursion': (19470, 'first', [
  'SM.openTreeRec_nearFar_equation', 'SM.openTreeRec_nearFar_inverse',
  'SM.rootedTreeRec_nearFar_farOnly']),
 'CanonicalTreeFarOutput': (15687, 'first', [
  'SM.canonicalPolynomial_half', 'SM.IntervalComposition.tripleOrdinaryWeight_nearFar',
  'SM.IntervalComposition.tripleRootWeight_nearFar', 'SM.canonicalTreePolynomial_farOnly',
  'SM.eval_canonicalTreePolynomial_farOnly']),
 'CanonicalFreezing': (14458, 'first', [
  'SM.canonicalFreezeValue', 'SM.canonicalFreezeHom', 'SM.canonicalFreezeHom_C',
  'SM.canonicalFreezeHom_X_zero', 'SM.canonicalFreezeHom_X_nonzero',
  'SM.eval_canonicalFreezeHom_of_agree', 'SM.eval_canonicalFreezeHom_base',
  'SM.boundaryTripleData_geometric', 'SM.canonicalFreezeHom_formalBoundaryChi_nonzero']),
 'VisibleGenericSignPersistence': (72929, 'second', [
  'SM.visible_chamber_generic_preserving_nonzero_chi']),
 'CanonicalSilentConstancy': (34366, 'first', [
  'SM.canonicalSilentPerturbation', 'SM.canonicalSilentPerturbation_support',
  'SM.canonicalFreezeBoundary_split', 'SM.canonicalTreePolynomial_freeze_constancy',
  'SM.eval_canonicalTreePolynomial_of_nonzero_agree']),
 'PolynomialContinuation': (34627, 'second', [
  'SM.canonicalTripleValue_agree_of_chi', 'SM.canonicalTreePolynomial_continuation_value',
  'SM.polynomial_form_continuation'])}

def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

baseline_path = CHECKS / 'polyform-baseline-20260912.json'
baseline = json.loads(baseline_path.read_text())['frozen_files_sha256']
assert len(baseline) == 977
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed baseline: {name}'
assert len([x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
receipts, evidence, declarations = {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for stem, (session, attempt, expected) in GROUPS.items():
    rp = CHECKS / f'{stem}-prototype-result.json'
    r = json.loads(rp.read_text())
    assert r['kernel_session'] == session and r['exit_code'] == 0
    assert r['source_claim_acceptance_increment'] == 0
    assert r['printed_declarations'] == expected
    prototype = (CHECKS / f'{stem}.prototype.lean').read_text()
    log = (CHECKS / f'{stem}-{attempt}-kernel.log').read_text()
    assert not re.search(r'\berror(?:\(|:)', log), stem
    assert re.findall(r'^#print axioms (.+)$', prototype, re.M) == expected
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected, stem
    parsed = {name: [x.strip() for x in axs.split(',') if x.strip()] for name, axs in traces}
    assert parsed == r['declaration_axioms'], stem
    assert all(set(axs) <= ALLOWED for axs in parsed.values()), stem
    for name, digest in r['files_sha256'].items():
        path = ROOT / name
        assert sha(path) == digest, f'Changed evidence: {name}'
        if name.endswith('.body.lean'):
            assert prototype.count(path.read_text()) == 1, f'Embedding: {name}'
            assert not re.search(r'(?m)^\s*(axiom|sorry|admit)\b|\bnative_decide\b', path.read_text()), name
        assert name not in evidence or evidence[name] == digest
        evidence[name] = digest
    receipts[str(rp.relative_to(ROOT))] = sha(rp)
    declarations.update(parsed)
assert len(declarations) == 26

failure_paths = [CHECKS / 'polyform-preserved-failures-20260912.json',
                 CHECKS / 'polyform-assembly-preserved-failure-20260912.json']
f1 = json.loads(failure_paths[0].read_text())['failures']['VisibleGenericSignPersistence:first']
f2 = json.loads(failure_paths[1].read_text())
for failure, session in [(f1, 49641), (f2, 11319)]:
    assert failure['kernel_session'] == session and failure['exit_code'] == 1
    for name, digest in failure['files_sha256'].items():
        assert sha(ROOT / name) == digest, f'Changed failed snapshot: {name}'
        evidence[name] = digest
stem = 'VisibleGenericSignPersistence'
header = lambda x: x[x.index('theorem '):].split(' := by', 1)[0]
assert header((CHECKS / f'{stem}.body.lean').read_text()) == header(
    (CHECKS / f'{stem}.first-failed.body.lean').read_text())
for kind in ['body', 'prototype']:
    assert (CHECKS / f'{stem}-first-draft.{kind}.lean').read_bytes() == (
        CHECKS / f'{stem}.first-failed.{kind}.lean').read_bytes()
assert (CHECKS / 'PolynomialContinuation.body.lean').read_bytes() == (
    CHECKS / 'PolynomialContinuation.first-failed.body.lean').read_bytes()
for stem in ['CanonicalSilentConstancy', 'PolynomialContinuation']:
    dp = CHECKS / f'{stem}-body-dependencies.json'
    ordered = json.loads(dp.read_text())
    prototype = (CHECKS / f'{stem}.prototype.lean').read_text()
    positions = [prototype.index((ROOT / x).read_text()) for x in ordered]
    assert positions == sorted(positions) and len(set(positions)) == len(positions)
    evidence[str(dp.relative_to(ROOT))] = sha(dp)
assert len(json.loads((CHECKS / 'PolynomialContinuation-body-dependencies.json').read_text())) == 90

source = ROOT / 'reference/SM/sm-2-amplitude.tex'
assert sha(source) == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
ledger_path = ROOT / 'work/checkpoints/goal-turn-087-candidates.json'
ledger = json.loads(ledger_path.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 for x in ledger)
result = {'utc': datetime.now(timezone.utc).isoformat(), 'verification': 'passed',
 'new_kernel_checked_candidate_declarations': 26, 'frozen_baseline_files_unchanged': 977,
 'canonical_modules_unchanged': 327, 'unique_candidate_evidence_files_checked': len(evidence),
 'baseline_sha256': sha(baseline_path), 'receipts_sha256': receipts,
 'candidate_ledger_sha256': sha(ledger_path), 'source_sha256': sha(source),
 'declaration_axioms': declarations, 'repair_statement_text_preserved': True,
 'preserved_failure_manifests_sha256': {str(p.relative_to(ROOT)):sha(p) for p in failure_paths},
 'source_claim_acceptance_increment': 0, 'whole_library_audit_rerun': False,
 'source_fidelity_approval': 'pending; not granted by this verifier'}
q = CHECKS / 'checkpoint-087-verification.json'
if q.exists():
    old = json.loads(q.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else:
    q.write_text(json.dumps(result, indent=2)+'\n')
print(f'PASS:26 candidate declarations;{len(evidence)} evidence files;977 frozen files;327 canonical modules unchanged.')
print('Full cor:polyform candidate; stronger fidelity and canonical acceptance remain pending.')
