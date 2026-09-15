"""Check exact soft-geometry candidate evidence; does not approve source fidelity."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
GROUPS = {
    'SoftInsertionIndices': (1276, 'first', 10),
    'SoftInsertionSuccessors': (98068, 'first', 4),
    'SoftInsertionTuple': (84277, 'second', 11),
    'SoftLocalDeterminants': (98338, 'second', 19),
    'SoftFamilyG1': (10086, 'fourth', 9),
    'SoftAttachmentSigns': (74029, 'first', 4),
    'SoftFamilyTurns': (56783, 'second', 4),
    'SoftFamilyLocalCrossing': (2482, 'first', 4),
    'SoftEdgeAvoidance': (27319, 'first', 3),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}

def sha(path):
    return hashlib.sha256(path.read_bytes()).hexdigest()

baseline_path = C / 'soft-geometry-baseline-20260912.json'
baseline = json.loads(baseline_path.read_text())['frozen_files_sha256']
assert len(baseline) == 1034
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed frozen file: {name}'
assert len([x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327

receipts, evidence, declarations, body_orders = {}, {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for stem, (session, attempt, count) in GROUPS.items():
    rp = C / f'{stem}-prototype-result.json'
    r = json.loads(rp.read_text())
    assert r['kernel_session'] == session and r['exit_code'] == 0
    assert r['source_claim_acceptance_increment'] == 0
    expected = r['printed_declarations']
    assert len(expected) == count and len(set(expected)) == count
    prototype = (C / f'{stem}.prototype.lean').read_text()
    log = (C / f'{stem}-{attempt}-kernel.log').read_text()
    assert not re.search(r'\berror(?:\(|:)', log), stem
    assert re.findall(r'^#print axioms (.+)$', prototype, re.M) == expected
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected, stem
    parsed = {name: [x.strip() for x in axs.split(',') if x.strip()] for name, axs in traces}
    assert parsed == r['declaration_axioms']
    assert all(set(axs) <= ALLOWED for axs in parsed.values())
    positions = []
    for name, digest in r['files_sha256'].items():
        path = ROOT / name
        assert sha(path) == digest, f'Changed candidate evidence: {name}'
        if name.endswith('.body.lean'):
            body = path.read_text()
            assert prototype.count(body) == 1, f'Exact embedding: {name}'
            assert not re.search(r'(?m)^\s*(axiom|sorry|admit)\b|\bnative_decide\b', body)
            positions.append((prototype.index(body), name))
        assert name not in evidence or evidence[name] == digest
        evidence[name] = digest
    body_orders[stem] = [name for _, name in sorted(positions)]
    assert len({p for p, _ in positions}) == len(positions)
    assert not set(declarations) & set(parsed)
    declarations.update(parsed)
    receipts[str(rp.relative_to(ROOT))] = sha(rp)
assert len(declarations) == 68

failure_path = C / 'soft-geometry-preserved-failures-20260912.json'
failures = json.loads(failure_path.read_text())['failures']
assert [f['kernel_session'] for f in failures] == [6443, 74386, 94576, 98720, 73398, 54616]
headers = lambda text: re.findall(r'(?ms)^(?:theorem|lemma) .*? := by', text)
for f in failures:
    assert f['exit_code'] == 1 and f['theorem_statement_text_preserved']
    for name, digest in f['files_sha256'].items():
        assert sha(ROOT / name) == digest, f'Changed failed snapshot: {name}'
        evidence[name] = digest
    stem, attempt = f['group'], f['attempt']
    old = (C / f'{stem}-{attempt}-failed.body.lean').read_text()
    new = (C / f'{stem}.body.lean').read_text()
    assert headers(old) == headers(new)
    failed_proto = (C / f'{stem}-{attempt}-failed.prototype.lean').read_text()
    assert failed_proto.count(old) == 1
    assert re.search(r'\berror(?:\(|:)', (C / f'{stem}-{attempt}-kernel.log').read_text())
    if stem == 'SoftInsertionTuple':
        assert new == old.replace('Fin.insertNth (softNewPosition j)',
            'Fin.insertNth (α := fun _ : Fin (n + 1) => Plane) (softNewPosition j)')
for kind in ['body', 'prototype']:
    assert (C / f'SoftLocalDeterminants-first-draft.{kind}.lean').read_bytes() == (
        C / f'SoftLocalDeterminants-first-failed.{kind}.lean').read_bytes()
    assert (C / f'SoftFamilyLocalCrossing-first-draft.{kind}.lean').read_bytes() == (
        C / f'SoftFamilyLocalCrossing.{kind}.lean').read_bytes()
dp = C / 'SoftFamilyLocalCrossing-body-dependencies.json'
assert json.loads(dp.read_text()) == body_orders['SoftFamilyLocalCrossing']
evidence[str(dp.relative_to(ROOT))] = sha(dp)

ledger_path = ROOT / 'work/checkpoints/goal-turn-088-candidates.json'
ledger = json.loads(ledger_path.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 for x in ledger)
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
assert sha(ROOT / 'reference/SM/sm-2-amplitude.tex') == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
result = {
    'utc': datetime.now(timezone.utc).isoformat(), 'verification': 'passed',
    'new_kernel_checked_candidate_declarations': len(declarations),
    'candidate_groups': len(GROUPS), 'frozen_baseline_files_unchanged': len(baseline),
    'canonical_modules_unchanged': 327,
    'unique_candidate_evidence_files_checked': len(evidence),
    'baseline_sha256': sha(baseline_path), 'receipts_sha256': receipts,
    'candidate_ledger_sha256': sha(ledger_path), 'declaration_axioms': declarations,
    'embedded_body_order': body_orders,
    'preserved_failure_manifest_sha256': sha(failure_path),
    'failed_kernel_sessions': [f['kernel_session'] for f in failures],
    'repair_theorem_statement_text_preserved': True,
    'source_claim_acceptance_increment': 0, 'whole_library_audit_rerun': False,
    'source_fidelity_approval': 'pending; not granted by this verifier',
    'source_scope': 'def:soft and partial lem:soft-generic; global crossings, G2, chamber and Gauss-word claims remain',
}
out = C / 'checkpoint-088-verification.json'
if out.exists():
    old = json.loads(out.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else:
    out.write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS:68 candidate declarations;{len(evidence)} evidence files;1034 frozen files;327 canonical modules unchanged.')
print('Partial soft-family geometry. Stronger fidelity and source acceptance remain pending.')
