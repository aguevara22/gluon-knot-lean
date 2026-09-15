"""Verify exact crossing/G2 candidate evidence; no fidelity or source acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
GROUPS = {
    'SoftParentEdges': (18025, 'second', 15),
    'SoftNewbornParameters': (90848, 'second', 12),
    'SoftInheritedParameters': (93785, 'second', 13),
    'SoftParentPairStability': (81328, 'first', 6),
    'SoftCrossingClassification': (59753, 'first', 3),
    'SoftNewbornVisitWindows': (38871, 'first', 3),
    'SoftFamilyG2': (96478, 'first', 7),
}
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

baseline_path = C / 'soft-crossings-baseline-20260912.json'
baseline = json.loads(baseline_path.read_text())['frozen_files_sha256']
assert len(baseline) == 1115
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed frozen file: {name}'
assert len([x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327

receipts, evidence, declarations, orders = {}, {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for stem, (session, attempt, count) in GROUPS.items():
    rp = C / f'{stem}-prototype-result.json'
    r = json.loads(rp.read_text())
    assert r['kernel_session'] == session and r['exit_code'] == 0
    assert r['source_claim_acceptance_increment'] == 0
    expected = r['printed_declarations']
    assert len(expected) == len(set(expected)) == count
    proto = (C / f'{stem}.prototype.lean').read_text()
    log = (C / f'{stem}-{attempt}-kernel.log').read_text()
    assert not re.search(r'\berror(?:\(|:)', log)
    assert re.findall(r'^#print axioms (.+)$', proto, re.M) == expected
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected
    parsed = {name: [x.strip() for x in axs.split(',') if x.strip()] for name, axs in traces}
    assert parsed == r['declaration_axioms']
    assert all(set(axs) <= ALLOWED for axs in parsed.values())
    positions = []
    for name, digest in r['files_sha256'].items():
        p = ROOT / name
        assert sha(p) == digest, f'Changed candidate evidence: {name}'
        if name.endswith('.body.lean'):
            body = p.read_text()
            assert proto.count(body) == 1
            assert not re.search(r'(?m)^\s*(axiom|sorry|admit)\b|\bnative_decide\b', body)
            positions.append((proto.index(body), name))
        assert name not in evidence or evidence[name] == digest
        evidence[name] = digest
    orders[stem] = [name for _, name in sorted(positions)]
    assert len({p for p, _ in positions}) == len(positions)
    assert not set(parsed) & set(declarations)
    declarations.update(parsed)
    receipts[str(rp.relative_to(ROOT))] = sha(rp)
assert len(declarations) == 59

fp = C / 'soft-crossings-preserved-failures-20260912.json'
failures = json.loads(fp.read_text())['failures']
assert [x['kernel_session'] for x in failures] == [2081, 95003, 50530]
headers = lambda text: re.findall(r'(?ms)^theorem .*? := by', text)
for f in failures:
    assert f['exit_code'] == 1 and f['theorem_statement_text_preserved']
    for name, digest in f['files_sha256'].items():
        assert sha(ROOT / name) == digest
        evidence[name] = digest
    s = f['group']
    old = (C / f'{s}-first-failed.body.lean').read_text()
    new = (C / f'{s}.body.lean').read_text()
    assert headers(old) == headers(new)
    assert (C / f'{s}-first-failed.prototype.lean').read_text().count(old) == 1
    assert re.search(r'\berror(?:\(|:)', (C / f'{s}-first-kernel.log').read_text())
for s in ['SoftNewbornParameters', 'SoftFamilyG2']:
    dp = C / f'{s}-body-dependencies.json'
    assert json.loads(dp.read_text()) == orders[s]
    evidence[str(dp.relative_to(ROOT))] = sha(dp)
    for kind in ['body', 'prototype']:
        suffix = '-first-failed' if s == 'SoftNewbornParameters' else ''
        p = C / f'{s}-first-draft.{kind}.lean'
        assert p.read_bytes() == (C / f'{s}{suffix}.{kind}.lean').read_bytes()
        evidence[str(p.relative_to(ROOT))] = sha(p)
draft = C / 'SoftParentPairStability-first-draft.prototype.lean'
assert draft.read_text().count((C / 'SoftInheritedParameters-first-failed.body.lean').read_text()) == 1
evidence[str(draft.relative_to(ROOT))] = sha(draft)

ledger_path = ROOT / 'work/checkpoints/goal-turn-089-candidates.json'
ledger = json.loads(ledger_path.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 for x in ledger)
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
assert sha(ROOT / 'reference/SM/sm-2-amplitude.tex') == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
result = {
    'utc': datetime.now(timezone.utc).isoformat(), 'verification': 'passed',
    'new_kernel_checked_candidate_declarations': 59, 'candidate_groups': 7,
    'frozen_baseline_files_unchanged': 1115, 'canonical_modules_unchanged': 327,
    'unique_candidate_evidence_files_checked': len(evidence),
    'baseline_sha256': sha(baseline_path), 'receipts_sha256': receipts,
    'candidate_ledger_sha256': sha(ledger_path), 'declaration_axioms': declarations,
    'embedded_body_order': orders, 'preserved_failure_manifest_sha256': sha(fp),
    'failed_kernel_sessions': [f['kernel_session'] for f in failures],
    'repair_theorem_statement_text_preserved': True,
    'source_claim_acceptance_increment': 0, 'whole_library_audit_rerun': False,
    'source_fidelity_approval': 'pending; not granted by this verifier',
    'source_scope': 'Soft crossing geometry, complete support classification, Generic and chamber; cyclic Gauss transport, adjacency/deletion and complete source assembly remain',
}
out = C / 'checkpoint-089-verification.json'
if out.exists():
    old = json.loads(out.read_text())
    assert {k:v for k,v in old.items() if k != 'utc'} == {k:v for k,v in result.items() if k != 'utc'}
else:
    out.write_text(json.dumps(result, indent=2)+'\n')
print(f'PASS:59 candidate declarations;{len(evidence)} evidence files;1115 frozen files;327 canonical modules unchanged.')
print('Cyclic Gauss transport and full source assembly remain; no stronger approval or acceptance.')
