"""Verify sealed soft-family assembly candidate evidence; grant no source acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
CONFIG = C / 'soft-family-assembly-candidate-groups-20260912.json'
GROUPS = json.loads(CONFIG.read_text())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

baseline_path = C / 'soft-family-assembly-baseline-20260912.json'
baseline = json.loads(baseline_path.read_text())['frozen_files_sha256']
assert len(baseline) == 1286
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed frozen file: {name}'
assert len([x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
assert len(GROUPS) == 5
assert sum(g['count'] for g in GROUPS) == 19
assert sum(g['implementation_declarations'] for g in GROUPS) == 19
assert sum(g['prototype_consumers'] for g in GROUPS) == 0

receipts, evidence, declarations, orders = {}, {}, {}, {}
pattern = r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)"
for g in GROUPS:
    stem, session, attempt, count = (g[k] for k in ['stem','session','attempt','count'])
    rp = C / f'{stem}-prototype-result.json'
    r = json.loads(rp.read_text())
    assert r['kernel_session'] == session and r['exit_code'] == 0
    assert r['source_claim_acceptance_increment'] == 0
    assert r['first_run_passed'] == (attempt == 'first')
    assert r['preserved_failed_sessions'] == g['failed']
    expected = r['printed_declarations']
    assert len(expected) == len(set(expected)) == count
    assert all(n.startswith('SM.') for n in expected) and g['prototype_consumers'] == 0
    proto = (C / f'{stem}.prototype.lean').read_text()
    log = (C / f'{stem}-{attempt}-kernel.log').read_text()
    assert not re.search(r'\berror(?:\(|:)', log)
    assert re.findall(r'^#print axioms (.+)$', proto, re.M) == expected
    traces = re.findall(pattern, log)
    assert [name for name, _ in traces] == expected
    parsed = {name:[x.strip() for x in axs.split(',') if x.strip()] for name,axs in traces}
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
    orders[stem] = [name for _,name in sorted(positions)]
    assert len({i for i,_ in positions}) == len(positions)
    dp = C / f'{stem}-body-dependencies.json'
    if dp.exists(): assert json.loads(dp.read_text()) == orders[stem]
    assert not set(parsed) & set(declarations)
    declarations.update(parsed)
    receipts[str(rp.relative_to(ROOT))] = sha(rp)
    for p in C.glob(f'{stem}*'):
        if p.is_file(): evidence[str(p.relative_to(ROOT))] = sha(p)
assert len(declarations) == 19

fp = C / 'soft-family-assembly-preserved-failures-20260912.json'
failures = json.loads(fp.read_text())['failures']
assert [f['kernel_session'] for f in failures] == [23927]
headers = lambda text: re.findall(r'(?ms)^theorem .*? :=', text)
for f in failures:
    assert f['exit_code'] == 1 and f['theorem_statement_text_preserved']
    for name,digest in f['files_sha256'].items():
        assert sha(ROOT / name) == digest
        evidence[name] = digest
    stem = f['group']
    old = (C / f'{stem}-first-failed.body.lean').read_text()
    new = (C / f'{stem}.body.lean').read_text()
    assert headers(old) == headers(new)
    assert (C / f'{stem}-first-failed.prototype.lean').read_text().count(old) == 1
    assert re.search(r'\berror(?:\(|:)', (C / f'{stem}-first-kernel.log').read_text())
for stem in ['SoftNewbornVertexArc', 'SoftInheritedCrossingData', 'SoftFamilyAssembly']:
    for kind in ['body', 'prototype']:
        assert (C / f'{stem}-first-draft.{kind}.lean').read_bytes() == (C / f'{stem}.{kind}.lean').read_bytes()
old = (C / 'SoftSourceSectors-first-failed.body.lean').read_text()
new = (C / 'SoftSourceSectors.body.lean').read_text()
assert new.replace('  haveI : Fact (1 < n) := ⟨by omega⟩\n', '', 1) == old

ledger_path = ROOT / 'work/checkpoints/goal-turn-091-candidates.json'
ledger = json.loads(ledger_path.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 for x in ledger)
assert sum(x['kind'] == 'prototype consumer' for x in ledger) == 0
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
assert sha(ROOT / 'reference/SM/sm-2-amplitude.tex') == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
result = {
    'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
    'new_kernel_checked_declarations':19, 'implementation_declarations':19,
    'prototype_consumers':0, 'candidate_groups':5,
    'frozen_baseline_files_unchanged':1286, 'canonical_modules_unchanged':327,
    'unique_candidate_evidence_files_checked':len(evidence),
    'baseline_sha256':sha(baseline_path), 'group_configuration_sha256':sha(CONFIG),
    'receipts_sha256':receipts, 'candidate_ledger_sha256':sha(ledger_path),
    'declaration_axioms':declarations, 'embedded_body_order':orders,
    'preserved_failure_manifest_sha256':sha(fp),
    'failed_kernel_sessions':[f['kernel_session'] for f in failures],
    'repair_theorem_statement_text_preserved':True,
    'evidence_files_sha256':evidence, 'source_claim_acceptance_increment':0,
    'whole_library_audit_rerun':False,
    'source_fidelity_approval':'pending; not granted by this verifier',
    'source_scope':'Candidate assembly of all four printed soft-family clauses; stronger fidelity/integration, amplitude soft theorem and final corner laws remain',
}
out = C / 'checkpoint-091-verification.json'
if out.exists():
    old = json.loads(out.read_text())
    assert {k:v for k,v in old.items() if k!='utc'} == {k:v for k,v in result.items() if k!='utc'}
else: out.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS:19 implementation declarations;{len(evidence)} evidence files;1286 frozen files;327 canonical modules unchanged.')
print('Full soft-family lemma assembled as candidate; final targets and stronger fidelity/integration remain.')
