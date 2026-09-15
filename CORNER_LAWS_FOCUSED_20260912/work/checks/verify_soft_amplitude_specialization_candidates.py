"""Verify frozen duplication candidate evidence; never grant source acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib, json, re

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
CONFIG = C / 'soft-amplitude-specialization-candidate-groups-20260912.json'
GROUPS = json.loads(CONFIG.read_text())
ALLOWED = {'propext', 'Classical.choice', 'Quot.sound'}
def sha(path): return hashlib.sha256(path.read_bytes()).hexdigest()

bp = C / 'soft-amplitude-specialization-baseline-20260912.json'
baseline = json.loads(bp.read_text())['frozen_files_sha256']
assert len(baseline) == 1876
for name, digest in baseline.items():
    assert sha(ROOT / name) == digest, f'Changed frozen file: {name}'
assert len([x for x in baseline if x.startswith('work/lean/SM/') and x.endswith('.lean')]) == 327
assert len(list((ROOT / 'work/lean/SM').glob('*.lean'))) == 327
assert len(GROUPS) == 3
assert sum(g['count'] for g in GROUPS) == 12
assert sum(g['implementation_declarations'] for g in GROUPS) == 12
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
    assert all(n.startswith('SM.') for n in expected)
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
assert len(declarations) == 12

# This text comparison tracks repair disclosure, not semantic fidelity approval.
# Full bodies and complete printed declaration traces above remain bound separately.
def headers(src):
    starts = list(re.finditer(r'(?m)^(?:@\[[^\n]*\]\s*)?(?:(?:noncomputable|local|private)\s+)*(?:theorem|def|instance)\s+([A-Za-z0-9_]+)', src))
    result = {}
    for i, match in enumerate(starts):
        chunk = src[match.start():starts[i+1].start() if i+1<len(starts) else len(src)]
        ends = [x for x in [chunk.find(':='), chunk.find(' where')] if x>=0]
        equation_branch = re.search(r'(?m)^  \| ', chunk)
        if equation_branch: ends.append(equation_branch.start())
        assert ends, match.group(1)
        result[match.group(1)] = chunk[:min(ends)]
    return result

fp = C / 'soft-amplitude-specialization-preserved-failures-20260912.json'
failures = json.loads(fp.read_text())['failures']
assert sorted(f['kernel_session'] for f in failures) == sorted(s for g in GROUPS for s in g['failed'])
for f in failures:
    assert f['exit_code'] == 1
    for name, digest in f['files_sha256'].items():
        assert sha(ROOT / name) == digest
        evidence[name] = digest
    old = (ROOT / f['before_body']).read_text()
    new = (ROOT / f['after_body']).read_text()
    oh, nh = headers(old), headers(new)
    assert set(oh) == set(nh)
    changed = sorted(k for k in oh if oh[k] != nh[k])
    assert changed == f['changed_header_names'], (f['group'], changed)
    assert f['theorem_statement_text_preserved'] == (not changed)
    assert (ROOT / f['failed_prototype']).read_text().count(old) == 1
    assert re.search(r'\berror(?:\(|:)', (ROOT / f['failed_log']).read_text())
    if f['attempt']=='first':
        for kind in ['body','prototype']:
            draft = C / (f['group'] + '-first-draft.' + kind + '.lean')
            if draft.exists():
                assert draft.read_bytes() == (C / (f['group'] + '-first-failed.' + kind + '.lean')).read_bytes()
for g in GROUPS:
    if g['attempt']=='first':
        for kind in ['body','prototype']:
            draft = C / (g['stem'] + '-first-draft.' + kind + '.lean')
            if draft.exists(): assert draft.read_bytes() == (C / (g['stem'] + '.' + kind + '.lean')).read_bytes()

lp = ROOT / 'work/checkpoints/goal-turn-097-candidates.json'
ledger = json.loads(lp.read_text())
assert [x['declaration'] for x in ledger] == list(declarations)
assert all(x['source_acceptance_increment'] == 0 and x['kind']=='implementation declaration' for x in ledger)
assert sha(ROOT / 'work/lean/lean-declarations.json') == 'f90f11ebdf5ce92b303fa879479bde4d04ba1b4f1e4c864fcc5688850eafc49c'
assert sha(ROOT / 'reference/SM/sm-2-amplitude.tex') == '014068e2f6e2d86b0ff4edf48877b5967847d661eaae04d2d4c5fd9f54b7c9cf'
result = {
    'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
    'new_kernel_checked_declarations':12, 'implementation_declarations':12,
    'prototype_consumers':0, 'candidate_groups':3,
    'frozen_baseline_files_unchanged':1876, 'canonical_modules_unchanged':327,
    'unique_candidate_evidence_files_checked':len(evidence),
    'baseline_sha256':sha(bp), 'group_configuration_sha256':sha(CONFIG),
    'receipts_sha256':receipts, 'candidate_ledger_sha256':sha(lp),
    'declaration_axioms':declarations, 'embedded_body_order':orders,
    'preserved_failure_manifest_sha256':sha(fp),
    'failed_kernel_sessions':[f['kernel_session'] for f in failures],
    'repair_header_changes':{str(f['kernel_session']):f['changed_header_names'] for f in failures},
    'repair_interface_disclosure':'All recorded repairs affect proofs only; every compared public declaration header is unchanged.',
    'evidence_files_sha256':evidence, 'source_claim_acceptance_increment':0,
    'whole_library_audit_rerun':False,
    'source_fidelity_approval':'pending; not granted by this verifier',
    'source_scope':'Actual geometric A-soft source statement with a common positive radius bounded by any source epsilon0, constructed parent Generic, all nonsoft roots including the return edge, rational coefficient identity and all three integer sector laws. Stronger fidelity/integration and the full corner theorem remain.',
}
out = C / 'checkpoint-097-verification.json'
if out.exists():
    old = json.loads(out.read_text())
    assert {k:v for k,v in old.items() if k!='utc'} == {k:v for k,v in result.items() if k!='utc'}
else: out.write_text(json.dumps(result,indent=2)+'\n')
print(f'PASS:12 implementation declarations;{len(evidence)} evidence files;1876 frozen files;327 canonical modules unchanged.')
print('The full corner target and stronger fidelity/integration remain.')
