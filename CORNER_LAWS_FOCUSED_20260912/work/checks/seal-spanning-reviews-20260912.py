import datetime, difflib, hashlib, json, re
from pathlib import Path

BASE = Path(__file__).resolve().parents[2]
def sha(p): return hashlib.sha256((BASE / p).read_bytes()).hexdigest()
def read(p): return json.loads((BASE / p).read_text())
def headers(text):
    return {'SM.SoftDuplication.' + m.group(1): m.group(0).strip()
            for m in re.finditer(r'^(?:noncomputable )?(?:theorem|def)\s+(\w+).*?(?=\s*:=)', text, re.M | re.S)}

def seal(stem, prepared, out, extras):
    report = read(prepared)
    receipt_path = f'work/checks/{stem}-prototype-result.json'
    receipt = read(receipt_path)
    assert receipt['exit_code'] == 0 and receipt['source_claim_acceptance_increment'] == 0
    assert receipt['printed_declarations'] == report['scope']['declarations']
    for p,h in receipt['files_sha256'].items(): assert sha(p) == h, p
    body_path = f'work/checks/{stem}.body.lean'
    proto_path = f'work/checks/{stem}.prototype.lean'
    body = (BASE/body_path).read_text()
    proto = (BASE/proto_path).read_text()
    old = (BASE/f'work/checks/{stem}-first-failed.body.lean').read_text()
    hdrs = headers(body)
    assert list(hdrs) == receipt['printed_declarations']
    assert hdrs == headers(old)
    deps = read(f'work/checks/{stem}-body-dependencies.json')
    assert len(deps) == report['scope']['embedded_body_count']
    offsets = []
    for p in deps:
        txt = (BASE/p).read_text().strip()
        assert proto.count(txt) == 1, p
        offsets.append(proto.index(txt))
    assert offsets == sorted(offsets)
    logpath = next(p for p in receipt['files_sha256'] if p.endswith('-second-kernel.log'))
    log = (BASE/logpath).read_text()
    assert not re.search(r'error[:(]|sorryAx', log)
    ax = dict((n,[x.strip() for x in a.split(',') if x.strip()]) for n,a in
              re.findall(r"^'([^']+)' depends on axioms: \[([^\]]*)\]", log, re.M))
    assert list(ax) == receipt['printed_declarations']
    assert ax == receipt['declaration_axioms']
    assert all(set(v) <= {'propext','Classical.choice','Quot.sound'} for v in ax.values())
    assert re.search(r'error[:(]', (BASE/f'work/checks/{stem}-first-kernel.log').read_text())
    files = set(extras) | {prepared, receipt_path, 'reference/SM/sm-2-amplitude.tex',
        'work/lean/lean-toolchain', 'work/lean/lake-manifest.json',
        'work/checks/SoftRootBoundary-draft-dependency-bindings.json',
        'work/checks/soft-duplication-spanning-complete-baseline-20260912.json',
        'work/checks/seal-spanning-reviews-20260912.py'}
    files.update(str(p.relative_to(BASE)) for p in (BASE/'work/checks').glob(stem+'*') if p.is_file())
    for p in deps[:-1]:
        depstem = Path(p).name.removesuffix('.body.lean')
        rp = f'work/checks/{depstem}-prototype-result.json'
        r = read(rp)
        assert r['exit_code'] == 0 and r['source_claim_acceptance_increment'] == 0
        for q,h in r['files_sha256'].items(): assert sha(q) == h, q
        files.add(rp)
        files.update(r['files_sha256'])
    imports = re.findall(r'^import\s+([^\s]+)', proto, re.M)
    closure = {}
    def visit(mod):
        if not mod.startswith('SM.'): return
        p = 'work/lean/' + mod.replace('.', '/') + '.lean'
        if p in closure: return
        closure[p] = sha(p)
        for dep in re.findall(r'^import\s+([^\s]+)', (BASE/p).read_text(), re.M): visit(dep)
    for mod in imports: visit(mod)
    files.update(closure)
    baseline = read('work/checks/SoftRootBoundary-draft-dependency-bindings.json')['all_existing_canonical_sha256']
    assert len(baseline) == 327
    for p,h in baseline.items(): assert sha(p) == h, p
    broad = read('work/checks/soft-duplication-spanning-complete-baseline-20260912.json')['frozen_files_sha256']
    assert len(broad) == 1693
    for p,h in broad.items(): assert sha(p) == h, p
    report.update({
        'review_id': Path(out).stem,
        'sealed_utc': datetime.datetime.now(datetime.timezone.utc).isoformat(),
        'state': 'Sealed bounded same-model technical review; no original-source acceptance or stronger fidelity approval.',
        'assessment': 'No defect found in the stated bounded source scope. All universal claims are supported by reviewed proofs and the bound root kernel evidence; finite checks are supplementary only.',
        'execution': {'reviewer_ran_lean_kernel_build_or_audit': False,
            'reviewer_modified_reviewed_body_or_frozen_evidence': False,
            'root_kernel_session': receipt['kernel_session'], 'root_exit_code': 0,
            'first_run_passed': False, 'preserved_failed_sessions': receipt['preserved_failed_sessions']},
        'declaration_headers': hdrs,
        'declaration_header_context': 'Exact source headers reviewed with complete namespace/implicit context; no independently run kernel or printed-type check is claimed.',
        'declaration_axioms': ax,
        'proof_repair_exact_diff': ''.join(difflib.unified_diff(old.splitlines(True), body.splitlines(True), fromfile='first-failed', tofile='passing-body')),
        'public_headers_unchanged_from_failed_attempt': True,
        'ordered_embedded_bodies_sha256': {p:sha(p) for p in deps},
        'body_embeddings_verified_once_and_in_order': True,
        'direct_imports': imports,
        'canonical_dependency_closure_sha256': dict(sorted(closure.items())),
        'canonical_dependency_closure_count': len(closure),
        'canonical_baseline_integrity': {'preserved_module_count':327, 'all_preserved':True,
            'note':'Byte integrity of all327 is distinct from substantive review of the actual dependency closure.'},
        'checkpoint094_frozen_file_integrity': {'count':1693,'all_preserved':True},
        'files_sha256': {p:sha(p) for p in sorted(files)},
        'reviewed_files_sha256': {p:sha(p) for p in sorted(files)},
    })
    assert all(report[x] is False for x in ['stronger_model_statement_fidelity_approval','source_claim_accepted','canonical_integration_approved'])
    assert report['source_claim_acceptance_increment'] == 0
    dest=BASE/out
    assert not dest.exists(), 'Refuse to overwrite sealed review'
    dest.write_text(json.dumps(report,indent=2,ensure_ascii=False)+'\n')
    print(json.dumps({'review':out,'sha256':sha(out),'declarations':len(hdrs),'bindings':len(files),'canonical_closure':len(closure),'root_session':receipt['kernel_session']}))

if __name__ == '__main__':
    import sys
    stem, prep, out, *extras = sys.argv[1:]
    seal(stem, prep, out, extras)
