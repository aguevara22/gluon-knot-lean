#!/usr/bin/env python3
"""Build selected modules; reject unregistered axioms and incomplete stage claims."""
import sys
sys.dont_write_bytecode = True
import argparse
import csv
from hashlib import sha256
import json
import os
from pathlib import Path
import re
import shutil
import subprocess

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.bootstrap import EXTRA
from tools.scope import SPEC, source_path
from tools.receipts import project_files

NAME = re.compile(r'[A-Za-z_][A-Za-z0-9_]*(?:\.[A-Za-z_][A-Za-z0-9_]*)*\Z')


def require(ok, message):
    if not ok:
        raise ValueError(message)


def run(command, cwd, stdin=None):
    result = subprocess.run(command, cwd=cwd, input=stdin, text=True, stdout=subprocess.PIPE,
                            stderr=subprocess.STDOUT)
    require(result.returncode == 0, 'command failed: ' + ' '.join(command) + '\n' + result.stdout)
    return result.stdout


def selected_rows(mapping, source, stage):
    ids = [r['id'] for r in mapping]
    require(len(ids) == len(set(ids)), 'duplicate declaration-map ID')
    required = set()
    if stage:
        required = {r['id'] for r in source if r['action'] not in {'SKIP', 'CERTIFICATE'}
                    and (stage == 2 or r['stage1'] == 'Y')}
        if stage == 3 or SPEC['mode'] == 'focused':
            required.update(EXTRA)
        byid = {r['id']: r for r in mapping}
        require(required <= set(byid), 'missing stage rows: ' + ', '.join(sorted(required-set(byid))))
        incomplete = sorted(i for i in required if byid[i].get('status') != 'accepted')
        require(not incomplete, 'stage is incomplete; unaccepted rows: ' + ', '.join(incomplete))
        return [r for r in mapping if r['id'] in required]
    return [r for r in mapping if r.get('status') in {'implemented', 'review', 'accepted'}]


def certificate_check(project):
    index = json.loads((project.parent / 'certificates/index.json').read_text())
    records = index['certificates']
    require(len({r['id'] for r in records}) == len(records), 'duplicate certificate IDs')
    for name in SPEC['certificates']:
        matches = [r for r in records if r['id'] == name]
        require(len(matches) == 1, 'missing certificate: ' + name)
        r = matches[0]
        require(r.get('status') == 'accepted' and r.get('author') and r.get('reviewer')
                and r['author'] != r['reviewer'], 'unreviewed certificate: ' + name)
        receipt = evidence_file(project.parent, r.get('receipt', ''))
        require(sha256(receipt.read_bytes()).hexdigest() == r.get('receipt_sha256'),
                'certificate receipt hash: ' + name)
        data = json.loads(receipt.read_text())
        for field in ['inputs', 'algorithm', 'coverage_argument', 'exact_arithmetic',
                      'results', 'reproduction_commands', 'review']:
            require(data.get(field), 'certificate receipt missing ' + field + ': ' + name)


def evidence_file(work, name):
    require(isinstance(name, str) and name, 'missing evidence path')
    p = Path(name)
    require(not p.is_absolute() and '..' not in p.parts, 'evidence path must be relative to work/')
    result = (work / p).resolve()
    require(result.is_relative_to(work.resolve()) and result.is_file(), 'missing/escaped evidence: ' + name)
    return result


def check(project, stage, lake):
    require(not stage or stage in SPEC['acceptance_stages'], 'stage is outside this handoff scope')
    receipt_dir = project.parent / 'checks'
    receipt_dir.mkdir(exist_ok=True)
    result_file = receipt_dir / ('stage-' + str(stage or 'development') + '.json')
    result_file.write_text(json.dumps({'passed': False, 'stage': stage, 'state': 'checking'}) + '\n')
    policy = json.loads((ROOT / 'lean/axiom-policy.json').read_text())
    require((project / 'Supplemental/Audit.lean').read_bytes() ==
            (ROOT / 'lean/Supplemental/Audit.lean').read_bytes(),
            'audit module changed; restore the supplied module in work/lean/Supplemental/Audit.lean')
    source = list(csv.DictReader((ROOT / 'blueprint/NODES.tsv').open(), delimiter='\t'))
    data = json.loads((project / 'lean-declarations.json').read_text())
    require(data.get('schema') == 1, 'declaration-map schema')
    rows = selected_rows(data['declarations'], source, stage)
    all_modules = sorted('.'.join(p.relative_to(project).with_suffix('').parts)
                         for p in project.rglob('*.lean')
                         if not any(part.startswith('.') for part in p.relative_to(project).parts)
                         and p.name != 'lakefile.lean')
    require('Supplemental.Audit' in all_modules, 'missing audit module')
    for name in all_modules:
        require(NAME.fullmatch(name), 'unsupported module name: ' + name)
    names = [r.get('declaration', '') for r in rows]
    require(len(names) == len(set(names)), 'multiple main rows mapped to the same declaration')
    fixed = policy['literature'] | policy['targets'] | {'hyp:R': 'SM.hyp_R'}
    for r in rows:
        require(NAME.fullmatch(r.get('declaration', '')), 'invalid declaration name: ' + r['id'])
        require(r.get('module') in all_modules, 'missing source module: ' + r['id'])
        if r['id'] in fixed:
            require(r['declaration'] == fixed[r['id']], 'fixed declaration name mismatch: ' + r['id'])
    modules = sorted({'Supplemental.Audit'} | {r['module'] for r in rows})
    if not stage:
        modules = sorted(set(modules) | {'Supplemental'})
    output = run([lake, 'build'] + ['+' + n for n in modules], project)
    allowed = policy['standard'] + list(policy['literature'].values())
    def arr(values):
        return '#[' + ', '.join('`' + n for n in values) + ']'
    program = '\n'.join('import ' + m for m in modules) + '\n'
    program += 'run_cmd Supplemental.auditProject ' + arr(all_modules) + ' ' + arr(allowed) + ' ' + arr(names) + '\n'
    output += run([lake, 'env', 'lean', '--stdin'], project, program)
    reports = [line[len('HANDOFF_AUDIT '):] for line in output.splitlines() if line.startswith('HANDOFF_AUDIT ')]
    require(len(reports) == 1, 'missing or duplicate machine audit result')
    audit = json.loads(reports[0])
    byname = {r['declaration']: r for r in audit['declarations']}
    require(set(byname) == set(names), 'audit declaration inventory mismatch')
    hashes = {}
    for r in rows:
        actual = byname[r['declaration']]
        require(actual['module'] == r['module'], 'declaration origin mismatch: ' + r['id'])
        hashes[r['id']] = sha256(json.dumps(actual['semantic_dependencies'],
            sort_keys=True, separators=(',', ':')).encode()).hexdigest()
    # Candidate hashes are available before review, without pretending to sign it.
    (receipt_dir / 'declaration-audit.json').write_text(json.dumps(
        {'stage_requested': stage, 'audit': audit, 'statement_hashes': hashes}, indent=2) + '\n')
    (receipt_dir / 'lean-check.log').write_text(output)
    if stage:
        source_by_id = {r['id']: r for r in source}
        for r in rows:
            require(r.get('author') and r.get('reviewer') and r['author'] != r['reviewer'],
                    'independent review missing: ' + r['id'])
            require(r.get('statement_sha256') == hashes[r['id']], 'missing/stale statement review: ' + r['id'])
            require(r.get('parameters_reviewed') is True and r.get('definition_equivalence_reviewed') is True,
                    'fidelity review incomplete: ' + r['id'])
            review = json.loads(evidence_file(project.parent, r.get('review_file', '')).read_text())
            require(review.get('id') == r['id'] and review.get('reviewer') == r['reviewer']
                    and review.get('statement_sha256') == hashes[r['id']]
                    and review.get('verdict') == 'faithful' and review.get('reason'),
                    'review evidence mismatch: ' + r['id'])
            if r['id'] in source_by_id:
                original = source_by_id[r['id']]
                if original['action'] == 'PROVE':
                    require(byname[r['declaration']]['kind'] == 'theorem', 'result must be a theorem declaration: ' + r['id'])
                require(set(r.get('labels', [])) == set(original['labels'].split()), 'source-label map mismatch: ' + r['id'])
                locator = source_path(original)
                require(r.get('source') == locator and r.get('line') == int(original['line']), 'source locator mismatch: ' + r['id'])
                require(review.get('source_sha256') == sha256((ROOT / locator).read_bytes()).hexdigest(),
                        'source review hash mismatch: ' + r['id'])
            elif r['id'] in EXTRA:
                require(byname[r['declaration']]['kind'] == 'theorem', 'required result must be a theorem: ' + r['id'])
        if stage == 2:
            certificate_check(project)
    bound_files = project_files(project)
    evidence = {evidence_file(project.parent, r['review_file']) for r in rows} if stage else set()
    if stage == 2:
        evidence.update(p for p in (project.parent / 'certificates').rglob('*') if p.is_file())
    bundle = {ROOT / name for name in ['tools/check_lean.py', 'tools/scope.py',
              'tools/receipts.py', 'lean/axiom-policy.json', 'lean/Supplemental/Audit.lean',
              'blueprint/NODES.tsv']}
    bundle.update(ROOT / source_path(r) for r in source)
    for directory in ['SM', 'R', 'BRIDGE', 'reference']:
        if (ROOT / directory).is_dir():
            bundle.update(p for p in (ROOT / directory).rglob('*')
                          if p.is_file() and p.name != '.DS_Store' and '__pycache__' not in p.parts)
    for name in ['TARGETS.md', 'PROOF_PLAN.md', 'R_ASSEMBLY_SPEC.md', 'FINAL_REVIEW.md',
                 'AUTONOMOUS_EXECUTION.md', 'OPEN_WORK.md']:
        if (ROOT / name).is_file():
            bundle.add(ROOT / name)
    if (ROOT / 'EXECUTION.json').is_file():
        bundle.add(ROOT / 'EXECUTION.json')
    from tools.receipts import hashes as file_hashes
    result = {'receipt_schema': 2, 'passed': True, 'stage': stage, 'mapped_declarations': len(rows),
              'audited_declarations': audit['checked'], 'stage_accepted': bool(stage),
              'project_sha256': file_hashes(project, bound_files),
              'evidence_sha256': file_hashes(project.parent, sorted(evidence)),
              'bundle_sha256': file_hashes(ROOT, sorted(bundle))}
    result_file.write_text(json.dumps(result, indent=2) + '\n')
    return result


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('project', type=Path)
    mode = parser.add_mutually_exclusive_group()
    mode.add_argument('--stage', type=int, choices=[1, 2, 3])
    mode.add_argument('--all', action='store_true', help='require every stage commissioned by this package')
    parser.add_argument('--lake', default=shutil.which('lake') or 'lake')
    args = parser.parse_args()
    try:
        stages = SPEC['acceptance_stages'] if args.all else [args.stage]
        results = [check(args.project.resolve(), stage, args.lake) for stage in stages]
        print(json.dumps({'all_required_stages_passed': True, 'stages': results} if args.all else results[0], indent=2))
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
