#!/usr/bin/env python3
"""End-to-end acceptance controls in an explicitly synthetic, core-only package."""
import sys
sys.dont_write_bytecode = True
import json
from hashlib import sha256
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]


def write(path, text):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(text)


def dump(path, value):
    write(path, json.dumps(value, indent=2) + '\n')


def command(args, cwd, success=True):
    result = subprocess.run(args, cwd=cwd, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    assert (result.returncode == 0) == success, result.stdout
    return result.stdout


def main():
    lake = shutil.which('lake') or str(Path.home() / '.elan/bin/lake')
    with tempfile.TemporaryDirectory(prefix='handoff-acceptance-') as temporary:
        root = Path(temporary)
        shutil.copytree(ROOT / 'lean', root / 'lean', ignore=shutil.ignore_patterns('.lake', '__pycache__'))
        for name in ['bootstrap.py', 'check_lean.py', 'scope.py', 'receipts.py', 'progress.py']:
            write(root / 'tools' / name, (ROOT / 'tools' / name).read_text())
        dump(root / 'EXECUTION.json', {'mode': 'focused', 'extra': [], 'certificates': [],
            'targets': ['T'], 'tasks': [], 'acceptance_stages': [1]})
        dump(root / 'lean/axiom-policy.json', {'literature': {}, 'targets': {'T': 'Fixture.main'},
            'standard': ['propext', 'Classical.choice', 'Quot.sound']})
        write(root / 'blueprint/NODES.tsv', 'id\taction\tfile\tsource\tline\tstage1\tlabels\n'
            'D\tDEFINE\tfixture.tex\treference/fixture.tex\t1\tY\tD\n'
            'T\tPROVE\tfixture.tex\treference/fixture.tex\t2\tY\tT\n')
        source = 'Synthetic fixture: the domain is True.\nSynthetic fixture: the domain implies itself.\n'
        write(root / 'reference/fixture.tex', source)
        command([sys.executable, '-B', 'tools/bootstrap.py'], root)
        project = root / 'work/lean'
        lakefile = project / 'lakefile.toml'
        lakefile.write_text(lakefile.read_text().split('\n[[require]]')[0] + '\n')
        (project / 'lake-manifest.json').unlink(missing_ok=True)
        fixture = project / 'Supplemental/Fixture.lean'
        clean = ('namespace Fixture\ndef hidden : Prop := True\ndef domain : Prop := hidden\n'
                 'theorem main : domain → domain := fun h => h\nend Fixture\n')
        fixture.write_text(clean)
        (project / 'Supplemental.lean').write_text('import Supplemental.Audit\nimport Supplemental.Fixture\n')
        mapping_path = project / 'lean-declarations.json'
        mapping = json.loads(mapping_path.read_text())
        for row in mapping['declarations']:
            row.update({'declaration': 'Fixture.domain' if row['id'] == 'D' else 'Fixture.main',
                'module': 'Supplemental.Fixture', 'status': 'implemented',
                'author': 'synthetic-implementer', 'reviewer': 'synthetic-reviewer',
                'parameters_reviewed': True, 'definition_equivalence_reviewed': True,
                'review_file': 'reviews/' + row['id'] + '.json'})
        dump(mapping_path, mapping)
        check = [sys.executable, '-B', 'tools/check_lean.py', 'work/lean', '--lake', lake]
        command(check, root)
        audit = json.loads((root / 'work/checks/declaration-audit.json').read_text())
        assert len(audit['statement_hashes']) == 2
        for row in mapping['declarations']:
            row['status'] = 'accepted'
            row['statement_sha256'] = audit['statement_hashes'][row['id']]
            dump(root / 'work' / row['review_file'], {'id': row['id'], 'reviewer': row['reviewer'],
                'statement_sha256': row['statement_sha256'], 'source_sha256': sha256(source.encode()).hexdigest(),
                'verdict': 'faithful', 'reason': 'Synthetic test receipt, never evidence about the SM theorem.'})
        dump(mapping_path, mapping)
        all_result = json.loads(command(check + ['--all'], root))
        assert all_result['all_required_stages_passed']
        def state():
            command([sys.executable, '-B', 'tools/progress.py', '--once'], root)
            return json.loads((root / 'work/progress/latest.json').read_text())['acceptance']['1']
        assert state() == 'checker receipt current'
        print('PASS: synthetic source/type reviews complete a real pinned-Lean acceptance cycle')
        review = root / 'work/reviews/T.json'
        saved = review.read_bytes()
        review.unlink()
        assert 'not established' in state()
        review.write_bytes(saved)
        assert state() == 'checker receipt current'
        review.write_text(saved.decode().replace('faithful', 'rejected'))
        assert 'not established' in state()
        assert 'review evidence mismatch' in command(check + ['--all'], root, False)
        review.write_bytes(saved)
        command(check + ['--all'], root)
        print('PASS: missing/changed/rejected reviews invalidate acceptance and cannot pass a recheck')
        fixture.write_text(clean.replace('hidden : Prop := True', 'hidden : Prop := False'))
        assert 'not established' in state()
        failure = command(check + ['--all'], root, False)
        assert 'stale statement review' in failure, failure
        new_audit = json.loads((root / 'work/checks/declaration-audit.json').read_text())
        assert all(new_audit['statement_hashes'][i] != audit['statement_hashes'][i] for i in ['D', 'T'])
        print('PASS: changing an unmapped helper definition invalidates both its dependent definition and theorem reviews')
        fixture.write_text(clean)
        command(check + ['--all'], root)
        extra = project / 'Supplemental/NewFile.lean'
        extra.write_text('theorem irrelevant : True := trivial\n')
        assert 'not established' in state()
        extra.unlink()
        assert state() == 'checker receipt current'
        source_path = root / 'reference/fixture.tex'
        source_path.write_text(source + 'source changed\n')
        assert 'not established' in state()
        assert 'source review hash mismatch' in command(check + ['--all'], root, False)
        source_path.write_text(source)
        print('PASS: new project files and changed mathematical source invalidate current receipts')
        audit_module = project / 'Supplemental/Audit.lean'
        audit_module.write_text(audit_module.read_text() + '\n-- audit edited\n')
        assert 'audit module changed' in command(check, root, False)
        print('PASS: the proof project cannot silently replace the shipped audit module')
        audit_module.write_bytes((root / 'lean/Supplemental/Audit.lean').read_bytes())
        full_spec = {'mode': 'full', 'extra': [], 'certificates': [], 'targets': ['T'],
                     'tasks': [], 'acceptance_stages': [1, 2, 3]}
        dump(root / 'EXECUTION.json', full_spec)
        result = json.loads(command(check + ['--all'], root))
        assert [r['stage'] for r in result['stages']] == [1, 2, 3]
        full_spec['certificates'] = ['synthetic-required-certificate']
        dump(root / 'EXECUTION.json', full_spec)
        failure = command(check + ['--all'], root, False)
        assert 'missing certificate: synthetic-required-certificate' in failure, failure
        assert json.loads((root / 'work/checks/stage-1.json').read_text())['passed']
        assert not json.loads((root / 'work/checks/stage-2.json').read_text())['passed']
        print('PASS: --all checks all three configured stages and rejects a missing Stage-2 certificate after Stage 1 succeeds')
    print('ALL ACCEPTANCE CONTROLS PASSED (synthetic core fixture, not mathematical formalization)')


if __name__ == '__main__':
    main()
