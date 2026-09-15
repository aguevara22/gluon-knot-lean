#!/usr/bin/env python3
"""Exercise periodic reporting, persisted scope, malformed state and exit status."""
import sys
sys.dont_write_bytecode = True
from contextlib import redirect_stdout
import io
import json
from pathlib import Path
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT))
from tools.progress import report, snapshot


def put(path, value):
    path.parent.mkdir(parents=True, exist_ok=True)
    path.write_text(json.dumps(value))


def check():
    with tempfile.TemporaryDirectory(prefix='handoff-progress-') as temporary:
        root = Path(temporary)
        (root / 'blueprint').mkdir()
        (root / 'blueprint/NODES.tsv').write_text('id\taction\nA\tDEFINE\nB\tPROVE\n')
        put(root / 'EXECUTION.json', {'extra': [], 'certificates': [], 'targets': ['B'], 'acceptance_stages': [1]})
        work = root / 'work'
        mapping = work / 'lean/lean-declarations.json'
        put(mapping, {'declarations': [{'id': 'A', 'status': 'pending'}, {'id': 'B', 'status': 'pending'}]})
        assert snapshot(work, root)['percentage'] == 0
        put(mapping, {'declarations': [{'id': 'A', 'status': 'accepted'}, {'id': 'B', 'status': 'review'}]})
        assert snapshot(work, root)['percentage'] == 50
        put(mapping, {'declarations': [{'id': 'A', 'status': 'accepted'}]})
        assert snapshot(work, root)['total'] == 2  # Missing baseline B stays pending.
        put(mapping, {'declarations': [{'id': 'A', 'status': 'accepted'}, {'id': 'helper', 'status': 'pending'}]})
        grown = snapshot(work, root)
        assert grown['total'] == 3 and grown['added_since_previous'] == ['helper']
        put(mapping, {'declarations': [{'id': 'A', 'status': 'accepted'}]})
        assert snapshot(work, root)['total'] == 3  # Missing helper stays tracked after restart.
        put(mapping, {'declarations': [{'id': 'A'}, {'id': 'A'}]})
        with redirect_stdout(io.StringIO()):
            failed = report(work, root)
        assert failed['percentage'] is None and 'duplicate' in failed['error']
        mapping.write_text('{broken')
        with redirect_stdout(io.StringIO()):
            assert report(work, root)['percentage'] is None
        put(mapping, {'declarations': [{'id': i, 'status': 'accepted'} for i in ['A', 'B', 'helper']]})
        complete = snapshot(work, root)
        assert complete['percentage'] == 100 and 'not established' in complete['acceptance']['1']
        print('PASS: 0/50/100% statuses; review not accepted; missing/deleted rows stay in denominator; scope expansion; malformed/duplicate state never fabricates progress')
        wrapper_work = root / 'wrapper-work'
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'tools/run_with_progress.py'),
            '--work-dir', str(wrapper_work), '--interval', '0.08', '--', sys.executable, '-c',
            'import time; print("execution child started", flush=True); time.sleep(0.25); raise SystemExit(3)'],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode == 3, result.stdout
        events = [json.loads(line) for line in (wrapper_work / 'progress/history.jsonl').read_text().splitlines()]
        assert len(events) >= 4 and all(e['percentage'] == 0 for e in events), result.stdout
        assert 'execution child started' in result.stdout
        print('PASS: automatic startup, periodic and exit reports; child output preserved; nonzero execution status propagated')
        broken_work = root / 'logging-unavailable'
        broken_work.mkdir()
        (broken_work / 'progress').write_text('not a directory')
        result = subprocess.run([sys.executable, '-B', str(ROOT / 'tools/run_with_progress.py'),
            '--work-dir', str(broken_work), '--interval', '0.05', '--', sys.executable, '-c',
            'print("proof command still ran"); raise SystemExit(7)'],
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
        assert result.returncode == 7 and 'proof command still ran' in result.stdout, result.stdout
        assert 'progress files unavailable' in result.stdout, result.stdout
        for interval in ['nan', 'inf', '0']:
            result = subprocess.run([sys.executable, '-B', str(ROOT / 'tools/run_with_progress.py'),
                '--interval', interval, '--', sys.executable, '-c', 'print("must not run")'],
                text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
            assert result.returncode == 2 and 'finite' in result.stdout
        print('PASS: logging failure does not block the execution command; invalid timer intervals are rejected')
    print('ALL PROGRESS TESTS PASSED')


if __name__ == '__main__':
    check()
