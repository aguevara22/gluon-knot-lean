"""Small shared configuration for the full and focused handoffs."""
import csv
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
DEFAULT_EXTRA = ['R:cv_theorem', 'Bridge:B1', 'Bridge:B2', 'Bridge:B3', 'Bridge:B4',
                 'Bridge:theorem', 'SM:comparison_unconditional']
DEFAULT_TASKS = [
    ('BOOTSTRAP', 'Install exact pins and build the scaffold; save resolved dependency manifest.'),
    ('STAGE1', 'Formalize the conservative STAGE1.tsv worklist.'),
    ('STAGE2', 'Schedule remaining SM rows as dependencies become available.'),
    ('R-ASSEMBLY', 'Prove the full-domain R theorem per OPEN_WORK.md.'),
    ('BRIDGE-REVIEW', 'Implement and independently review B1-B4 and the theorem.'),
    ('CENSUS-REBUILD', 'Reconstruct exact enumeration and fibre-connectedness evidence.'),
    ('TREE-CERTIFICATE', 'Reproduce SM/checks/treecheck.py and record the receipt.')]


def configuration(root=ROOT):
    spec = {'name': 'Full SM formalization', 'mode': 'full', 'extra': DEFAULT_EXTRA,
            'certificates': ['comp:census', 'comp:treecheck'], 'tasks': DEFAULT_TASKS,
            'targets': ['thm:comparison', 'SM:comparison_unconditional', 'R:cv_theorem'],
            'acceptance_stages': [1, 2, 3], 'progress_interval_seconds': 900}
    path = root / 'EXECUTION.json'
    if path.is_file():
        spec.update(json.loads(path.read_text()))
    return spec


def source_rows(root=ROOT):
    with (root / 'blueprint/NODES.tsv').open() as stream:
        return list(csv.DictReader(stream, delimiter='\t'))


def source_path(row):
    return row.get('source') or 'SM/' + row['file']


def required_ids(root=ROOT):
    spec = configuration(root)
    return {r['id'] for r in source_rows(root) if r['action'] not in {'SKIP', 'CERTIFICATE'}} | set(spec['extra']) | set(spec['certificates'])


SPEC = configuration()
