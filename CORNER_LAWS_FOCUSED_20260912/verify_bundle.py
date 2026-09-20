#!/usr/bin/env python3
"""Verify the focused source subset, exact extracts and dependency worklist."""
import sys
sys.dont_write_bytecode = True
import csv
from graphlib import TopologicalSorter
import json
from pathlib import Path
import re

# This file is installed as verify_bundle.py at the focused package root.
ROOT = Path(__file__).resolve().parent
sys.path.insert(0, str(ROOT))
from tools.bundlelib import FRAMES, digest, manifest_rows, require, safe_file, verify_manifest
from tools.quote_realignment import check_quotes


def render(extracts):
    pieces = ['# Selected source statements and printed proofs\n\nRead source context for unlabelled notation. Historical status tags are not acceptance.\n']
    for x in extracts:
        pieces.append('\n## ' + x['id'] + ' — ' + x['action'] + '\n')
        for s in x['segments']:
            raw = ''.join(safe_file(ROOT, s['source']).read_text().splitlines(keepends=True)[s['start']-1:s['end']])
            require(digest(raw.encode()) == s['sha256'], 'excerpt source mismatch: ' + x['id'])
            pieces.append('\n' + s['source'] + ':' + str(s['start']) + '–' + str(s['end']) + '\n\n```tex\n' + raw + '```\n')
    return ''.join(pieces)


def verify():
    payloads = verify_manifest(ROOT, 'MANIFEST.sha256')
    for name in ['README.md', 'TARGETS.md', 'PROOF_PLAN.md', 'PROGRESS.md', 'AGENTS.md',
                 'START_HERE.md', 'FINAL_REVIEW.md', 'R_ASSEMBLY_SPEC.md', 'tools/receipts.py',
                 'EXECUTION.json', 'tools/bootstrap.py', 'tools/check_lean.py',
                 'tools/progress.py', 'tools/run_with_progress.py', 'lean/axiom-policy.json',
                 'blueprint/DEPENDENCIES.json', 'provenance/SOURCES.json',
                 'provenance/BRIDGE_REALIGNMENT_SM15.json', 'tools/quote_realignment.py']:
        require(name in payloads, 'missing required payload: ' + name)
    frames = json.loads((ROOT / 'provenance/SOURCES.json').read_text())
    source_count = 0
    for name, frame in frames.items():
        raw = safe_file(ROOT, frame['manifest']).read_bytes()
        require(digest(raw) == FRAMES[name][2] == frame['pin'], 'original frame pin: ' + name)
        original = manifest_rows(raw)
        require(len(original) == FRAMES[name][3] == frame['original_count'], 'original inventory: ' + name)
        for file in frame['files']:
            data = safe_file(ROOT / frame['directory'], file).read_bytes()
            require(file in original and digest(data) == original[file], 'source subset mismatch: ' + file)
            source_count += 1
    print('PASS:', source_count, 'unchanged source-context files against original pinned manifests (subset only)')
    extracts = json.loads((ROOT / 'blueprint/EXTRACTS.json').read_text())
    require(render(extracts) == (ROOT / 'blueprint/STATEMENTS_AND_PROOFS.md').read_text(), 'rendered extract drift')
    axioms = [x for x in extracts if x['action'] == 'AXIOM']
    require(render(axioms) == (ROOT / 'blueprint/AXIOM_REGISTRY.md').read_text(), 'axiom registry drift')
    rows = list(csv.DictReader((ROOT / 'blueprint/NODES.tsv').open(), delimiter='\t'))
    require(len(rows) == 172 and len({r['id'] for r in rows}) == 172, 'focused source inventory')
    require({x['id'] for x in extracts} == {r['id'] for r in rows}, 'extract inventory')
    by_id = {r['id']: r for r in rows}
    clauses = {'CV:selector_A': (1017, 'lem:selectorid(A)'),
               'CV:singleton_D_i': (2682, 'thm:s7universal(D)(i)')}
    for extract in extracts:
        row = by_id[extract['id']]
        first = extract['segments'][0]
        require(row['source'] == first['source'] and int(row['line']) == first['start']
                and int(row['proofs']) == len(extract['segments']) - 1
                and row['action'] == extract['action'], 'source-map metadata: ' + row['id'])
        if row['id'] in clauses:
            line, label = clauses[row['id']]
            require(first['source'] == 'reference/R/CV/d6_vertexedge.tex' and first['start'] == line
                    and row['labels'] == label and row['action'] == 'PROVE', 'clause mapping: ' + row['id'])
            continue
        body = ''.join((ROOT / first['source']).read_text().splitlines(keepends=True)[first['start']-1:first['end']])
        body = re.sub(r'(?<!\\)%[^\n]*', '', body)
        env = re.search(r'\\begin\{([^}]+)\}', body).group(1)
        labels = re.findall(r'\\label\{([^}]+)\}', body)
        action = ('DEFINE' if env in {'definition', 'convention'} else
                  'AXIOM' if env == 'literature' else
                  'HYPOTHESIS' if env == 'hypothesis' or row['id'] == 'CV:ax:R' else 'PROVE')
        require(env == row['env'] and set(labels) == set(row['labels'].split()) and action == row['action'],
                'source environment/alias/action mismatch: ' + row['id'])
    spec = json.loads((ROOT / 'EXECUTION.json').read_text())
    graph = json.loads((ROOT / 'blueprint/DEPENDENCIES.json').read_text())
    ids = {r['id'] for r in rows} | set(spec['extra'])
    require(set(graph['edges']) == ids and all(set(d) <= ids for d in graph['edges'].values()), 'DAG endpoints')
    order = list(TopologicalSorter({k: sorted(v) for k, v in sorted(graph['edges'].items())}).static_order())
    require(order == graph['order'], 'dependency order')
    require(all(set(r['deps'].split()) == set(graph['edges'][r['id']]) for r in rows), 'TSV dependency mismatch')
    require((ROOT / 'blueprint/NODES.tsv').read_bytes() == (ROOT / 'blueprint/STAGE1.tsv').read_bytes(), 'focused acceptance scope mismatch')
    require(set(spec['targets']) <= ids and 'SM:corner_laws_and_soft' in ids, 'missing final target')
    seen = {'SM:corner_laws_and_soft'}
    pending = list(seen)
    while pending:
        for dep in graph['edges'][pending.pop()]:
            if dep not in seen:
                seen.add(dep)
                pending.append(dep)
    require(seen == ids, 'selected obligations outside the final target dependency graph')
    require(spec['mode'] == 'focused' and spec['acceptance_stages'] == [1] and not spec['certificates'], 'focused mode')
    policy = json.loads((ROOT / 'lean/axiom-policy.json').read_text())
    required_axioms = {'lit:homfly', 'lp:lm', 'lp:lm-uniqueness', 'ng:finite-word', 'src:contact'}
    # A literature input may carry a second declaration under a key '<id> (<note>)' (author's decision D-GAP2, 2026-09-15);
    # the ceiling is on the set of literature inputs (labels), which must still be exactly the five.
    require({k.split(' ')[0] for k in policy['literature']} == {x['id'] for x in axioms} == required_axioms, 'literature ceiling')
    require('hd:tableau-source' not in ids and 'CV:thm:main' not in ids and 'CV:ax:lawful' not in ids, 'unrelated or circular scope')
    # Check the sealed SM11 quotations against SM15 through the pinned realignment ledger.
    quotes = json.loads((ROOT / 'reference/BRIDGE/QUOTATIONS.json').read_text())['quotes']
    ledger = json.loads((ROOT / 'provenance/BRIDGE_REALIGNMENT_SM15.json').read_text())
    frame_bytes = {name: {file: safe_file(ROOT / frame['directory'], file).read_bytes() for file in frame['files']}
                   for name, frame in frames.items()}
    realigned = check_quotes(quotes, frame_bytes, ledger, 'SM15')
    require(len(quotes) == 59 and sum(realigned['counts'].values()) == 59, 'quotation inventory')
    print('PASS: 59 bridge quotations checked against SM15', json.dumps(realigned['counts'], sort_keys=True),
          '; superseded:', ', '.join(realigned['superseded']))
    print('PASS: 172 source/clause rows +', len(spec['extra']), 'R/bridge/final obligations; five literature inputs')
    print('FOCUSED BUNDLE VERIFIED:', len(payloads), 'files; no mathematical acceptance is inferred')


if __name__ == '__main__':
    try:
        verify()
    except (ValueError, OSError, KeyError, TypeError) as error:
        print('FAIL:', error, file=sys.stderr)
        sys.exit(1)
