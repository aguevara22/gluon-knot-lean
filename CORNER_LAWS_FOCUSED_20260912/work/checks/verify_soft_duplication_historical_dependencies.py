"""Resolve historical dependency bindings without rewriting their original records."""
from pathlib import Path
from datetime import datetime, timezone
import hashlib
import json

ROOT = Path(__file__).resolve().parents[2]
C = ROOT / 'work/checks'
def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()

groups = ['SoftDuplicationSpanningBothChildFactors', 'SoftDuplicationSpanningTransform']
checked = []
records = {}
for stem in groups:
    draft_path = C / f'{stem}-draft-dependency-bindings.json'
    draft = json.loads(draft_path.read_text())
    live = C / f'{stem}-body-dependencies.json'
    historical = C / f'{stem}-first-failed-body-dependencies.json'
    resolution = C / f'{stem}-historical-dependency-binding-resolution.json'
    r = json.loads(resolution.read_text())
    assert sha(draft_path) == r['original_manifest_sha256']
    assert sha(historical) == r['historical_reference_digest'] == r['historical_bytes_sha256']
    assert sha(live) == r['current_manifest_sha256']
    assert json.loads(historical.read_text()) == draft['ordered_body_dependencies']
    assert r['historical_reference_path'] == str(live.relative_to(ROOT))
    for manifest in [draft_path, C / f'{stem}-first-failure-bindings.json']:
        entries = json.loads(manifest.read_text())['files_sha256']
        for name, digest in entries.items():
            target = ROOT / name
            if target == live:
                target = historical
            elif manifest == draft_path:
                for kind in ['body', 'prototype']:
                    if target == C / f'{stem}.{kind}.lean':
                        target = C / f'{stem}-first-draft.{kind}.lean'
                        break
            assert sha(target) == digest, (stem, name, str(target))
            checked.append({'quoted_path':name, 'resolved_path':str(target.relative_to(ROOT)), 'sha256':digest})
    proto = (C / f'{stem}-first-failed.prototype.lean').read_text()
    order = []
    for name in draft['ordered_body_dependencies']:
        target = ROOT / name
        if name == f'work/checks/{stem}.body.lean':
            target = C / f'{stem}-first-failed.body.lean'
        body = target.read_text()
        assert proto.count(body) == 1
        order.append(proto.index(body))
    assert order == sorted(order)
    records[str(resolution.relative_to(ROOT))] = sha(resolution)

result = {'utc':datetime.now(timezone.utc).isoformat(), 'verification':'passed',
          'historical_groups':len(groups), 'resolved_bindings':checked,
          'resolution_records_sha256':records, 'original_records_modified':False,
          'source_claim_acceptance_increment':0}
out = C / 'checkpoint-096-historical-dependency-bindings.json'
assert not out.exists()
out.write_text(json.dumps(result, indent=2) + '\n')
print(f'PASS: {len(groups)} exact historical dependency manifests; {len(checked)} resolved file bindings.')
