"""Record an observed successful root run; never grant source acceptance."""
from pathlib import Path
from datetime import datetime, timezone
import argparse, hashlib, json, re
ap = argparse.ArgumentParser()
ap.add_argument('stem'); ap.add_argument('session', type=int)
ap.add_argument('attempt'); ap.add_argument('count', type=int)
ap.add_argument('--deps', nargs='+', required=True)
ap.add_argument('--failed', nargs='*', type=int, default=[])
a = ap.parse_args()
assert re.fullmatch(r'[A-Za-z][A-Za-z0-9]*', a.stem)
assert a.attempt in ['first','second','third','fourth','fifth']
root = Path(__file__).resolve().parents[2]; p = root / 'work/checks'
proto = (p / f'{a.stem}.prototype.lean').read_text()
log = (p / f'{a.stem}-{a.attempt}-kernel.log').read_text()
expected = re.findall(r'^#print axioms (.+)$', proto, re.M)
traces = re.findall(r"'([^']+)' (?:depends on axioms: \[([^\]]*)\]|does not depend on any axioms)", log)
assert len(expected) == a.count and [n for n,_ in traces] == expected
assert not re.search(r'\berror(?:\(|:)',log)
axioms = {n:[s.strip() for s in axs.split(',') if s.strip()] for n,axs in traces}
assert all(set(xs) <= {'propext','Classical.choice','Quot.sound'} for xs in axioms.values())
paths = [p / f'{s}.body.lean' for s in a.deps]
for path in paths: assert proto.count(path.read_text()) == 1, str(path)
paths += [p / f'{a.stem}.prototype.lean', p / f'{a.stem}-{a.attempt}-kernel.log']
r = {'utc':datetime.now(timezone.utc).isoformat(), 'kernel_session':a.session,
 'exit_code':0, 'first_run_passed':a.attempt=='first',
 'preserved_failed_sessions':a.failed,
 'files_sha256':{str(x.relative_to(root)):hashlib.sha256(x.read_bytes()).hexdigest() for x in paths},
 'printed_declarations':expected, 'declaration_axioms':axioms,
 'state':'Kernel-checked candidate; frozen; stronger fidelity and controlled canonical integration pending.',
 'source_claim_acceptance_increment':0, 'canonical_modules_unchanged':327}
q = p / f'{a.stem}-prototype-result.json'; assert not q.exists()
q.write_text(json.dumps(r,indent=2)+'\n')
print(f'{a.stem}: {a.count} candidates sealed for observed terminal root run {a.session}.')
