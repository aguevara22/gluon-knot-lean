from pathlib import Path
from hashlib import sha256
import re,json
base=Path(__file__).resolve().parents[2];check=base/'work/checks'
def sha(p):return sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(base))
m=json.loads((check/'root-gates-port-preparation.json').read_text());ports={}
for dest,v in m['new_modules'].items():
 p=base/v['candidate'];assert sha(p)==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  src=base/f['source'];assert sha(src)==f['source_sha256'];s=src.read_text();b=s[s.index('namespace SM'):]
  if '#print axioms' in b:b=b.split('#print axioms')[0].rstrip()+'\n'
  assert sha256(b.encode()).hexdigest()==f['body_sha256'];blocks.append(b)
 actual=p.read_text();body=actual[actual.index('namespace SM'):]
 assert body=='\n'.join(blocks),dest
 ports[dest]={'candidate':v['candidate'],'candidate_sha256':sha(p),'source_fragments':v['source_fragments'],'fragment_bodies_byte_for_byte_equal':True,'only_between_fragment_separator':'one newline','imports':re.findall(r'^import (\S+)',actual,re.M)}
assert all(sha(base/'work/lean'/p)==h for p,h in m['prior_SM_files_sha256'].items())
names=[]
for review in ['root-boundary-prototype','finite-compositions-prototype','gates-prototype']:
 d=json.loads((base/'work/reviews'/(review+'.json')).read_text())
 for n in d['evidence']['checked_declarations']:
  if n not in names:names.append(n)
t='import SM.Gates\nimport SM.FiniteCompositions\n\nset_option pp.fullNames true\nset_option pp.universes false\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
transparent=['SM.rootData','SM.BoundaryInterval','SM.IntervalComposition','SM.signTheta','SM.IntervalComposition.nearSign','SM.IntervalComposition.farSign','SM.IntervalComposition.ordinaryWeight','SM.IntervalComposition.rootWeight','SM.gatesData']
t+='\n'.join('#print '+n for n in transparent)+'\n'
exnames=[]
for f,ns in [('root-boundary-review-examples.lean','RootBoundaryIndependentReview'),('finite-and-gates-review-examples.lean','FiniteAndGatesIndependentReview'),('gates-equivariance-review-examples.lean','GatesEquivarianceIndependentReview')]:
 e=(check/f).read_text();new=[ns+'.'+n for n in re.findall(r'^theorem (\w+)',e,re.M)];exnames+=new;t+='\n'+e+'\n'+'\n'.join('#print axioms '+n for n in new)+'\n'
(check/'root-gates-canonical-review-types.lean').write_text(t)
out={'status':'candidate body comparison complete; canonical installed files, audit and kernel check pending','ports':ports,'prior_SM_count':len(m['prior_SM_files_sha256']),'all_285_old_SM_unchanged':True,'checked_declarations':names,'examples':exnames,'transparent_predicates_printed':transparent,'canonical_trace':'work/checks/root-gates-canonical-review-types.lean','canonical_trace_sha256':sha(check/'root-gates-canonical-review-types.lean'),'prototype_reviews_sha256':{str('work/reviews/'+n+'.json'):sha(base/'work/reviews'/(n+'.json')) for n in ['root-boundary-prototype','finite-compositions-prototype','gates-prototype']}}
(check/'root-gates-canonical-review-preparation.json').write_text(json.dumps(out,indent=2)+'\n')
print('Three exact candidate bodies verified; prepared',len(names),'declarations and',len(exnames),'canonical consumer checks')
