from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parents[2]
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def rel(p):return str(p.relative_to(base))
manifest=json.loads((base/'work/checks/relgp-port-candidate-files.json').read_text())
ports={}
for key,v in manifest['new_modules'].items():
 source=base/v['source'];actual=base/key;candidate=base/v['candidate']
 assert sha(source)==v['source_sha256'];assert actual.read_bytes()==candidate.read_bytes();assert sha(actual)==v['sha256']
 s=source.read_text();b=s[s.index('namespace SM'):]
 if '#print axioms' in b:b=b.split('#print axioms')[0].rstrip()+'\n'
 a=actual.read_text();ab=a[a.index('namespace SM'):]
 assert ab==b,key
 ports[key]={'source':v['source'],'source_sha256':sha(source),'module_sha256':sha(actual),'body_sha256':hashlib.sha256(b.encode()).hexdigest(),'body_byte_for_byte_equal':True,'imports':re.findall(r'^import (\S+)',a,re.M)}
old=manifest['prior_SM_files_sha256']; assert all(sha(base/'work/lean'/k)==v for k,v in old.items())
current={rel(p):sha(p) for p in sorted((base/'work/lean/SM').glob('*.lean'))};assert len(current)==285
assert set(current)=={'work/lean/'+x for x in old}|set(ports)
sup=(base/'work/lean/Supplemental.lean').read_bytes();delta=b'\nimport SM.RelativeGeneralPosition\n';assert sup.endswith(delta);assert hashlib.sha256(sup[:-len(delta)]).hexdigest()==manifest['prior_Supplemental_sha256']
seen={}
def visit(m):
 if m in seen:return
 p=base/'work/lean'/Path(m.replace('.','/')+'.lean');seen[m]=p
 for x in re.findall(r'^import (\S+)',p.read_text(),re.M):
  if x.startswith('SM.'):visit(x)
visit('SM.RelativeGeneralPosition')
prior=json.loads((base/'work/checks/relative-general-position-review-closure.json').read_text())
assert set(rel(x) for x in seen.values())==set(prior['SM_closure_files_sha256'])|set(ports)
assert all(sha(base/k)==v for k,v in prior['SM_closure_files_sha256'].items())
names=[]
for rev in ['point-control-geometry-prototype','point-control-walls-prototype','concurrence-order-prototype','relative-general-position-prototype']:
 d=json.loads((base/'work/reviews'/(rev+'.json')).read_text())
 for n in d['evidence']['checked_declarations']:
  if n not in names:names.append(n)
header='import SM.RelativeGeneralPosition\n\nset_option pp.fullNames true\nset_option pp.universes false\n'
header+='\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
header+='\n'.join('#print '+n for n in ['SM.RelativeGeneralPositionPath','SM.WallGerm.HasRegularWallKind','SM.CurveCubeSubdivision.TimedEventCertificate'])+'\n'
header+=(base/'work/checks/relative-general-position-review-examples.lean').read_text()
examples=re.findall(r'^theorem (\w+)',(base/'work/checks/relative-general-position-review-examples.lean').read_text(),re.M)
header+='\n'+'\n'.join('#print axioms RelgpIndependentReview.'+n for n in examples)+'\n'
(base/'work/checks/relative-general-position-canonical-review-types.lean').write_text(header)
d={'port_manifest':'work/checks/relgp-port-candidate-files.json','port_manifest_sha256':sha(base/'work/checks/relgp-port-candidate-files.json'),'ports':ports,'prior_SM_count':len(old),'all_280_prior_SM_unchanged':True,'canonical_SM_count':len(current),'canonical_SM_files_sha256':current,'SM_import_roots':['SM.RelativeGeneralPosition'],'SM_closure_count':len(seen),'SM_closure_files_sha256':{rel(seen[m]):sha(seen[m]) for m in sorted(seen)},'prior124closure_exactly_preserved':True,'sole_Supplemental_append':'\\nimport SM.RelativeGeneralPosition\\n','Supplemental_sha256':sha(base/'work/lean/Supplemental.lean'),'checked_declarations':names,'example_count':len(examples),'canonical_trace_sha256':sha(base/'work/checks/relative-general-position-canonical-review-types.lean')}
(base/'work/checks/relative-general-position-canonical-review-closure.json').write_text(json.dumps(d,indent=2)+'\n')
print('All five ports byte-identical bodies; old280 unchanged; exact129closure; declarations',len(names),'examples',len(examples))
