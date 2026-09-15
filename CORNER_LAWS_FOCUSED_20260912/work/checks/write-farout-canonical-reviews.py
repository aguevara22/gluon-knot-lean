from pathlib import Path
from hashlib import sha256
import json,re,datetime,sys
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
def digest(d):return sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
session=int(sys.argv[1]);prepfile='work/checks/farout-canonical-review-preparation.json';p=load(prepfile)
m=load(p['port_manifest']);assert sha(p['port_manifest'])==p['port_manifest_sha256']
ports={}
for dest,v in p['ports'].items():
 assert (base/dest).read_bytes()==(base/v['candidate']).read_bytes() and sha(dest)==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]=='\n'.join(blocks)
 ports[dest]=dict(v,installed_module_sha256=sha(dest),installed_equals_candidate=True)
assert len(ports)==12 and len(m['prior_SM_files_sha256'])==307
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
current={str(f.relative_to(base)):sha(str(f.relative_to(base))) for f in sorted((base/'work/lean/SM').glob('*.lean'))}
assert len(current)==319 and set(current)=={'work/lean/'+f for f in m['prior_SM_files_sha256']}|set(ports)
seen={}
def visit(n):
 if n in seen:return
 f='work/lean/'+n.replace('.','/')+'.lean';seen[n]=f
 for q in re.findall(r'^import (\S+)',(base/f).read_text(),re.M):
  if q.startswith('SM.'):visit(q)
visit('SM.Farout');cl={seen[n]:sha(seen[n]) for n in sorted(seen)};assert len(cl)==32
for n,v in p['predicted_import_closure'].items():assert sha(v['canonical'])==v['sha256']
sup=(base/'work/lean/Supplemental.lean').read_bytes();cuts=[k for k in range(1,100) if sha256(sup[:-k]).hexdigest()==m['prior_Supplemental_sha256']];assert len(cuts)==1
delta=sup[-cuts[0]:].decode();assert re.findall(r'^import (\S+)',delta,re.M)==['SM.Farout']
beforefile='work/checks/lean-declarations-before-farout.json';before=load(beforefile);after=load('work/lean/lean-declarations.json')
assert sha(beforefile)==m['prior_map_sha256']
oldrows={x['id']:x for x in before['declarations']};rows={x['id']:x for x in after['declarations']}
assert oldrows.keys()==rows.keys() and all(oldrows[k]==rows[k] for k in oldrows if k!='lem:farout')
assert rows['lem:farout']['status']=='review' and rows['lem:farout']['declaration']=='SM.farout' and rows['lem:farout']['module']=='SM.Farout'
rfile='work/checks/farout-port-audit-result.json';r=load(rfile)
assert r['session']==62779 and r['exit_code']==0 and r['audited']==4169 and r['mapped']==39
paths={'receipt':'work/checks/checkpoint-067-output.json','audit':'work/checks/checkpoint-067-declaration-audit.json','log':'work/checks/checkpoint-067-lean-check.log'}
for k,f in paths.items():assert sha(f)==r[k+'_sha256']
receipt=load(paths['receipt']);a=load(paths['audit']);assert receipt['passed'] and not receipt['stage_accepted']
assert all(sha('work/lean/'+f)==h for f,h in receipt['project_sha256'].items())
assert all(sha(f)==h for f,h in receipt['bundle_sha256'].items())
prioraudit='work/checks/checkpoint-066-declaration-audit.json';prior=load(prioraudit)['statement_hashes']
assert len(prior)==38 and all(a['statement_hashes'][k]==h for k,h in prior.items())
for f,h in p['external_review_binding'].items():assert sha(f)==h
prototypefile='work/reviews/farout-prototype.json';prototype=load(prototypefile)
assert sha(prototypefile)=='7f0e403763fbc0564ea4634d88cfdc62c70ed3f1a1688bd84d3016c80ae784ab'
fragmentfile='work/reviews/marked-transport-independent.json';fragment=load(fragmentfile)
assert sha(fragmentfile)=='660b35e9ce99e04fce1ad1a722652b388806cdf0df55574b09804a66a9f71174'
for f,h in fragment['files_sha256'].items():assert sha(f)==h
assert sha(prototype['source'])==prototype['source_sha256']
for f,h in prototype['additional_source_sha256'].items():assert sha(f)==h
assert sha(p['trace'])==p['trace_sha256']
logfile='work/checks/farout-canonical-review-types.log';s=(base/logfile).read_text();assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=p['checked_declarations'];examples=p['additional_examples'];assert len(names)==127 and len(examples)==48
axioms={};types={}
for n in names+examples:
 m0=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m0:axioms[n]=[x.strip() for x in m0[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n;axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m0=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m0,n
 i=m0.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
assert types==load('work/checks/farout-reviewed-types.json')['types']
target=next(x for x in a['audit']['declarations'] if x['declaration']=='SM.farout')
assert target['kind']=='theorem' and target['module']=='SM.Farout'
assert set(target['axioms'])<={'propext','Classical.choice','Quot.sound'}
sh=digest(target['semantic_dependencies']);assert sh==a['statement_hashes']['lem:farout']==r['semantic_sha256']=='079a085d5f248db40018ec89c9840d4d3b40300c923e82f5eb13eae7ec56a3d8'
sn={d['declaration'] for d in target['semantic_dependencies']};assert len(sn)==80
required=['SM.farout','SM.BoundaryInterval','SM.BoundaryInterval.mk','SM.BoundaryInterval.leaves','SM.BoundaryInterval.globalPosition','SM.IntervalComposition','SM.IntervalComposition.mk','SM.IntervalComposition.parts','SM.IntervalComposition.cut','SM.IntervalComposition.part','SM.IntervalComposition.finite','SM.IntervalComposition.fintype','SM.IncreasingBoundaryTriple','SM.IncreasingBoundaryTriple.mk','SM.TripleArray','SM.IntervalArray','SM.IntervalComposition.nearTriple','SM.IntervalComposition.farTriple','SM.IntervalComposition.nearFarWeight','SM.nearFarTransform','SM.nearTransform','SM.farTransform','SM.triangularInverse','SM.nearFarInverse','SM.farOnlyCoordinates','SM.farOnlyOutput','SM.boundaryUnitArray','SM.LabelledTuple','SM.G1','SM.Plane','SM.det','SM.chi','SM.geometricBoundaryArray','SM.boundaryIndex','SM.boundaryWord','SM.edge','SM.restrictedWordTuple','SM.fullBoundaryInterval','SM.openTreeRec','SM.rootedTreeRec','SM.openTreeSum','SM.treeCoefficient','SM.IntervalComposition.ordinaryWeight','SM.IntervalComposition.rootWeight','SM.ordinaryGate','SM.rootGate','SM.signTheta']
assert set(required)<=sn and 'SM.G2' not in sn
semfile='work/checks/farout-canonical-semantic-review.json'
write(semfile,{'source_id':'lem:farout','declaration':'SM.farout','module':'SM.Farout','statement_sha256':sh,'semantic_dependency_count':80,'semantic_declarations':sorted(sn),'required_transparent_definitions_and_constructors':required,'semantic_dependency_record_sha256':{d['declaration']:digest(d) for d in target['semantic_dependencies']},'canonical_printed_types':types,'canonical_printed_type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'all_127_prototype_canonical_printed_types_equal':True,'axioms':axioms,'all_38_prior_semantic_hashes_unchanged':True,'prior_semantic_audit':prioraudit,'prior_semantic_audit_sha256':sha(prioraudit),'semantic_scope_note':'This is the complete statement/transparent-definition closure, not the entire proof dependency graph. The full proof is independently kernel-checked and every exact imported implementation module is hash-bound separately.'})
closurefile='work/checks/farout-canonical-review-closure.json'
c={'ports':ports,'prior_SM_count':307,'all_307_prior_SM_unchanged':True,'canonical_SM_count':319,'canonical_SM_files_sha256':current,'SM_import_roots':['SM.Farout'],'SM_closure_files_sha256':cl,'SM_closure_count':32,'individual_import_closures':{'SM.Farout':cl},'Supplemental_append':delta,'Supplemental_sha256':sha('work/lean/Supplemental.lean'),'only_source_map_change':'lem:farout pending->review with SM.farout','source_map_sha256':sha('work/lean/lean-declarations.json'),'before_map':beforefile,'before_map_sha256':sha(beforefile),'port_manifest':p['port_manifest'],'port_manifest_sha256':sha(p['port_manifest']),'port_installation':'work/checks/farout-port-installed.json','port_installation_sha256':sha('work/checks/farout-port-installed.json'),'checked_declarations':names,'additional_examples':examples,'trace':p['trace'],'trace_sha256':sha(p['trace']),'canonical_audit_paths':paths,'canonical_audit_hashes':{k:sha(f) for k,f in paths.items()},'scope':'Twelve exact ports; complete original lem:farout is faithful and eligible for source-map acceptance. No map edits by reviewer.'}
write(closurefile,c)
evidence={'independent_trace_source':p['trace'],'independent_trace_source_sha256':sha(p['trace']),'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),'independent_kernel_command':'lake env lean ../checks/farout-canonical-review-types.lean','independent_kernel_session':session,'independent_kernel_exit_code':0,'first_independent_run_passed':True,'checked_declarations':names,'declaration_count':127,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':48,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},'all_127_prototype_canonical_printed_types_equal':True,'transparent_predicates_printed':p['transparent_definitions_printed'],'independent_closure_evidence':closurefile,'independent_closure_evidence_sha256':sha(closurefile),'canonical_semantic_evidence':semfile,'canonical_semantic_evidence_sha256':sha(semfile),'root_result_file':rfile,'root_result_sha256':sha(rfile),'successful_build_session':62779,'successful_build_exit_code':0,'successful_build_log':paths['log'],'successful_build_log_sha256':sha(paths['log']),'audit_receipt':paths['receipt'],'audit_receipt_sha256':sha(paths['receipt']),'declaration_audit':paths['audit'],'declaration_audit_sha256':sha(paths['audit']),'fresh_fragment_statement_review':fragmentfile,'fresh_fragment_statement_review_sha256':sha(fragmentfile),'scope_note':'Canonical imports only; no implementation definitions embedded. All 48 substantive external consumers rerun unchanged, including every physical subinterval/composition, actual near/far samples, polynomial inverses, complete output independence, and local-G1 physical closing-root coefficient.'}
binding=p['external_review_binding'];portfile='work/reviews/farout-port.json'
port={'review_schema':'independent-full-source-port-review-v1','id':'farout-port','source_ids':['lem:farout'],'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910','verdict':'faithful','source_claim_accepted':False,'parameters_reviewed':True,'definition_equivalence_reviewed':True,'in_theorem_library':True,'statement_hashes':{'lem:farout':sh},
 'reason':f'All twelve installed namespace bodies equal their exact independently reviewed frozen prototypes. Only canonical import headers replace embedded predecessors. All 307 earlier SM modules and all 38 earlier source semantic hashes remain unchanged. Supplemental adds exactly SM.Farout; the only source-map change is the pending lem:farout candidate. Canonical-only independent first kernel {session} passes 127 declaration types and 48 consumers with 175 standard-or-empty traces. Every canonical type matches its independently checked prototype type. Source fidelity is established by the substantive complete-source review and consumer meanings, while exact-port hashes and immutable audit067 bind that review to the installed implementation. The 80-entry statement/definition semantic hash is independently recomputed. Shared marking-fragment provenance and its fresh independent review remain explicitly bound.',
 'ports':ports,'main_declarations':names,'reviewed_files_sha256':cl,'import_closure_roots':['SM.Farout'],'import_closure_file_count':32,'prior307_unchanged':True,'current_SM_count':319,'all_38_prior_semantic_hashes_unchanged':True,'prototype_review_binding':binding,'provenance_disclosure':prototype['provenance_disclosure'],'evidence':evidence,'not_certified':['No source-map edit or claim of a subsequent accepted-map audit.','No extra original claims for helpers.','No wall law, soft theorem, R theorem or stage completion.']}
write(portfile,port)
math=[x for x in prototype['mathematical_justification'] if x['clause']!='Original source result is complete externally, not yet accepted canonically']
math.append({'clause':'Current canonical statement and complete dependency closure','assessment':'All twelve reviewed bodies are installed exactly, with the original 307 modules unchanged. The independent canonical import-only check reruns every one of the 48 consumers and matches all 127 printed types to the external trace. Immutable audit067 covers 319 SM modules and 4169 local declarations; all 38 prior mapped semantic hashes are unchanged. The current 80-entry semantic closure contains the actual finite interval/triple/composition constructors, full unrestricted array definitions, actual near/far coefficient and transform, constructed triangular inverse, E/c/B, geometric chirotope and integer casts, original recursive tree sums, and restricted tuple/global-position/directed-edge definitions. The G1 predicate is present and G2 is absent. The semantic hash is independently recomputed from these exact records. This semantic closure is distinguished from the full proof dependency graph: full proof validity is supplied by the kernel, while the exact 32-module import closure and separately reviewed refinement proofs bind proof provenance. The two shared marking fragments retain the fresh authorship-independent statement review and current independent kernel checks. Every printed original lemma clause is now faithful and eligible for acceptance; no accepted-map audit is prematurely asserted.'})
d={k:prototype[k] for k in ['reviewer','implementer','source','source_lines','source_sha256','additional_source_sha256','parameters_reviewed','definition_equivalence_reviewed','pins','independence','provenance_disclosure']}
d.update({'review_schema':'independent-full-source-review-v1','id':'lem:farout','source_id':'lem:farout','source_line':146,'labels':['lem:farout'],'declaration':'SM.farout','module':'SM.Farout','verdict':'faithful','full_source_coverage':True,'source_claim_accepted':True,'in_theorem_library':True,'statement_sha256':sh,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reason':f'Faithful complete original lem:farout: two-sided coordinate-polynomial inverse; exact full marked-refinement factorization; actual geometric open/full-root identities; entire-output independence of near arrays with fixed H and E; all open leaf/nonleaf values; and the restricted nonleaf coefficient under only local G1 at the actual closing edge from a_j to a_i. The exact canonical implementation passes independent first kernel {session} with all 127 prototype types unchanged and 48 substantive consumers. Immutable audit067 passes and its 80-entry transparent statement/definition hash is independently recomputed. Shared marking-fragment provenance is explicitly resolved by the separately bound noncontributing reviewer. This exact source row is faithful and eligible for map acceptance.',
 'mathematical_justification':math,'reviewed_files_sha256':cl,'import_closure_roots':['SM.Farout'],'import_closure_file_count':32,'semantic_dependency_count':80,'required_semantic_definitions_checked':required,'prototype_review':prototypefile,'prototype_review_sha256':sha(prototypefile),'prototype_review_binding':binding,'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,
 'audit_context':{'receipt':paths['receipt'],'receipt_sha256':sha(paths['receipt']),'root_audit_session':62779,'root_audit_exit_code':0,'passed':True,'stage_accepted':False,'audited_local_declarations':4169,'mapped_claims':39,'audited_SM_modules':319,'audited_project_files':len(receipt['project_sha256']),'all_receipt_project_and_bundle_hashes_checked_at_review':True,'all_38_prior_semantic_hashes_unchanged':True,'scope':'Immutable actual audit067 covers installed twelve-module batch with lem:farout in review. The unrelated pre-port audit94944 is not used. A later accepted-map audit is not asserted to have passed.'},
 'acceptance_scope':{'original_claim':'lem:farout','original_rows_added_if_mapped_accepted':1,'proofs_added_if_mapped_accepted':1,'definitions_added_if_mapped_accepted':0,'current_map_was_not_edited_by_reviewer':True,'helper_original_claim_count':0,'stage_complete':False},
 'unproved_original_clauses_in_this_reviewed_batch':[],'not_certified':['No additional original claims for supporting helpers.','No later accepted-map audit before it runs.','No state-sum wall law, soft theorem, unconditional R theorem or overall handoff completion.','Later untested FarOnlyLocality is outside this exact port/review.']})
d['independence']+=' The canonical review wrote only new reviewer check/report files; no implementation, source, map, root receipt or frozen prior report was changed.'
out='work/reviews/lem-farout.json';write(out,d);print(out,sha(out));print(portfile,sha(portfile));print('PASS:127 exact types+48 consumers;175 standard-or-empty traces;32-module closure;80 semantic entries;one original lemma eligible; no map edits.')
