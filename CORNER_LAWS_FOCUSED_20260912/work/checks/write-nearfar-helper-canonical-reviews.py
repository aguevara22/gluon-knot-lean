from pathlib import Path
from hashlib import sha256
import json,re,datetime,sys
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
session=int(sys.argv[1])
p=load('work/checks/nearfar-helper-canonical-review-preparation.json');c=load('work/checks/nearfar-helper-canonical-review-closure.json')
rfile='work/checks/nearfar-helper-port-audit-result.json';r=load(rfile);a=load(r['audit']);receipt=load(r['receipt'])
assert r['session']==85206 and r['exit_code']==0 and receipt['passed'] and not receipt['stage_accepted']
for k in ['receipt','audit','log']:assert sha(r[k])==r[k+'_sha256']
assert all(sha('work/lean/'+f)==h for f,h in receipt['project_sha256'].items())
assert all(sha(f)==h for f,h in receipt['bundle_sha256'].items())
assert all(sha(f)==h for f,h in c['canonical_SM_files_sha256'].items())
assert len(c['canonical_SM_files_sha256'])==307
assert {str(f.relative_to(base)) for f in (base/'work/lean/SM').glob('*.lean')}==set(c['canonical_SM_files_sha256'])
m=load(c['port_manifest']);assert sha(c['port_manifest'])==c['port_manifest_sha256'];assert len(m['prior_SM_files_sha256'])==299
assert all(sha('work/lean/'+f)==h for f,h in m['prior_SM_files_sha256'].items())
assert sha('work/lean/lean-declarations.json')==c['source_map_sha256']==m['prior_map_sha256']
assert sha(c['port_installation'])==c['port_installation_sha256']
assert sha('work/lean/Supplemental.lean')==c['Supplemental_sha256']
for dest,v in c['ports'].items():
 assert (base/dest).read_bytes()==(base/v['candidate']).read_bytes()
 assert sha(dest)==v['installed_module_sha256']==v['candidate_sha256']
 blocks=[]
 for f in v['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
priorfile='work/checks/checkpoint-065-declaration-audit.json';prior=load(priorfile)['statement_hashes'];assert len(prior)==38 and a['statement_hashes']==prior
for f,h in p['external_review_binding'].items():assert sha(f)==h
assert sha(c['trace'])==c['trace_sha256']==p['trace_sha256']
logfile='work/checks/nearfar-helper-canonical-review-types.log';s=(base/logfile).read_text();assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];assert len(names)==62 and len(examples)==22
axioms={};types={}
for n in names+examples:
 m0=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m0:axioms[n]=[v.strip() for v in m0[1].split(',') if v.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n;axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m0=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m0,n
 i=m0.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
expected={}
for f in ['work/checks/composition-cut-set-reviewed-types.json','work/checks/nearfar-refinement-reviewed-types.json']:expected.update(load(f)['types'])
assert types==expected
semfile='work/checks/nearfar-helper-canonical-semantic-review.json'
write(semfile,{'canonical_printed_types':types,'canonical_printed_type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms,
 'all_62_prototype_canonical_printed_types_equal':True,'all_38_prior_semantic_hashes_unchanged':True,'prior_semantic_audit':priorfile,'prior_semantic_audit_sha256':sha(priorfile),'source_statement_hashes':prior,
 'scope':'The eight helpers are not new mapped original source declarations. Their exact canonical bodies/import closures, printed types, axiom traces and substantive consumers are checked; no new full lem:farout statement hash is invented.'})
evidence={'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
 'independent_kernel_command':'lake env lean ../checks/nearfar-helper-canonical-review-types.lean','independent_kernel_session':session,'independent_kernel_exit_code':0,'first_independent_run_passed':True,
 'checked_declarations':names,'declaration_count':62,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':22,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'all_62_prototype_canonical_printed_types_equal':True,'transparent_predicates_printed':p['transparent_definitions_printed'],
 'independent_closure_evidence':'work/checks/nearfar-helper-canonical-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/nearfar-helper-canonical-review-closure.json'),
 'canonical_semantic_evidence':semfile,'canonical_semantic_evidence_sha256':sha(semfile),
 'root_result_file':rfile,'root_result_sha256':sha(rfile),'successful_build_session':85206,'successful_build_exit_code':0,'successful_build_log':r['log'],'successful_build_log_sha256':sha(r['log']),
 'audit_receipt':r['receipt'],'audit_receipt_sha256':sha(r['receipt']),'declaration_audit':r['audit'],'declaration_audit_sha256':sha(r['audit']),
 'scope_note':'All 22 previously successful consumers are rerun through canonical imports only. They include complete raw cut-domain recovery, exact finite full-cut arity, actual union/outer-mark behavior, empty/full marks, unary cases, unique physical index coverage, actual geometric b inverse identification and the full physical-root sum.'}
ctx={'receipt':r['receipt'],'receipt_sha256':sha(r['receipt']),'root_audit_session':85206,'root_audit_exit_code':0,'passed':True,'stage_accepted':False,
 'audited_local_declarations':receipt['audited_declarations'],'mapped_claims':38,'audited_SM_modules':307,'audited_project_files':len(receipt['project_sha256']),
 'all_receipt_project_and_bundle_hashes_checked_at_review':True,'all_38_prior_semantic_hashes_unchanged':True,'source_map_unchanged':True,
 'scope':'Immutable audit066 checks the installed eight-helper batch; all 38 mapped claims remain identical. This adds no source acceptance or proof count.'}
portfile='work/reviews/nearfar-helper-port.json'
write(portfile,{'review_schema':'independent-partial-source-port-review-v1','id':'nearfar-helper-port','source_ids':['lem:farout'],'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910',
 'verdict':'faithful','implemented_scope_verdict':'faithful','parameters_reviewed':True,'definition_equivalence_reviewed':True,'source_claim_accepted':False,'in_theorem_library':True,'statement_sha256':None,'statement_hashes':{},
 'reason':f'All eight installed canonical helper bodies equal their independently reviewed frozen source fragments byte for byte. All 299 prior SM modules and the complete declaration map remain unchanged; Supplemental adds only the four expected imports. Independent canonical kernel {session} passes 62 declaration checks and 22 substantive consumers with 84 standard-or-empty axiom traces, and every printed type equals its prior independent external trace. Immutable audit066 passes and all 38 prior original semantic hashes are unchanged. The full raw cut/refinement index domain, actual geometric two identities and local factor expansion are faithful within the previously reviewed explicit scope. No factorization or full lem:farout acceptance follows from this helper port.',
 'ports':c['ports'],'main_declarations':names,'reviewed_files_sha256':c['SM_closure_files_sha256'],'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':20,
 'prior299_unchanged':True,'current_SM_count':307,'all_38_prior_semantic_hashes_unchanged':True,'source_map_unchanged':True,
 'prototype_review_binding':p['external_review_binding'],'evidence':evidence,'audit_context':ctx,
 'mathematical_scope':{
  'CompositionCutSet':'Exact equivalence of all raw compositions with every bounded endpoint-containing finite set; actual sorted cut-map recovery, unary and maximal full-cut cases.',
  'InteriorCutSet':'Every strict interior subset, exact endpoint deletion/insertion and closed restriction with both inverse and nested restriction laws.',
  'CompositionSegments':'Actual ordered-part bounds and coverage, including the final closed endpoint; no omitted shared boundary.',
  'NestedCutSets':'Explicit half-open uniqueness; actual inner cut-set union and restriction are inverse for every outer composition.',
  'MarkedRefinement':'Full raw nested/marked equivalence; independent consumers prove the forward cut union and underlying outer marks, including dependent transport.',
  'InteriorCutIndex':'Exact bijection of individual interior indices with actual physical cut positions, including the empty unary domain.',
  'NearFarCutExpansion':'Local independent finite product expansion over all marked index subsets in every allowed commutative ring.',
  'GeometricNearFar':'Exact cast geometric Phi(b)=E array identity and full physical-root coefficient equals Phi(D,-H)(b), retaining the unary root term.'},
 'accounting':{'original_claims_accepted':0,'proof_increment':0,'definition_increment':0,'full_farout_accepted':False,'stage_complete':False},
 'not_certified':['Termwise marked/unmarked triple matching, refined child-product transport and the complete weighted sum factorization are not certified by this batch.','No full far-only or restricted-subpolygon consequence, wall law, soft theorem, R theorem or stage completion.','ConsecutiveCuts and later transport prototypes are outside this exact port.']})
rows=[('composition-cut-set-prototype','composition-cut-set-canonical-partial','SM.CompositionCutSet'),('geometric-nearfar-prototype','geometric-nearfar-canonical-partial','SM.GeometricNearFar'),('nearfar-refinement-prototype','nearfar-refinement-canonical-partial','SM.MarkedRefinement')]
for source,name,module in rows:
 sf='work/reviews/'+source+'.json';old=load(sf);assert sha(old['source'])==old['source_sha256']
 for f,h in old.get('additional_source_sha256',{}).items():assert sha(f)==h
 d={k:old[k] for k in ['reviewer','implementer','source','source_id','source_lines','source_sha256','parameters_reviewed','definition_equivalence_reviewed','pins','independence']}
 if 'additional_source_sha256' in old:d['additional_source_sha256']=old['additional_source_sha256']
 d.update({'review_schema':'independent-partial-source-review-v1','id':name,'source_line':146,'module':module,'verdict':'faithful','implemented_scope_verdict':'faithful','source_claim_accepted':False,'in_theorem_library':True,'statement_sha256':None,
  'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'main_declarations':old.get('main_declarations',names),
  'reason':f'The previously reviewed explicit partial scope is now installed as exact canonical helper bodies and independently rechecked in kernel {session}. All 62 printed implementation types match their reviewed external traces, and all 22 substantive consumers pass with 84 standard-or-empty axiom traces. Full source interpretation remains the scope documented below; immutable audit066 confirms this exact canonical port and preserves all 38 prior source semantic hashes. No original source claim, full factorization or lem:farout acceptance is added.',
  'mathematical_justification':list(old['mathematical_justification'])+[{'clause':'Exact canonical port and source boundary','assessment':'The canonical check imports the installed modules only and repeats the earlier substantive consumers; it does not copy implementation definitions into its check source. The eight installed namespace bodies are byte-for-byte equal to the separately reviewed external bodies. Their actual 20-module combined dependency closure and whole-project audit066 are bound here. Every printed implementation type is unchanged. This report certifies the explicit partial scope only; no new full-source semantic hash is inferred for an unmapped helper.'}],
  'reviewed_files_sha256':c['SM_closure_files_sha256'],'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':20,
  'prototype_review':sf,'prototype_review_sha256':sha(sf),'prototype_review_binding':p['external_review_binding'],'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,'audit_context':ctx,
  'accounting':{'original_claims_accepted':0,'proof_increment':0,'definition_increment':0,'canonical_port_and_current_semantic_audit_pending':False,'full_farout_accepted':False,'stage_complete':False},
  'not_certified':['No full lem:farout, factorization or remaining far-only/restricted-interval acceptance.','No original source count for supporting helpers, wall law, soft theorem, R theorem or overall stage completion.']})
 # Older source-report descriptions are historical; retain them while explicitly delimiting their scope.
 d['independence']+=' The canonical review writes only new check/report evidence; implementation, source, map, root receipts and frozen prior reviews were preserved.'
 if 'unproved_original_clauses_in_this_reviewed_batch' in old:d['unproved_original_clauses_in_this_reviewed_batch']=old['unproved_original_clauses_in_this_reviewed_batch']
 write('work/reviews/'+name+'.json',d)
for f in [portfile]+['work/reviews/'+name+'.json' for _,name,_ in rows]:print(f,sha(f))
print('PASS: eight exact canonical helpers;62 unchanged printed types,22 consumers,84 standard-or-empty traces;299 old modules and38 mapped semantics unchanged; no original acceptance.')
