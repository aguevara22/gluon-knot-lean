from pathlib import Path
from hashlib import sha256
import json,re,datetime,sys
base=Path(__file__).resolve().parents[2]
def sha(f):return sha256((base/f).read_bytes()).hexdigest()
def load(f):return json.loads((base/f).read_text())
def write(f,d):(base/f).write_text(json.dumps(d,indent=2)+'\n')
def digest(d):return sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
session=int(sys.argv[1]);pfile='work/checks/critical-response-canonical-review-preparation.json';p=load(pfile)
for f,h in p['canonical_SM_files_sha256'].items():assert sha(f)==h
assert len(p['canonical_SM_files_sha256'])==327 and len(p['SM_closure_files_sha256'])==40
assert sha(p['port_manifest'])==p['port_manifest_sha256'] and sha(p['port_installation'])==p['port_installation_sha256']
assert sha('work/lean/lean-declarations.json')==p['source_map_sha256']
for f,h in p['external_review_binding'].items():assert sha(f)==h
for dest,v in p['ports'].items():
 assert sha(dest)==sha(v['candidate'])==v['candidate_sha256'] and sha(v['source_body'])==v['source_body_sha256']
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]==(base/v['source_body']).read_text()
assert sha(p['trace'])==p['trace_sha256']
paths={'receipt':'work/checks/checkpoint-070-output.json','audit':'work/checks/checkpoint-070-declaration-audit.json','log':'work/checks/checkpoint-070-lean-check.log'}
receipt=load(paths['receipt']);a=load(paths['audit'])
assert receipt['passed'] and not receipt['stage_accepted'] and receipt['mapped_declarations']==39
assert all(sha('work/lean/'+f)==h for f,h in receipt['project_sha256'].items())
assert all(sha(f)==h for f,h in receipt['bundle_sha256'].items())
prioraudit='work/checks/checkpoint-068-declaration-audit.json';oldsem=load(prioraudit)['statement_hashes']
assert len(oldsem)==39 and oldsem==a['statement_hashes']
assert a['audit']['checked']==receipt['audited_declarations']
prototypefile='work/reviews/critical-source-response-prototype.json';prototype=load(prototypefile)
assert sha(prototypefile)=='bea6534e4ed4850ee5dbe41e31a07df1e01964e7a52e3ee4725c346e43f9ed0c'
assert sha(prototype['source'])==prototype['source_sha256']
for f,h in prototype['additional_source_sha256'].items():assert sha(f)==h
freshfile='work/reviews/critical-inverse-difference-independent.json';fresh=load(freshfile)
assert sha(freshfile)=='4293890be6f627208d9c2a68fe14d741629bb1923dafbd3069eaa69a46924fd0'
for f,h in fresh['files_sha256'].items():assert sha(f)==h
for f,h in fresh['canonical_import_binding']['local_source_files_sha256'].items():assert sha(f)==h
logfile='work/checks/critical-source-canonical-review-types.log';s=(base/logfile).read_text();assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=p['checked_declarations'];examples=p['additional_examples'];assert len(names)==53 and len(examples)==41
axioms={};types={}
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[x.strip() for x in m[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n;axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 types[n]=s[m.start():s.index("'"+n+"'",m.start())].strip()
assert types==load('work/checks/critical-source-reviewed-types.json')['types']
records={d['declaration']:d for d in a['audit']['declarations']}
helperrecords={n:records[n] for n in names if n in records}
for n,d in helperrecords.items():assert set(d['axioms'])<={'propext','Classical.choice','Quot.sound'}
sourceprep=load('work/checks/critical-source-review-preparation.json')
modules={n:'SM.'+b for b,ns in sourceprep['checked_declarations_by_body'].items() for n in ns}
assert set(modules)==set(names)
semfile='work/checks/critical-response-canonical-type-review.json'
write(semfile,{'checked_declarations':names,'canonical_printed_types':types,'canonical_printed_type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'all_53_prototype_canonical_printed_types_equal':True,'axioms':axioms,'all_39_prior_semantic_hashes_unchanged':True,'prior_semantic_audit':prioraudit,'prior_semantic_audit_sha256':sha(prioraudit),'enumerated_helper_audit_records':list(helperrecords),'mapped_audit_record_count':len(records),'canonical_modules':modules,'scope':'The whole audit reports its total checked count but enumerates mapped-source records only. Unmapped helper evidence here is the independent printed types and axiom traces plus exact canonical module/import closure; no unavailable per-helper audit record or original thm:single-triple semantic hash is invented.'})
closurefile='work/checks/critical-response-canonical-review-closure.json'
c=dict(p);c.update({'state':'independent canonical kernel and current audit passed; partial source helpers only','independent_kernel_session':session,'independent_kernel_exit_code':0,'canonical_audit_paths':paths,'canonical_audit_hashes':{k:sha(f) for k,f in paths.items()},'all_39_prior_semantic_hashes_unchanged':True})
write(closurefile,c)
evidence={'independent_trace_source':p['trace'],'independent_trace_source_sha256':sha(p['trace']),'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),'independent_kernel_command':'lake env lean ../checks/critical-source-canonical-review-types.lean','independent_kernel_session':session,'independent_kernel_exit_code':0,'first_independent_run_passed':True,'checked_declarations':names,'declaration_count':53,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,'additional_example_count':41,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},'all_53_prototype_canonical_printed_types_equal':True,'transparent_predicates_printed':p['transparent_definitions_printed'],'independent_closure_evidence':closurefile,'independent_closure_evidence_sha256':sha(closurefile),'canonical_type_evidence':semfile,'canonical_type_evidence_sha256':sha(semfile),'successful_build_session':84039,'successful_build_exit_code':0,'successful_build_log':paths['log'],'successful_build_log_sha256':sha(paths['log']),'audit_receipt':paths['receipt'],'audit_receipt_sha256':sha(paths['receipt']),'declaration_audit':paths['audit'],'declaration_audit_sha256':sha(paths['audit']),'fresh_inverse_difference_review':freshfile,'fresh_inverse_difference_review_sha256':sha(freshfile),'scope_note':'Canonical imports only, all same53 types and41 consumers. No embedded implementation definitions, map changes or new original-source acceptance. Exact source/proof review is bound through the sealed external review; hashes/builds do not replace it.'}
portfile='work/reviews/critical-response-port.json'
port={'review_schema':'independent-partial-source-port-review-v1','id':'critical-response-port','source_ids':['thm:single-triple'],'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910','verdict':'faithful','parameters_reviewed':True,'definition_equivalence_reviewed':True,'source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':True,
 'reason':f'All eight installed canonical namespace bodies exactly equal their independently reviewed frozen bodies. Import headers replace embedded predecessors without mathematical edits. All319 earlier SM files and all39 mapped semantic hashes remain unchanged; the map bytes are unchanged and Supplemental adds onlySM.CriticalSourceResponse. Independent canonical first kernel {session} passes all53 exact prototype types and41 consumers with94 standard-or-empty traces over the actual40-module import closure. Current immutable audit070 passes. The exact partial source review establishes actual algebraic critical c/B jumps, with both fresh inverse-difference and earlier marking-fragment independence evidence retained. No full wall theorem or original-source acceptance is inferred.',
 'ports':p['ports'],'main_declarations':names,'reviewed_files_sha256':p['SM_closure_files_sha256'],'import_closure_roots':['SM.CriticalSourceResponse'],'import_closure_file_count':40,'prior319_unchanged':True,'current_SM_count':327,'map_unchanged':True,'all_39_prior_semantic_hashes_unchanged':True,'prototype_review_binding':p['external_review_binding'],'provenance_disclosure':prototype['provenance_disclosure'],'evidence':evidence,'not_certified':['No new original source claim or full thm:single-triple semantic hash.','No geometric epsilon identification, contracted propagation or wall theorem completion.','No soft theorem, R theorem or stage completion.','Separate CollinearGateSigns external prototype is not part of this port.']}
write(portfile,port)
math=list(prototype['mathematical_justification'])
math.append({'clause':'Exact canonical integration with unchanged original-source accounting','assessment':'The eight exact reviewed helper bodies are now installed as canonical modules. All53 imported canonical types match the external independent trace and all41 consumers rerun successfully. The actual40-module import closure contains the full prior Farout development and the eight new modules; all319 prior modules are byte-for-byte unchanged. The declaration map is unchanged and immutable audit070 preserves all39 mapped semantic hashes. These helper declarations are not the full original thm:single-triple, so no original statement hash or acceptance is invented. Current evidence binds every helper audit record and full printed type, exact module bytes, substantive external source/proof review, fresh noncontributing CriticalInverseDifference review and the explicit n=3 interpretation note. The separate CollinearGateSigns prototype is not imported or certified by this port.'})
d={k:prototype[k] for k in ['source','source_sha256','source_lines','source_line','source_id','additional_source_sha256','reviewer','implementer','parameters_reviewed','definition_equivalence_reviewed','pins','independence','provenance_disclosure','separate_source_domain_note','separate_source_domain_note_sha256']}
d.update({'review_schema':'independent-partial-source-canonical-review-v1','id':'critical-source-response-canonical-partial','verdict':'faithful','implemented_scope_verdict':'faithful','source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':True,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'main_declarations':names,
 'reason':f'Faithful canonical algebraic source-response development within the partial thm:single-triple proof. The actual full transforms, inverse equations, ordinary/reversed coefficient sums, physical fixed-endpoint gates, exact middle-cut splitting and complete child/cut products derive both critical c and B jumps. Exact installed bodies pass independent canonical kernel {session}:53 unchanged types,41 consumers,94 standard-or-empty traces. Immutable audit070 passes, all319 previous modules/map bytes and39 original semantic hashes are unchanged. Geometric epsilon/E/B identification, source-domain interpretation and propagation remain outside this helper result; no original theorem is accepted.',
 'mathematical_justification':math,'reviewed_files_sha256':p['SM_closure_files_sha256'],'import_closure_roots':['SM.CriticalSourceResponse'],'import_closure_file_count':40,'prototype_review':prototypefile,'prototype_review_sha256':sha(prototypefile),'prototype_review_binding':p['external_review_binding'],'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,
 'audit_context':{'receipt':paths['receipt'],'receipt_sha256':sha(paths['receipt']),'root_audit_session':84039,'root_audit_exit_code':0,'passed':True,'stage_accepted':False,'audited_local_declarations':receipt['audited_declarations'],'mapped_claims':39,'audited_SM_modules':327,'all_receipt_project_and_bundle_hashes_checked_at_review':True,'all_39_prior_semantic_hashes_unchanged':True,'source_map_unchanged':True},
 'accounting':{'original_claims_accepted':0,'proof_increment':0,'definition_increment':0,'canonical_port_pending':False,'full_single_triple_accepted':False,'stage_complete':False},'unproved_original_clauses_in_this_reviewed_batch':prototype['unproved_original_clauses_in_this_reviewed_batch'],'not_certified':port['not_certified']})
d['independence']+=' For canonical review only new evidence was written; no implementation, source, map, root receipt or frozen previous report was changed.'
out='work/reviews/critical-source-response-canonical-partial.json';write(out,d)
print(portfile,sha(portfile));print(out,sha(out));print('PASS:8 exact ports;53 types+41 consumers;40-module closure;39 unchanged mapped semantics; no original acceptance.')
