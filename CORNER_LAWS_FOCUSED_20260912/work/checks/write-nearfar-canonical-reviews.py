from pathlib import Path
from hashlib import sha256
import json,re,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
def digest(d):return sha256(json.dumps(d,sort_keys=True,separators=(',',':')).encode()).hexdigest()
c=load('work/checks/nearfar-canonical-review-closure.json');prep=load('work/checks/nearfar-canonical-review-preparation.json')
rfile='work/checks/nearfar-port-audit-result.json';r=load(rfile);a=load(r['audit']);receipt=load(r['receipt'])
assert r['session']==90989 and r['exit_code']==0 and receipt['passed'] and not receipt['stage_accepted']
for k in ['receipt','audit','log']:assert sha(r[k])==r[k+'_sha256']
assert all(sha('work/lean/'+p)==h for p,h in receipt['project_sha256'].items())
assert all(sha(p)==h for p,h in receipt['bundle_sha256'].items())
assert all(sha(p)==h for p,h in c['canonical_SM_files_sha256'].items())
assert len(c['canonical_SM_files_sha256'])==299
assert {str(f.relative_to(base)) for f in (base/'work/lean/SM').glob('*.lean')}==set(c['canonical_SM_files_sha256'])
manifest=load(c['port_manifest']);assert sha(c['port_manifest'])==c['port_manifest_sha256']
assert sha(c['port_installation'])==c['port_installation_sha256']
assert len(manifest['prior_SM_files_sha256'])==294
assert all(sha('work/lean/'+p)==h for p,h in manifest['prior_SM_files_sha256'].items())
for dest,p in c['ports'].items():
 assert (base/dest).read_bytes()==(base/p['candidate']).read_bytes()
 assert sha(dest)==p['installed_module_sha256']==p['candidate_sha256']
 blocks=[]
 for f in p['source_fragments']:
  assert sha(f['source'])==f['source_sha256'];blocks.append((base/f['source']).read_text())
 s=(base/dest).read_text();assert s[s.index('namespace SM'):]== '\n'.join(blocks)
assert sha('work/lean/Supplemental.lean')==c['Supplemental_sha256']
priorfile='work/checks/checkpoint-063-declaration-audit.json';prior=load(priorfile)['statement_hashes']
assert len(prior)==37 and all(a['statement_hashes'][k]==h for k,h in prior.items())
assert sha(c['trace'])==c['trace_sha256']==prep['trace_sha256']
logfile='work/checks/nearfar-canonical-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['additional_examples'];axioms={};types={}
assert len(names)==37 and len(examples)==11
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[x.strip() for x in m[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n
  axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'},n
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
oldtypes=load('work/checks/nearfar-inverse-reviewed-types.json')['types'];assert types==oldtypes
ident='def:nearfar';decl='SM.nearfarData';module='SM.NearFar'
target=next(d for d in a['audit']['declarations'] if d['declaration']==decl)
assert target['module']==module and target['kind']=='definition'
sh=digest(target['semantic_dependencies']);assert sh==a['statement_hashes'][ident]==r['new_statement_hashes'][ident]=='91f29768c7e1ce1bb4f0d7c110e5a9e379d62e50b38064d2373ecb64bea22aa0'
sn={d['declaration'] for d in target['semantic_dependencies']};assert len(sn)==41
required=['SM.nearfarData','SM.IncreasingBoundaryTriple','SM.IncreasingBoundaryTriple.mk','SM.TripleArray','SM.IntervalArray','SM.IntervalComposition','SM.IntervalComposition.mk','SM.IntervalComposition.cut','SM.IntervalComposition.parts','SM.IntervalComposition.part','SM.IntervalComposition.finite','SM.IntervalComposition.fintype','SM.IntervalComposition.nearTriple','SM.IntervalComposition.farTriple','SM.IntervalComposition.nearFarWeight','SM.nearFarTransform','SM.farTransform','SM.nearTransform','SM.boundaryUnitArray','SM.geometricBoundaryArray','SM.BoundaryInterval','SM.BoundaryInterval.mk','SM.boundaryIndex','SM.LabelledTuple','SM.chi','SM.det']
assert set(required)<=sn
semfile='work/checks/nearfar-canonical-semantic-review.json'
semantic={'declaration':decl,'module':module,'statement_sha256':sh,'semantic_dependency_count':41,
 'semantic_declarations':sorted(sn),'required_transparent_definitions_and_constructors':required,
 'semantic_dependency_record_sha256':{d['declaration']:digest(d) for d in target['semantic_dependencies']}}
write(semfile,{'targets':{ident:semantic},'canonical_printed_types':types,'canonical_printed_type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},
 'all_37_prototype_canonical_printed_types_equal':True,'axioms':axioms,'all_37_prior_semantic_hashes_unchanged':True,
 'prior_semantic_audit':priorfile,'prior_semantic_audit_sha256':sha(priorfile),
 'partial_inverse_scope':'The unmapped helper SM.nearFar_has_polynomial_inverse is bound by its exact canonical module closure, printed type and independent consumers, not by an invented full lem:farout semantic hash. Audit064 contains semantic closures for mapped source declarations only.'})
evidence={'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),
 'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),
 'independent_kernel_command':'lake env lean ../checks/nearfar-canonical-review-types.lean','independent_kernel_session':21424,'independent_kernel_exit_code':0,'first_independent_run_passed':True,
 'checked_declarations':names,'declaration_axioms':{n:axioms[n] for n in names},'additional_examples':examples,
 'additional_example_count':11,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
 'all_37_prototype_canonical_printed_types_equal':True,'transparent_predicates_printed':prep['transparent_definitions_printed'],
 'independent_closure_evidence':'work/checks/nearfar-canonical-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/nearfar-canonical-review-closure.json'),
 'canonical_semantic_evidence':semfile,'canonical_semantic_evidence_sha256':sha(semfile),
 'root_result_file':rfile,'root_result_sha256':sha(rfile),
 'successful_build_session':90989,'successful_build_exit_code':0,'successful_build_log':r['log'],'successful_build_log_sha256':sha(r['log']),
 'audit_receipt':r['receipt'],'audit_receipt_sha256':sha(r['receipt']),'declaration_audit':r['audit'],'declaration_audit_sha256':sha(r['audit']),
 'scope_note':'The same 11 substantive external consumers were rerun with canonical imports only: complete triple/interval domains, exact unary term and half factors, actual unit array, inverse base coordinate, every-target uniqueness, explicit coordinate-polynomial evaluation, zero-weight normalization and physical-root geometric array transport.'}
binding={p:sha(p) for p in ['work/reviews/nearfar-prototype.json','work/reviews/triangular-polynomial-inverse-prototype.json','work/checks/nearfar-inverse-reviewed-types.json','work/checks/nearfar-inverse-review-examples.lean']}
for pfile in ['work/reviews/nearfar-prototype.json','work/reviews/triangular-polynomial-inverse-prototype.json']:
 p=load(pfile);assert sha(p['source'])==p['source_sha256']
 for f,h in p['additional_source_sha256'].items():assert sha(f)==h
 for f,h in p['reviewed_files_sha256'].items():assert sha(f)==h
for f,h in prep['external_review_binding'].items():assert sha(f)==h
ctx={'receipt':r['receipt'],'receipt_sha256':sha(r['receipt']),'root_audit_session':90989,'root_audit_exit_code':0,
 'passed':True,'stage_accepted':False,'audited_local_declarations':3804,'mapped_claims':38,'audited_SM_modules':299,
 'audited_project_files':len(receipt['project_sha256']),'all_receipt_project_and_bundle_hashes_checked_at_review':True,
 'all_37_prior_semantic_hashes_unchanged':True,'scope':'Immutable audit064 covers the installed five-module batch while def:nearfar is in review and lem:farout remains pending. No subsequent accepted-map audit is claimed here.'}
portfile='work/reviews/nearfar-port.json'
write(portfile,{'review_schema':'independent-full-source-port-review-v1','id':'nearfar-port','source_ids':[ident],
 'reviewer':'review_relgp_full-independent-20260911','implementer':'root-implementation-20260910','verdict':'faithful','source_claim_accepted':False,
 'parameters_reviewed':True,'definition_equivalence_reviewed':True,'in_theorem_library':True,
 'statement_hashes':{ident:sh},
 'reason':'All five installed canonical namespace bodies equal the exact concatenations of the six independently reviewed frozen body fragments. Import headers replace embedded predecessor bodies. All 294 prior SM modules remain byte-for-byte unchanged, Supplemental appends only SM.TriangularPolynomial, and all 37 previous mapped semantic hashes remain unchanged. Independent canonical kernel 21424 passes all 37 declaration checks and 11 substantive consumers with 48 standard-only axiom traces. Every canonical printed implementation type exactly matches the independent prototype trace. Full source interpretation and transparent definitions were reviewed, and the def:nearfar semantic hash was independently recomputed from immutable audit064. Only that definition is eligible for original source acceptance; the four inverse helper modules establish the reviewed partial assertion and do not complete lem:farout.',
 'ports':c['ports'],'main_declarations':names,'reviewed_files_sha256':c['SM_closure_files_sha256'],
 'import_closure_roots':c['SM_import_roots'],'import_closure_file_count':11,'prior294_unchanged':True,'current_SM_count':299,
 'all_37_prior_semantic_hashes_unchanged':True,'prototype_review_binding':binding,'evidence':evidence,'audit_context':ctx,
 'not_certified':['No full lem:farout acceptance, including factorization, far-only output and restricted-interval assertions.','No extra original claims for helpers, wall law, soft theorem, R theorem or stage completion.']})
pfile='work/reviews/nearfar-prototype.json';p=load(pfile)
math=list(p['mathematical_justification']);math.append({'clause':'Canonical statement and transparent definition closure','assessment':'The exact frozen NearFar and NearFarEquivariance bodies are now canonical. The seven-module import closure and the 41-entry source semantic dependency closure include the actual raw composition constructor, cut/part maps, finite instances, increasing-triple constructor, complete arrays, near/far sampling, half products, Phi/F/G/E and geometric chi formula. All 37 printed types agree with the independently reviewed prototypes. Canonical kernel 21424 independently reruns all 11 substantive consumers and 48 axiom traces. Whole-project audit064 checks the installed files; its original definition semantic hash is independently recomputed. No whole source lemma is inferred from a build or hash. No axiom, G2 restriction, coefficient nontriviality assumption or smaller composition domain has been introduced.'})
d={k:p[k] for k in ['reviewer','implementer','source','source_lines','source_sha256','additional_source_sha256','parameters_reviewed','definition_equivalence_reviewed','pins','independence']}
d.update({'review_schema':'independent-full-source-review-v1','id':ident,'source_id':ident,'source_line':132,'labels':[ident],
 'declaration':decl,'module':module,'verdict':'faithful','source_claim_accepted':True,'in_theorem_library':True,
 'statement_sha256':sh,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reason':p['reason'].split(' Independent kernel')[0]+' The exact canonical port passes independent kernel 21424 with 37 declaration checks, 11 substantive consumers and 48 standard-only axiom traces. All printed types equal their reviewed prototype types; the full source definition and transparent closure match immutable audit064. This definition is faithful and eligible for map acceptance.',
 'mathematical_justification':math,'main_declarations':p['main_declarations'],'reviewed_files_sha256':c['definition_import_closure'],
 'import_closure_roots':[module],'import_closure_file_count':7,'semantic_dependency_count':41,'required_semantic_definitions_checked':required,
 'prototype_review':pfile,'prototype_review_sha256':sha(pfile),'prototype_review_binding':binding,
 'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,'audit_context':ctx,
 'acceptance_scope':{'original_claim':ident,'original_rows_added_if_mapped_accepted':1,'proofs_added_if_mapped_accepted':0,'definitions_added_if_mapped_accepted':1,'current_map_was_not_edited_by_reviewer':True,'helper_original_claim_count':0,'full_farout_accepted':False,'stage_complete':False},
 'not_certified':['No full lem:farout, factorization, far-only output or restricted-interval acceptance.','No original claims for inverse helpers, wall law, soft theorem, R theorem or overall handoff completion.']})
d['independence']+=' The canonical review writes only new check/report evidence; no implementation, source, map or frozen prior review was changed.'
write('work/reviews/def-nearfar.json',d)
pfile='work/reviews/triangular-polynomial-inverse-prototype.json';p=load(pfile)
d={k:p[k] for k in ['reviewer','implementer','source','source_id','source_line','source_lines','source_sha256','additional_source_sha256','parameters_reviewed','definition_equivalence_reviewed','pins','independence','main_declarations','mathematical_justification']}
d.update({'review_schema':'independent-partial-source-review-v1','id':'triangular-polynomial-inverse-canonical-partial','declaration':'SM.nearFar_has_polynomial_inverse','module':'SM.TriangularPolynomial','verdict':'faithful','implemented_scope_verdict':'faithful','source_claim_accepted':False,'in_theorem_library':True,'statement_sha256':None,
 'canonical_printed_type_sha256':sha256(types['SM.nearFar_has_polynomial_inverse'].encode()).hexdigest(),
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'reason':'The installed canonical development faithfully proves only the two-sided polynomial-inverse assertion of lem:farout(i). Exact unary separation identifies the generic triangular transform with the source Phi; strict actual child lengths justify inversion; both full-array inverse identities, every-target uniqueness, explicit inverse coordinate polynomials and their evaluation are proved. Independent kernel 21424 rechecks the exact installed modules and substantive consumers, all 37 printed types match the independently reviewed prototypes, and immutable audit064 passes. The remaining lemma clauses are not certified by this canonical batch, and full lem:farout remains unaccepted.',
 'reviewed_files_sha256':c['SM_closure_files_sha256'],'import_closure_roots':['SM.TriangularPolynomial'],'import_closure_file_count':11,
 'prototype_review':pfile,'prototype_review_sha256':sha(pfile),'prototype_review_binding':binding,
 'port_review':portfile,'port_review_sha256':sha(portfile),'evidence':evidence,'audit_context':ctx,
 'accounting':{'original_claims_accepted':0,'definition_increment':0,'proof_increment':0,'canonical_port_and_current_semantic_audit_pending':False,'full_farout_accepted':False,'stage_complete':False},
 'semantic_hash_scope':'Audit064 records semantic closures for mapped original declarations only. The unmapped inverse helper is bound here by its canonical printed type hash, exact 11-module closure, kernel trace and independent consumer evidence. No full lem:farout statement hash or acceptance is asserted.',
 'unproved_original_clauses_in_this_reviewed_batch':p['unproved_original_clauses'],
 'not_certified':['Full original lem:farout remains incomplete and unaccepted.','No factorization, geometric-output, far-only output or restricted-interval assertion is certified by this canonical batch.','Later external geometry/combinatorics prototypes are outside this report.','No wall law, soft theorem, R theorem or stage completion.']})
d['mathematical_justification'].append({'clause':'Canonical partial boundary','assessment':'This report ports and independently rechecks the already reviewed inverse-only scope. The full source lemma also demands factorization and geometric/restricted-interval consequences; the inverse aggregate does not contain those assertions. None is inferred from polynomial invertibility alone. The exact printed helper type and actual implementation closure provide partial evidence without a new mapped source row or an invented full-lemma semantic hash.'})
d['independence']+=' Only new canonical check/report evidence was written; no source, map, implementation or frozen review changed.'
write('work/reviews/triangular-polynomial-inverse-canonical-partial.json',d)
for p in ['work/reviews/def-nearfar.json',portfile,'work/reviews/triangular-polynomial-inverse-canonical-partial.json']:print(p,sha(p))
print('PASS: 37 exact canonical/prototype types, 11 consumers, 48 standard-only traces, 41 source semantic entries; old 294 modules and 37 hashes unchanged; no map edits.')
