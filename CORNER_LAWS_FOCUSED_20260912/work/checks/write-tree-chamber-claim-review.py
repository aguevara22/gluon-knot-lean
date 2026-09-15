from pathlib import Path
from hashlib import sha256
import json,re,datetime
base=Path(__file__).resolve().parents[2]
def load(p):return json.loads((base/p).read_text())
def sha(p):return sha256((base/p).read_bytes()).hexdigest()
def write(p,d):(base/p).write_text(json.dumps(d,indent=2)+'\n')
c=load('work/checks/tree-chamber-claim-review-closure.json');old=load('work/reviews/tree-chamber-prototype.json')
root=load('work/checks/TreeChamberClaim-prototype-result.json')
assert root['kernel_session']==44816 and root['exit_code']==0
assert all(sha(p)==h for p,h in root['files_sha256'].items())
assert all(sha(p)==h for p,h in c['frozen_body_sha256'].items())
assert all(sha(p)==h for p,h in c['SM_closure_files_sha256'].items())
assert sha(c['trace'])==c['trace_sha256'] and sha(c['examples_file'])==c['examples_sha256']
logfile='work/checks/tree-chamber-claim-review-types.log';s=(base/logfile).read_text()
assert not re.search(r'error[:(]',s) and 'sorryAx' not in s
names=c['checked_declarations'];examples=c['examples'];axioms={};types={}
assert len(names)==29 and len(examples)==4
for n in names+examples:
 m=re.search("'"+re.escape(n)+r"' depends on axioms:\s*\[([^]]*)\]",s)
 if m:axioms[n]=[x.strip() for x in m[1].split(',') if x.strip()]
 else:
  assert "'"+n+"' does not depend on any axioms" in s,n
  axioms[n]=[]
 assert set(axioms[n])<={'propext','Classical.choice','Quot.sound'}
for n in names:
 m=re.search(r'^'+re.escape(n)+r'(?:\.\{[^}]+\})?(?=\s)',s,re.M);assert m,n
 i=m.start();j=s.index("'"+n+"'",i);types[n]=s[i:j].strip()
previous=load('work/checks/tree-laws-reviewed-types.json')
for n in names[:-2]:assert previous['types'][n]==types[n],n
typefile='work/checks/tree-chamber-claim-reviewed-types.json'
write(typefile,{'types':types,'type_sha256':{n:sha256(t.encode()).hexdigest() for n,t in types.items()},'axioms':axioms,'all_27_predecessor_types_unchanged':True})
source='reference/SM/sm-2-amplitude.tex';additional='reference/SM/sm-1-polygons.tex'
assert sha(source)==c['source_sha256']
review={k:old[k] for k in ['reviewer','implementer','pins','independence','accounting']}
review.update({'review_schema':'independent-full-source-prototype-review-v1','id':'tree-chamber-claim-prototype','source_id':'prop:A-chamber',
 'source':source,'source_lines':'120-128; source section G1-only domain3-6; rooted convention10-15; sm-1-polygons.tex33-38 and55-60',
 'source_sha256':sha(source),'additional_source_sha256':{additional:sha(additional)},
 'verdict':'faithful','implemented_scope_verdict':'faithful','parameters_reviewed':True,'definition_equivalence_reviewed':True,
 'source_claim_accepted':False,'statement_sha256':None,'in_theorem_library':False,
 'prototype_file':'work/checks/TreeChamberClaim.prototype.lean','prototype_sha256':sha('work/checks/TreeChamberClaim.prototype.lean'),
 'main_declarations':['SM.TreeDataEqual','SM.A_chamber'],
 'reason':'Faithful complete rooted interpretation of prop:A-chamber. The transparent TreeDataEqual predicate contains both actual composition weights, every open interval sum and the actual rooted coefficient. A_chamber proves equality under G1 and equal chirotopes, constancy on genuine labelled connected components, the coherent physical-root transport over actual cyclic-quotient chambers, and the actual G1-path clause with its printed constant-chirotope premise. This follows the explicit source permission to use labelled representatives and the rule that a root is part of the data and shifts with the tuple. Independent kernel25757 passes29 declarations and4 substantive consumers, including transport of all quantities over the quotient chamber. Original acceptance remains pending the exact canonical port, semantic hash and whole-project audit.',
 'mathematical_justification':[
  {'clause':'All named quantities and G1 domain','assessment':'TreeDataEqual is a transparent conjunction quantifying over every actual BoundaryInterval and raw IntervalComposition, comparing ordinaryWeight and rootWeight, then every openTreeSum and the treeCoefficient at the chosen root. A_chamber first quantifies over arbitrary labelled tuples with G1 proofs and equality of all actual chi entries. The already checked sign/weight congruence theorems give equal weight functions; substituting these functions into the defined recursion gives equal open and rooted sums. No G2, regularity, nonzero-control oracle or unproved constancy is added. The independent complete_G1_quantities consumer extracts every source quantity on this precise domain.'},
  {'clause':'Actual connected-component chambers','assessment':'The labelled chamber in the source formalization remark is the actual connected component of GenericTuple, not the locus of a fixed sign pattern used as a replacement definition. continuous_generic_chi maps this space continuously to discrete SignType. Preconnectedness of a connected component forces each chi entry to be constant, yielding the full data equality. The independent actual_connected_component consumer begins directly with Q in connectedComponent P and obtains TreeDataEqual, verifying the domain is exactly the topological component.'},
  {'clause':'Rooted interpretation and quotient chamber','assessment':'The source states that a polygon has no distinguished edge and a needed root is part of the construction data (sm-1 lines33-38), explicitly permits labelled tuples with shift-equivariance (lines55-60), and requires the simultaneous rule (P,g)->(shift a P,g-a) in def:root. Consequently constancy of A_g on a chamber uses the same physical-root choice under representative changes; it does not assert that selecting fixed label zero afresh on every representative defines an unrooted invariant. The proved chamber preimage formula expresses the actual quotient component as a union of shifted labelled components. A_chamber exposes one a with Q in the actual labelled component of genericShift a P and transports every root g coherently to g-a. This is the source permitted representative interpretation, strengthened by explicit quotient transport, without presuming independence of different physical roots.'},
  {'clause':'All quantities also transport under the quotient reading','assessment':'The independent all_quantities_under_quotient_transport consumer uses the aggregate to obtain the same a and actual component. Labelled TreeDataEqual compares genericShift a P and Q at root g-a. Reversing these equalities and applying the independently reviewed gate/open shift identities compares both actual weights and every open sum of Q at g-a with P at g. The aggregate already provides the same equality for A_g. This verifies that no quantity from the first clause is lost when interpreting the source through the quotient, although the printed in-particular chamber clause itself names only A_g.'},
  {'clause':'Actual G1 paths and their printed premise','assessment':'The final clause uses an actual Path in the subtype of G1 labelled tuples, retaining all time parameters in unitInterval and the stated equality of chirotopes at every pair of times. It applies the G1 chirotope theorem to these actual path values to get every named quantity. The independent actual_G1_path consumer checks this full domain. It does not replace the path by a finite list, assume G2 along it, or drop the source constant-chirotope premise.'},
  {'clause':'Independent proof and scope binding','assessment':'The exact frozen helper and new aggregate bodies were independently read and compiled over canonical predecessors. All27 predecessor printed types equal the previous full tree review, and the two new types expose the intended complete predicate and aggregate. The independent first run25757 checks29 declarations and four source consumers with standard axioms only. The helper/prototype and source hashes, successful root44816 receipt, and17-module canonical import closure are bound below. No previous review or implementation was edited.'}],
 'reviewed_files_sha256':{**c['SM_closure_files_sha256'],**c['frozen_body_sha256'],**root['files_sha256']},
 'import_closure_roots':['SM.Gates','SM.FiniteCompositions','SM.CyclicChambers'],'import_closure_file_count':17,
 'inherited_review_binding':{p:sha(p) for p in ['work/reviews/tree-coefficient-prototype.json','work/reviews/plane-tree-prototype.json','work/reviews/tree-chamber-prototype.json','work/reviews/def-root.json','work/reviews/def-gates.json']},
 'evidence':{'independent_trace_source':c['trace'],'independent_trace_source_sha256':sha(c['trace']),
  'independent_trace_log':logfile,'independent_trace_log_sha256':sha(logfile),'independent_kernel_command':'lake env lean ../checks/tree-chamber-claim-review-types.lean',
  'independent_kernel_session':25757,'independent_kernel_exit_code':0,'first_independent_run_passed':True,
  'checked_declarations':names,'declaration_axioms':{n:axioms[n] for n in names},
  'additional_examples':examples,'additional_example_count':4,'additional_examples_passed':True,'additional_example_axioms':{n:axioms[n] for n in examples},
  'transparent_predicates_printed':['SM.TreeDataEqual'],'all_27_predecessor_types_unchanged':True,
  'printed_types':typefile,'printed_types_sha256':sha(typefile),
  'independent_closure_evidence':'work/checks/tree-chamber-claim-review-closure.json','independent_closure_evidence_sha256':sha('work/checks/tree-chamber-claim-review-closure.json'),
  'root_result_file':'work/checks/TreeChamberClaim-prototype-result.json','root_result_sha256':sha('work/checks/TreeChamberClaim-prototype-result.json'),
  'successful_root_kernel_session':44816,'successful_root_kernel_exit_code':0,'root_files_sha256':root['files_sha256']},
 'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),
 'not_certified':['No canonical or original source acceptance before exact port and current semantic audit.','No equality between arbitrary different physical roots is claimed.','No wall law, soft theorem, R theorem or overall stage completion.']})
write('work/reviews/tree-chamber-claim-prototype.json',review)
print('Full prop:A-chamber external review faithful; SHA',sha('work/reviews/tree-chamber-claim-prototype.json'))
