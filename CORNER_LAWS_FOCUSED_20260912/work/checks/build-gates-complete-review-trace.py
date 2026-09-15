from pathlib import Path
import re,json,hashlib
base=Path(__file__).resolve().parents[2];c=base/'work/checks'
p=(c/'GatesEquivariance.prototype.lean').read_text().split('\n#print axioms SM.IntervalComposition.ordinaryWeight_shift')[0]
f=(c/'FiniteCompositions.body.lean').read_text()
old=(c/'finite-and-gates-review-types.lean').read_text();names=re.findall(r'^#check (\S+)',old,re.M)
names+=['SM.ordinaryGate_congr','SM.rootGate_congr','SM.IntervalComposition.nearSign_shift','SM.IntervalComposition.farSign_shift','SM.IntervalComposition.ordinaryWeight_eq_of_signs','SM.IntervalComposition.rootWeight_eq_of_signs','SM.IntervalComposition.ordinaryWeight_shift','SM.IntervalComposition.rootWeight_shift','SM.gatesData_shift']
t=p+'\n'+f+'\nset_option pp.fullNames true\nset_option pp.universes false\n'+'\n'.join('#check '+n+'\n#print axioms '+n for n in names)+'\n'
t+='\n'.join('#print '+n for n in ['SM.IntervalComposition','SM.signTheta','SM.IntervalComposition.nearSign','SM.IntervalComposition.farSign','SM.IntervalComposition.ordinaryWeight','SM.IntervalComposition.rootWeight','SM.gatesData'])+'\n'
for file,ns in [('finite-and-gates-review-examples.lean','FiniteAndGatesIndependentReview'),('gates-equivariance-review-examples.lean','GatesEquivarianceIndependentReview')]:
 e=(c/file).read_text();t+='\n'+e+'\n'+'\n'.join('#print axioms '+ns+'.'+n for n in re.findall(r'^theorem (\w+)',e,re.M))+'\n'
(c/'gates-complete-review-types.lean').write_text(t)
print('Prepared complete exact-body trace;31 declarations and14 consumer checks')
