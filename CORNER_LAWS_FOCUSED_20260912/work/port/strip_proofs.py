#!/usr/bin/env python3
"""strip_proofs.py <module.lean> <out.txt>: replace every top-level theorem/lemma proof by `sorry`
(definitions kept). The split point is the first ` :=` / ` where` at bracket depth 0 of the block."""
import re, sys
src=open(sys.argv[1]).read().split('\n')
out=[]; i=0; n=len(src); stripped=[]
top=re.compile(r'^(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+)?(theorem|lemma)\s+(\S+)')
PROOF_STARTS = ('by', 'fun ', 'fun(', '·', '|', '⟨', '(', 'calc', 'exact', 'intro', 'refine', 'simp', 'rw ', 'rw[', 'apply', 'have', 'obtain', 'rcases', 'constructor', 'cases', 'induction', 'unfold', 'show', 'sorry', 'omega', 'linarith', 'decide', 'rfl', 'le_antisymm', 'Or.', 'And.', 'Exists.', 'Iff.', 'Eq.', 'Nat.', 'List.', 'Finset.', 'Set.', 'fun', 'let ', 'match', 'nofun', 'nomatch', '.', 'this', 'trivial', 'absurd', 'id ', 'congrArg', 'congr', 'ext', 'norm_num', 'positivity', 'nlinarith', 'field_simp', 'ring', 'push_cast', 'exact_mod_cast', 'simpa', 'aesop', 'subst', 'specialize', 'use', 'left', 'right', 'exfalso', 'contradiction', 'change', 'set ', 'classical', 'first', 'all_goals', 'any_goals', 'repeat', 'try', 'next', 'case', 'focus', 'iterate', 'symm', 'trans', 'calc')
def is_block_end(line):
    # a theorem block ends at the next non-empty column-0 line that is NOT a proof continuation
    # (some units write `theorem foo : T :=` and then `by` / a term at column 0)
    if len(line) == 0 or line[0].isspace(): return False
    stripped = line.lstrip()
    return not any(stripped.startswith(t) for t in PROOF_STARTS)
def split_point(block):
    depth=0; k=0; L=len(block)
    while k<L:
        c=block[k]
        if c in '([{⟨': depth+=1
        elif c in ')]}⟩': depth-=1
        elif depth==0 and block.startswith(' :=',k):
            seg=block[block.rfind('\n',0,k)+1:k]
            if re.match(r'^\s*(let|have|set)\s', seg): pass   # a `let x := …` inside the statement
            else: return k
        elif depth==0 and block.startswith(' where',k) and (k+6==L or not (block[k+6].isalnum() or block[k+6]=='_')): return k
        k+=1
    return -1
while i<n:
    line=src[i]; m=top.match(line)
    if not m: out.append(line); i+=1; continue
    j=i+1
    while j<n and not is_block_end(src[j]) and not (src[j]=='' and j+1<n and is_block_end(src[j+1])): j+=1
    block='\n'.join(src[i:j]); k=split_point(block)
    if k<0: out.extend(src[i:j]); i=j; continue
    header=block[:k].rstrip()
    out.append(header+' := by'); out.append('  sorry'); out.append(''); stripped.append(m.group(2)); i=j
open(sys.argv[2],'w').write('\n'.join(out))
print('stripped', len(stripped), 'theorems')
