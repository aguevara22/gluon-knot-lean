#!/usr/bin/env python3
"""check_comment_only.py — assert that patches (or a before/after pair) change ONLY comment text in Lean files.

A Lean line is classified by a comment scanner (nested `/- … -/` blocks incl. `/-- … -/` and `/-! … -/`
docstrings, `--` line comments, string literals respected):
  comment : every non-blank character of the line lies inside a comment (or its delimiters)
  code    : the line has non-comment, non-blank characters (its non-comment text is the "code part")
  blank   : whitespace only, outside any comment
Two versions of a file pass iff the sequence of (kind, code part) over their non-comment lines
(kinds `code` and `blank`) is identical — i.e. no code line was changed, added, removed or reordered and
no blank line was inserted outside a comment. Docstring/comment lines may change freely.

Usage
  python3 check_comment_only.py --pair BEFORE AFTER            # two files, or two directory trees
  python3 check_comment_only.py --root PKG_ROOT --patches P.patch [Q.patch ...]
      copies the files named in the patches from PKG_ROOT to a temp dir, applies the patches there in
      the given order with `patch -p0`, and checks each touched .lean file before/after (cumulative);
      non-.lean files are listed as "not checked (not Lean)".
Exit status 0 = every checked Lean file is comment-only; 1 = a violation or a patch failure.
"""
import argparse, difflib, os, re, shutil, subprocess, sys, tempfile

def comment_mask(text):
    n = len(text); mask = [False] * n; i = 0; depth = 0; in_str = False
    while i < n:
        c = text[i]
        if depth > 0:
            mask[i] = True
            if text.startswith('/-', i):
                depth += 1; mask[i + 1] = True; i += 2; continue
            if text.startswith('-/', i):
                depth -= 1; mask[i + 1] = True; i += 2; continue
            i += 1; continue
        if in_str:
            if c == '\\':
                i += 2; continue
            if c == '"':
                in_str = False
            i += 1; continue
        if c == '"':
            in_str = True; i += 1; continue
        if text.startswith('/-', i):
            depth = 1; mask[i] = True; mask[i + 1] = True; i += 2; continue
        if text.startswith('--', i):
            j = text.find('\n', i)
            if j < 0: j = n
            for k in range(i, j): mask[k] = True
            i = j; continue
        i += 1
    return mask

def classify(text):
    """-> list of (kind, code_part_rstripped, raw_line) per line."""
    mask = comment_mask(text)
    out = []; pos = 0
    for raw in text.split('\n'):
        L = len(raw)
        code = ''.join(ch for k, ch in enumerate(raw) if not mask[pos + k])
        has_comment = any(mask[pos:pos + L])
        if code.strip():
            kind = 'code'
        elif has_comment:
            kind = 'comment'
        else:
            kind = 'blank'
        out.append((kind, code.rstrip(), raw))
        pos += L + 1
    return out

def check_pair(before_text, after_text):
    """-> (ok, message, changed_line_ranges_after)"""
    A = classify(before_text); B = classify(after_text)
    seqA = [(k, c) for k, c, _ in A if k != 'comment']
    seqB = [(k, c) for k, c, _ in B if k != 'comment']
    problems = []
    if seqA != seqB:
        sm = difflib.SequenceMatcher(a=seqA, b=seqB, autojunk=False)
        for tag, i1, i2, j1, j2 in sm.get_opcodes():
            if tag != 'equal':
                problems.append(f'  non-comment content differs: before[{i1}:{i2}]={seqA[i1:i2][:3]} after[{j1}:{j2}]={seqB[j1:j2][:3]}')
    # report the changed raw lines (after side) and make sure each is a comment line or a code line with the same code part
    rawA = [r for _, _, r in A]; rawB = [r for _, _, r in B]
    sm = difflib.SequenceMatcher(a=rawA, b=rawB, autojunk=False)
    ranges = []
    for tag, i1, i2, j1, j2 in sm.get_opcodes():
        if tag == 'equal':
            continue
        ranges.append((tag, i1 + 1, i2, j1 + 1, j2))
        for idx in range(i1, i2):
            if A[idx][0] == 'code' and not any(B[j][0] == 'code' and B[j][1] == A[idx][1] for j in range(j1, j2)):
                problems.append(f'  removed/altered code line {idx+1} (before): {rawA[idx][:100]!r}')
        for idx in range(j1, j2):
            if B[idx][0] == 'code' and not any(A[i][0] == 'code' and A[i][1] == B[idx][1] for i in range(i1, i2)):
                problems.append(f'  added/altered code line {idx+1} (after): {rawB[idx][:100]!r}')
            if B[idx][0] == 'blank' and not any(A[i][0] == 'blank' for i in range(i1, i2)):
                problems.append(f'  blank line inserted outside a comment at {idx+1} (after)')
    return (not problems), problems, ranges

def fmt_ranges(ranges):
    parts = []
    for tag, a1, a2, b1, b2 in ranges:
        parts.append(f'{tag} before {a1}-{a2} -> after {b1}-{b2}')
    return '; '.join(parts) if parts else 'no line changes'

def touched_paths(patch_text):
    paths = []
    for ln in patch_text.splitlines():
        if ln.startswith('+++ '):
            p = ln[4:].split('\t')[0].strip()
            if p not in paths: paths.append(p)
    return paths

def run_pair(before, after):
    ok_all = True
    if os.path.isdir(before):
        files = []
        for dp, _, fns in os.walk(after):
            for fn in fns:
                if fn.endswith('.lean'):
                    rel = os.path.relpath(os.path.join(dp, fn), after)
                    files.append(rel)
        for rel in sorted(files):
            fa = os.path.join(before, rel); fb = os.path.join(after, rel)
            if not os.path.exists(fa):
                print(f'FAIL {rel}: new file'); ok_all = False; continue
            ta = open(fa, encoding='utf-8').read(); tb = open(fb, encoding='utf-8').read()
            if ta == tb: continue
            ok, probs, ranges = check_pair(ta, tb)
            print(('OK  ' if ok else 'FAIL') + f' {rel}: {fmt_ranges(ranges)}')
            for p in probs: print(p)
            ok_all &= ok
    else:
        ta = open(before, encoding='utf-8').read(); tb = open(after, encoding='utf-8').read()
        ok, probs, ranges = check_pair(ta, tb)
        print(('OK  ' if ok else 'FAIL') + f' {after}: {fmt_ranges(ranges)}')
        for p in probs: print(p)
        ok_all = ok
    return ok_all

def run_patches(root, patches):
    ok_all = True
    tmp = tempfile.mkdtemp(prefix='docdebt-check-')
    try:
        for patch in patches:
            ptext = open(patch, encoding='utf-8').read()
            paths = touched_paths(ptext)
            befores = {}
            for rel in paths:
                dst = os.path.join(tmp, rel)
                if not os.path.exists(dst):
                    os.makedirs(os.path.dirname(dst), exist_ok=True)
                    shutil.copyfile(os.path.join(root, rel), dst)
                befores[rel] = open(dst, encoding='utf-8').read()
            r = subprocess.run(['patch', '-p0', '--no-backup-if-mismatch', '-i', os.path.abspath(patch)], cwd=tmp,
                               stdout=subprocess.PIPE, stderr=subprocess.STDOUT, text=True)
            if r.returncode != 0:
                print(f'FAIL {os.path.basename(patch)}: patch did not apply cleanly\n{r.stdout}'); ok_all = False; continue
            print(f'== {os.path.basename(patch)} ({len(paths)} file(s))')
            for rel in paths:
                after = open(os.path.join(tmp, rel), encoding='utf-8').read()
                if not rel.endswith('.lean'):
                    print(f'  --  {rel}: not checked (not Lean; comment-only rule does not apply)'); continue
                ok, probs, ranges = check_pair(befores[rel], after)
                print(('  OK  ' if ok else '  FAIL') + f' {rel}: {fmt_ranges(ranges)}')
                for p in probs: print('  ' + p)
                ok_all &= ok
    finally:
        shutil.rmtree(tmp, ignore_errors=True)
    return ok_all

def main():
    ap = argparse.ArgumentParser(description=__doc__, formatter_class=argparse.RawDescriptionHelpFormatter)
    ap.add_argument('--pair', nargs=2, metavar=('BEFORE', 'AFTER'))
    ap.add_argument('--root', help='package root the patches apply to (with -p0)')
    ap.add_argument('--patches', nargs='+')
    a = ap.parse_args()
    if a.pair:
        ok = run_pair(*a.pair)
    elif a.root and a.patches:
        ok = run_patches(a.root, a.patches)
    else:
        ap.error('give --pair BEFORE AFTER, or --root ROOT --patches P...')
    print('RESULT:', 'comment-only' if ok else 'VIOLATION')
    sys.exit(0 if ok else 1)

if __name__ == '__main__':
    main()
