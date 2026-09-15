import sys, fitz
def dump(path, first, last, out=None):
    d=fitz.open(path)
    buf=[]
    for i in range(first-1, min(last, d.page_count)):
        buf.append(f"\n=====[PDF page {i+1} / {d.page_count}]=====\n")
        buf.append(d[i].get_text())
    t="".join(buf)
    if out: open(out,"w").write(t)
    else: sys.stdout.write(t)
if __name__=="__main__":
    p=sys.argv[1]; a=int(sys.argv[2]); b=int(sys.argv[3])
    dump(p,a,b, sys.argv[4] if len(sys.argv)>4 else None)
