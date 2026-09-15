import sys, fitz
src, out = sys.argv[1], sys.argv[2]
d = fitz.open(src)
with open(out, "w") as f:
    for i, p in enumerate(d):
        f.write("\n===== PDFPAGE %d =====\n" % (i+1))
        f.write(p.get_text())
print(out, d.page_count, "pages")
