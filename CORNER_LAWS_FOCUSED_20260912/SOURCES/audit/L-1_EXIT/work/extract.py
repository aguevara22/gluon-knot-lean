import sys, fitz
src, out = sys.argv[1], sys.argv[2]
doc = fitz.open(src)
with open(out, "w") as f:
    f.write("NPAGES %d\n" % doc.page_count)
    for i in range(doc.page_count):
        t = doc[i].get_text()
        f.write("\n\n===== PDFPAGE %d =====\n" % (i+1))
        f.write(t)
print("npages", doc.page_count, "->", out)
