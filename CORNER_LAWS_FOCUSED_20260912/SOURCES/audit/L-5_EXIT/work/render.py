import sys, fitz
pdf, prefix, pages = sys.argv[1], sys.argv[2], sys.argv[3]
scale = float(sys.argv[4]) if len(sys.argv) > 4 else 2.2
doc = fitz.open(pdf)
print("pagecount", doc.page_count)
for p in pages.split(','):
    p = int(p)
    pg = doc[p-1]
    pix = pg.get_pixmap(matrix=fitz.Matrix(scale, scale))
    out = f"{prefix}-{p}.png"
    pix.save(out)
    print(out, pix.width, pix.height)
