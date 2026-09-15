import sys, fitz
src, out_prefix = sys.argv[1], sys.argv[2]
pages = [int(x) for x in sys.argv[3].split(',')]
doc = fitz.open(src)
for p in pages:
    pix = doc[p-1].get_pixmap(matrix=fitz.Matrix(2.4, 2.4))
    fn = f"{out_prefix}-{p:02d}.png"
    pix.save(fn); print("wrote", fn, pix.width, pix.height)
