import sys, fitz
src, page, out = sys.argv[1], int(sys.argv[2]), sys.argv[3]
clip = None
if len(sys.argv) > 4:
    x0,y0,x1,y1 = [float(v) for v in sys.argv[4].split(",")]
    clip = fitz.Rect(x0,y0,x1,y1)
d = fitz.open(src)
p = d[page-1]
print("page rect", p.rect)
pix = p.get_pixmap(matrix=fitz.Matrix(3,3), clip=clip)
pix.save(out)
print(out, pix.width, pix.height)
