#!/usr/bin/env python3
"""Statement byte-identity check for the four FROZEN declarations of the Wave-3 lane:
`G11_ConfigSw` (whole structure block), `G11_core_sw_statement` (whole def), `G11_core_sw` (statement up to
`:=`), `esc_switch_riii_of_chain` (whole theorem incl. body).  Also checks that the frozen
`namespace G11_ConfigSw … end G11_ConfigSw` block of the draft (comp, xs, D₀sw, D₀sw_componentCount, vmp…vqp,
σ, σD) appears verbatim in the skeleton, and that the imports are the draft's plus `import SM.BigonDeletion`.
Usage: check_W3_identity.py Port_GenericTransportSw_draft.lean Skeleton_W3.lean"""
import re, sys
A = open(sys.argv[1], encoding='utf-8').read()
B = open(sys.argv[2], encoding='utf-8').read()
ok = True
def block(text, start_pat, end_pat):
    i = text.index(start_pat)
    j = text.index(end_pat, i) + len(end_pat)
    return text[i:j]
def check(name, a):
    global ok
    n = B.count(a)
    print(f"{name}: {'IDENTICAL' if n == 1 else ('MISSING' if n == 0 else f'AMBIGUOUS x{n}')}  ({len(a)} bytes)")
    ok = ok and n == 1
# 1. structure G11_ConfigSw (docstring + structure, up to the trans_sw field)
check("structure G11_ConfigSw", block(A, "/-- **A triangle configuration with one switched local crossing**",
      "(if sw = 2 then -crossingSign X p q else crossingSign X p q)\n"))
# 2. the frozen namespace block
check("namespace G11_ConfigSw block", block(A, "namespace G11_ConfigSw\n\nvariable {k : ℕ} [NeZero k] (C : G11_ConfigSw k)\n\ndef comp",
      "end G11_ConfigSw\n"))
# 3. G11_core_sw_statement (docstring + def)
check("def G11_core_sw_statement", block(A, "/-- **G11 core on the switched diagram**",
      "C.D₀sw.VisitBetween (C.σD u) (C.σD v) (C.σD w))\n"))
# 4. G11_core_sw statement (docstring + statement up to ':= by')
check("theorem G11_core_sw (statement)", block(A, "/-- **Leaf (Wave 3, ≈ 4.5–6.5k lines).** -/",
      "theorem G11_core_sw {k : ℕ} [NeZero k] (C : G11_ConfigSw k) : G11_core_sw_statement C := by\n"))
# 5. esc_switch_riii_of_chain (docstring + theorem + body)
check("theorem esc_switch_riii_of_chain", block(A, "/-- Row 177 (4) `esc_switch_riii` from the chain",
      "exact CV.gausscode_polynomial M₁ (D_L.switch x_L) hc1 hcL hrec.some\n"))
# 6. imports
ia = [l for l in A.split('\n') if l.startswith('import ')]
ib = [l for l in B.split('\n') if l.startswith('import ')]
imp_ok = ib == ia + ['import SM.BigonDeletion']
print(f"imports = draft's + SM.BigonDeletion: {imp_ok}")
ok = ok and imp_ok
# 7. the leaf's body is no longer `sorry` (it is assembled) — informational
i = B.index("theorem G11_core_sw {k : ℕ}")
body = B[i:i+400]
print("G11_core_sw body starts with sorry:", "\n  sorry" in body[:120])
sys.exit(0 if ok else 1)
