#!/usr/bin/env python3
"""Assemble W3_A1_Assembled.lean = W3_A1_BC.lean with the DE block (W3_A1_DE.lean `section W3DECopy … end W3DECopy`,
minus the 8 aliases and 11 black boxes that duplicate BC's proved copies) spliced after `M₁sw_componentCount`, and the
two DE connectors (`w3a_riii_param`, `w3a_exists_Ψ₁`) closed by `exact π.w3de_…`."""
import re, sys
BC = open('W3_A1_BC.lean', encoding='utf-8').read().split('\n')
DE = open('W3_A1_DE.lean', encoding='utf-8').read().split('\n')
def find(lines, pat, start=0):
    for i in range(start, len(lines)):
        if lines[i].startswith(pat): return i
    raise SystemExit(f"not found: {pat}")
# --- BC split point: after `theorem M₁sw_componentCount`
n_split = find(BC, 'theorem M₁sw_componentCount') + 1        # index after that line
# --- DE block: from the `/-! ### W3-A1-DE` header to `end W3DECopy`
de_hdr = find(DE, '/-! ### W3-A1-DE')
de_sec = find(DE, 'section W3DECopy', de_hdr)
de_alias_hdr = find(DE, '/-! #### Aliases', de_sec)
de_copy_hdr = find(DE, '/-! #### The copy proper', de_alias_hdr)
de_end = find(DE, 'end W3DECopy', de_copy_hdr) + 1
# sanity: between de_alias_hdr and de_copy_hdr are exactly the 8 aliases + 11 black boxes
dropped = DE[de_alias_hdr:de_copy_hdr]
alias_names = [m.group(1) for l in dropped for m in [re.match(r'^theorem (\S+)', l)] if m]
assert len(alias_names) == 19, alias_names
print("dropped duplicate declarations (19):", ' '.join(alias_names))
assert sum(l.strip() == 'sorry' for l in dropped) == 11
head = DE[de_hdr:de_alias_hdr]
head = [l.replace("unproved black boxes (accepted names, statements verbatim; the assembler de-duplicates). -/",
                  "the BC prover's PROVED copies above (`section W3A1Copy`); the 8 aliases and 11 black boxes of\n"
                  "`W3_A1_DE.lean` are dropped here (assembled 2026-09-15, `W3_A1_ASSEMBLY_REPORT.md`). -/") for l in head]
block = head + DE[de_copy_hdr:de_end]
# --- BC tail with the two connectors closed
tail = BC[n_split:]
def close(tail, thm, body):
    i = find(tail, f'theorem {thm}')
    j = i
    while tail[j].strip() != 'sorry': j += 1
    assert j - i < 40, (thm, j - i)
    tail[j] = body
    print(f"closed {thm}: tail line {j} -> {body.strip()[:60]}…")
close(tail, 'w3a_riii_param', '  exact π.w3de_riii_param f₀ hf₀ f₁ hf₁ h₀ h₁ Rmp Rmq Rpq hmp₀ hmq₀ hpq₀ hmp₁ hmq₁ hpq₁ htrans')
close(tail, 'w3a_exists_Ψ₁', '  exact π.w3de_exists_Ψ₁ Ψ₀ h₀ hmp hpm hmq hqm hpq hqp')
out = BC[:n_split] + [''] + block + [''] + tail
open('W3_A1_Assembled.lean', 'w', encoding='utf-8').write('\n'.join(out))
print(f"BC head {n_split} + DE block {len(block)} + BC tail {len(tail)} = {len(out)} lines")
print("DE block = DE lines", de_hdr+1, "-", de_alias_hdr, "and", de_copy_hdr+1, "-", de_end, "; spliced after BC line", n_split)
