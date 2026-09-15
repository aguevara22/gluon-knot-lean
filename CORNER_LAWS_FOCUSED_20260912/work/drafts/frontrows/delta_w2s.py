#!/usr/bin/env python3
"""Assemble work/drafts/frontrows/FrontRows_W2S_Delta.lean (certificate rows lane, sweep delta: the leaf `represent`
and row 76 ng:commutation) from W3S_Merged.lean + Skeleton_W2.lean.  Rerunnable; every source range is anchored
(first/last line text asserted) so it fails loudly on a different input.  Also writes the axiom probe copy
/tmp/w2sdelta/W2S_ax.lean.  Writes nothing under work/lean."""
import os, sys
ROOT = "/workspace/repos/lean/lean_repo/LEAN_HANDOFF_20260912_RESUME/CORNER_LAWS_FOCUSED_20260912"
FR = f"{ROOT}/work/drafts/frontrows"
MERGED = f"{FR}/W3S_Merged.lean"
SKEL = f"{FR}/Skeleton_W2.lean"
OUT = f"{FR}/FrontRows_W2S_Delta.lean"
PROBE = "/tmp/w2sdelta/W2S_ax.lean"

M = open(MERGED, encoding="utf-8").read().split("\n")
S = open(SKEL, encoding="utf-8").read().split("\n")
assert len(M) == 23405 and M[-1] == "", len(M)   # 23,404 lines + trailing newline
assert len(S) == 14892 and S[-1] == "", len(S)

def m(i): return M[i - 1]          # 1-based
def s(i): return S[i - 1]
def rng(L, a, b): return L[a - 1:b]   # inclusive 1-based

def anchor(desc, cond):
    if not cond:
        sys.exit(f"ANCHOR FAILED: {desc}")

# --- anchors on the merged file (line numbers from W3S_MERGE_REPORT.md §3, re-checked here) ---
anchor("sweep block header start 14568", m(14568).startswith("/-! ### U8R sweep — the leaf skeleton for `U8R.SweepStatement`"))
anchor("14567 = end U8RInfra + blank before", m(14566) == "end U8RInfra" and m(14567) == "")
anchor("namespace U8R 14591", m(14591) == "namespace U8R")
anchor("open 14593", m(14593) == "open SM.FrontWord SM.FrontWord.Letter SM.FrontRealize Equiv")
anchor("noncomputable section 14595", m(14595) == "noncomputable section")
anchor("end Assembly 23074", m(23074) == "end Assembly")
anchor("end (noncomputable) 23076", m(23076) == "end")
anchor("end U8R 23078", m(23078) == "end U8R" and m(23079) == "")
anchor("represent docstring 23080", m(23080).startswith("/-- LEAF = THE REPRESENTATION THEOREM"))
anchor("theorem represent 23083", m(23083).startswith("theorem represent (F : SmoothFront) : ∃ W : OWord,"))
anchor("represent body 23086", m(23086) == "  U8R.represent_of_sweepStatement F (U8R.sweep_proof F)")
anchor("end Leaves 23088", m(23087) == "" and m(23088) == "end Leaves")
# the two false leaves (with docstrings and the blank line after each)
anchor("blank 16708", m(16708) == "")
anchor("dirBit_of_cont_before docstring 16709", m(16709).startswith("/-- LEAF (S1): a continuation carries the bit of its entry"))
anchor("dirBit_of_cont_before 16712-16713", m(16712).startswith("theorem dirBit_of_cont_before") and m(16713).endswith(":= sorry") and m(16714) == "")
anchor("dirBit_of_cont_after docstring 16715", m(16715).startswith("/-- LEAF (S1): the same after the x-value"))
anchor("dirBit_of_cont_after 16716-16717", m(16716).startswith("theorem dirBit_of_cont_after") and m(16717).endswith(":= sorry") and m(16718) == "")
anchor("next leaf 16719", m(16719).startswith("/-- LEAF (S1): the one-sided limits of the cut itself"))
# row 76
anchor("ng_commutation docstring 23254", m(23254) == "/-- **ng:commutation** (row 76), assembled. -/")
anchor("theorem ng_commutation 23255", m(23255) == "theorem ng_commutation : NgCommutationClauses where")
anchor("ng_commutation last field 23268", m(23268) == "  represent := represent" and m(23269) == "")
anchor("row 77 follows 23270", m(23270).startswith("/-- **ng:front-I** (row 77)"))
# --- anchors on the skeleton ---
anchor("skeleton NgCommutationClauses 57", s(57) == "structure NgCommutationClauses : Prop where")
anchor("skeleton NgCommutationClauses end 72-73", s(72).endswith("Nonempty (RecordIso S.record (realize W).diagram.record)") and s(73) == "" and s(74).startswith("structure NgFrontIClauses"))
# sanity: the sweep block region is exactly the two-hunk insertion (W3S_MERGE_REPORT §3)
anchor("merged 1-14567 == skeleton 1-14567", M[:14567] == S[:14567])
anchor("merged 23087- == skeleton 14574-", M[23086:] == S[14573:])

HEADER = """/-! # Front certificate rows — sweep delta: the leaf `represent` and row 76 ng:commutation

Certificate rows lane, sweep delta (decision D-FR1: the lane is ported incrementally as fully proved modules).
This module imports `SM.FrontRowsW2` (the wave-2 clean subset: rows 81 ng:circle and 82 ng:cusp-skein with the
shared infrastructure U1-U4, U7, U8D and the U8R record layer) and adds, in this order:
* **the U8R sweep block** (`SM.FrontRows.U8R`, sections `SweepDefs`, `SweepLeaves`, `SlotMap`, `Traversal`,
  `Assembly`): the vertical sweep of the printed proof (sm-3:1938-1947) — the fibre lists and the cuts (S1), the
  cusp and crossing local models (S2, S3), the event word and its run through the hybrid cuts (S4), the slot map
  `Φ` (S5), the traversal `slotAt` and the circle bijection (S6), the record isomorphism `recordIso` and the
  theorem `sweep_proof : SweepStatement F`.  Taken verbatim from the sweep-lane merge
  `work/drafts/frontrows/W3S_Merged.lean` (W3S_MERGE_REPORT.md), minus the two leaves `dirBit_of_cont_before` /
  `dirBit_of_cont_after`, which are false as stated and consumed by nothing (their corrected forms
  `s1b_dirBit_of_cont_before` / `s1b_dirBit_of_cont_after`, with the extra hypothesis `¬ F.IsCusp q`, are proved here).
* **the leaf `SM.FrontRows.represent`** (the representation theorem of row 76), proved from `U8R.sweep_proof`
  through the reduction `U8R.represent_of_sweepStatement` of `SM.FrontRowsW2`.
* **row 76**: the statement `SM.NgCommutationClauses` (verbatim from `Skeleton_W2.lean` / `Statements_FINAL.lean`)
  and `SM.ng_commutation : NgCommutationClauses`, assembled from `comm_counts`, `P_comm`, `deform_downCount`,
  `deform_writhe`, `deform_P` (all in `SM.FrontRowsW2`) and `represent`.

Every declaration in this module is fully proved: the axioms of `SM.ng_commutation` are
`[propext, Classical.choice, Quot.sound, SM.lp_lm]` (`lp_lm` is the accepted literature interface reached through
`P`); those of `SM.FrontRows.represent`, `SM.FrontRows.U8R.sweep_proof` and `SM.FrontRows.U8R.recordIso` are
`[propext, Classical.choice, Quot.sound]`.  Provenance and line map: `work/drafts/frontrows/W2S_DELTA_REPORT.md`.

Not in this module (the final delta module imports this one and adds exactly these): the row statements
`NgFrontIClauses`, `NgFrontIIClauses`, `NgFrontIIIClauses`, `NgDeletionsClauses`, `NgLocalFrontBoundClauses`; the
L-geo leaves `typeIII_site`, `typeII_move`, `typeI_move`, `crossedCusp_move` and their consumers `P_typeIII`,
`P_typeII`, `P_typeI`, `P_crossedCusp`; the rows `ng_front_I`, `ng_front_II`, `ng_front_III`, `ng_deletions`
(77-80), `certificate_laws`, `word_bound`, `ng_local_front_bound` (83).

Checked with `cd work/lean && lake env lean`. -/"""

NOTE = ["/-! `dirBit_of_cont_before` / `dirBit_of_cont_after` removed: false as stated (W3S_MERGE_REPORT.md §4; consumed by",
        "nothing), replaced by the proved `s1b_dirBit_of_cont_before` / `s1b_dirBit_of_cont_after` (extra hypothesis `¬ F.IsCusp q`). -/",
        ""]

out = []
out += ["import SM.FrontRowsW2", ""]
out += HEADER.split("\n")
out += ["", "namespace SM", "", "open SM.FrontWord SM.Link", "open scoped ContDiff", "",
        "namespace FrontRows", "", "section Leaves", ""]
block_start = len(out) + 1
# (2) the sweep block, merged 14568-23079, minus 16709-16718 (+ the note)
out += rng(M, 14568, 16708)
note_line = len(out) + 1
out += NOTE
out += rng(M, 16719, 23079)
block_end = len(out)
# (3) represent, merged 23080-23086, then the closing of section Leaves / namespace FrontRows
represent_doc = len(out) + 1
out += rng(M, 23080, 23086)
represent_line = represent_doc + 3
out += ["", "end Leaves", "", "end FrontRows", ""]
# (4) row 76: statement (skeleton 57-73, byte-identical) then the assembled theorem (merged 23254-23269)
out += ["/-! ## Statement of row 76 (verbatim from `Skeleton_W2.lean` L57-73 = `Statements_FINAL.lean`) -/", ""]
struct_line = len(out) + 1
out += rng(S, 57, 73)
struct_end = len(out)
out += ["open FrontRows", "", "/-! ## Assembly of row 76 -/", ""]
ng_doc = len(out) + 1
out += rng(M, 23254, 23269)
ng_line = ng_doc + 1
out += ["end SM"]
text = "\n".join(out) + "\n"
open(OUT, "w", encoding="utf-8").write(text)
n = text.count("\n")
print(f"wrote {OUT}: {n} lines")
print(f"  sweep block: delta L{block_start}-{block_end} (merged 14568-23079 minus 16709-16718; note at L{note_line}-{note_line+1})")
print(f"  represent: docstring L{represent_doc}, theorem L{represent_line}-{represent_line+3} (merged 23080-23086)")
print(f"  NgCommutationClauses: L{struct_line}-{struct_end-1} (+ blank {struct_end}) (skeleton 57-73)")
print(f"  ng_commutation: docstring L{ng_doc}, theorem L{ng_line}-{ng_line+13} (merged 23254-23269)")

# --- verification ---
lines = text.split("\n")
bad = [(i, l) for i, l in enumerate(lines, 1) if "sorry" in l.lower()]
print(f"  sorry (case-insensitive) occurrences: {len(bad)}", bad[:5])
bad2 = [(i, l) for i, l in enumerate(lines, 1) if any(k in l for k in ("#print", "#eval", "#check", "set_option"))]
print(f"  #print/#eval/#check/set_option lines: {len(bad2)}", bad2[:5])
assert lines[struct_line - 1:struct_end] == rng(S, 57, 73), "structure not byte-identical"
assert lines[ng_doc - 1:ng_doc - 1 + 16] == rng(M, 23254, 23269), "ng_commutation not byte-identical"
assert lines[represent_doc - 1:represent_doc - 1 + 7] == rng(M, 23080, 23086), "represent not byte-identical"
# the block minus the note must equal the merged block minus the removed lines
blk = lines[block_start - 1:block_end]
merged_blk = rng(M, 14568, 16708) + rng(M, 16719, 23079)
assert [l for i, l in enumerate(blk, block_start) if not (note_line <= i <= note_line + 2)] == merged_blk, "block not verbatim"
print("  byte-identity checks: structure OK, ng_commutation OK, represent OK, sweep block (minus note) OK")
# structure cmp files for an external `cmp`
open("/tmp/w2sdelta/struct_delta.txt", "w").write("\n".join(lines[struct_line - 1:struct_end]) + "\n")
open("/tmp/w2sdelta/struct_skel.txt", "w").write("\n".join(rng(S, 57, 73)) + "\n")
open("/tmp/w2sdelta/ng_delta.txt", "w").write("\n".join(lines[ng_doc - 1:ng_doc + 15]) + "\n")
open("/tmp/w2sdelta/ng_merged.txt", "w").write("\n".join(rng(M, 23254, 23269)) + "\n")

# --- axiom probe copy ---
probe = text + "\n".join([
    "#print axioms SM.ng_commutation",
    "#print axioms SM.FrontRows.represent",
    "#print axioms SM.FrontRows.U8R.sweep_proof",
    "#print axioms SM.FrontRows.U8R.recordIso",
    "#print axioms SM.FrontRows.U8R.s1b_dirBit_of_cont_before",
    "#print axioms SM.FrontRows.U8R.s1b_dirBit_of_cont_after",
    "#print axioms SM.NgCommutationClauses",
]) + "\n"
os.makedirs("/tmp/w2sdelta", exist_ok=True)
open(PROBE, "w", encoding="utf-8").write(probe)
print(f"  probe: {PROBE}")
