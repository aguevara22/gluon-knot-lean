# L-3 EXIT — ACCESS AUDIT

Seat `source L-3 EXIT`, cold, seated on frame **SM6** under
`phase25/evidence/curator/EXIT_SOURCE_PASS_CHARTER.md` (curator,
2026-09-06T00:43:39Z). Stamp 2026-09-06T01:56:31Z.

Rule 7 binds: **a source is never dismissed, downgraded or routed around for
fetchability.** Below is every route tried and its outcome. Nothing needed for
L-3 on SM6 was blocked; two named items are carried as optional operator
fetches, neither blocking.

---

## A0 — the audited frame, verified before anything was read

```
cd phase25/frames/SM6 && shasum -a 256 FRAMED_MANIFEST_SM6.sha256
38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813
cd phase25/frames/SM6 && shasum -a 256 -c FRAMED_MANIFEST_SM6.sha256
20/20 OK  (sm.tex, sm-0 … sm-11, sm-refs.bib, checks/treecheck.py,
           README.md, DAG.md, DISCREPANCIES.md, BUILD_RECEIPT.md, sm.pdf)
```

Self-hash equals the value in the charter and in ruling R-25-46. The frame was
read read-only; **no frame byte was written.**

## A0b — the predecessor lanes, verified before being trusted

Both lanes' `SHA256SUMS` mix lane-relative and campaign-root-relative paths, so
each line was resolved against both bases (`work/extract.py` sibling check):

| lane | entries | OK | mismatch | missing |
|---|---|---|---|---|
| `evidence/source_audit/L-3/` | 40 | **40** | 0 | 0 |
| `evidence/source_audit/L-3-L-4_SM2/` | 38 | **38** | 0 | 0 |

(The residual "missing" lines reported by a naive `shasum -c` are the files'
header/blank lines, not entries.) Both lanes verify; their findings are cited
below as **their** claims, and every statement this seat relies on was re-read
at its own extraction.

---

## 1. Sources needed for L-3 on SM6, and how each was obtained

| source | route | outcome |
|---|---|---|
| **Geiges, *An Introduction to Contact Topology*, CUP 2008** (bib key `Geiges`) | already on disk, `phase199/state/shared/literature_sources/geiges_2008_contact_topology.pdf` | **obtained.** sha256 `d1875466909366b13f22d94b25bcf7d0c4d3d8b72eade5ab0b4f3b140dea07f9`, 458 PDF pages, text layer present. The second copy in the same directory (`[Cambridge studies in advanced mathematics 109] … libgen.li.pdf`) is **byte-identical** (same sha256) — one document, two names. Title page (PDF p. 5) read: *An Introduction to Contact Topology*, HANSJÖRG GEIGES, Universität zu Köln; CUP, © 2008 (PDF p. 6). Page offset established by inspection: **printed p = PDF page − 18** (PDF 122 carries the printed header "104"). |
| **Geiges, "Contact Geometry", arXiv:math/0307242v2** (bib key `GeigesContact`) | already on disk, `phase199/state/shared/literature_sources/geiges_contact_geometry.pdf` (copied there by the curator on 2026-09-05T23:29:28Z under F-25-84) | **obtained.** sha256 `e2c1c1789b6b8e005bd2293766738c09ec86eb3dd8ebb59e734eba22d50207bf`, **86 pages**, banner on p. 1 `arXiv:math/0307242v2 [math.SG] 24 Jan 2004`. Byte-identical to the codex lane copy `phase25/evidence/codex/candidate_contact_source_crosscheck_v1/source/geiges_contact_geometry.pdf`. **Printed p = PDF page** (no front matter offset). |
| **Etnyre, "Legendrian and transversal knots", arXiv:math/0306256v2** (bib key `Etnyre`) | already on disk, `phase199/state/shared/literature_sources/etnyre_legendrian_transversal_survey.pdf` | **obtained.** sha256 `34826016f982ecf0338bafa8a9665499b78929253595989764b0232adc4ac8f1`, 58 pages, banner p. 1 `arXiv:math/0306256v2 [math.SG] 22 Nov 2004`. Byte-identical to the codex lane copy. **Printed p = PDF page.** |
| **DeTurck–Gluck** (bib key `DeTurckGluckLinking`) | on disk, `phase199/state/shared/literature_sources/deturck_gluck_linking.pdf`, sha256 `3a89d83883736c0383eb99d7b7799b54fb818d3601092ffd2dbac0040ba5388b` | **obtained**; a comparison source for `fd:gauss-integrand`, not an L-3 premise on SM6. Not re-graded here (the SM2 seat's F-25-85 corroboration stands as its claim). |

**Extraction method.** PyMuPDF 1.28.0 (`work/extract.py`) text layer, plus
**glyph-level re-reads as rendered page images at 4× for the two claims that
turn on individual symbols**: Etnyre eq. (9) (`work/etnyre_p15_eq9.png`) and
Geiges Prop. 3.5.9 (`work/geiges_p117_prop3559.png`). Text layer and image agree
at both. No OCR was used or needed.

## 2. Named items NOT on disk

Neither is blocking; both are recorded so they are not lost.

1. **Saveliev, *Lectures on the Topology of 3–Manifolds*, de Gruyter 1999** —
   reference **[98]** of the Geiges survey (verified in the survey's own
   bibliography, printed p. 85), cited at survey p. 37-reference inside the
   proof of **Lemma 3.3, p. 46** for "the linking number of γ and γ′ is equal
   to the signed number of times that γ′ crosses underneath γ". **Not on disk;
   not requested.** Reason it is not an escalation: the identical fact is
   proved on disk, with a complete printed proof, at **Geiges book
   Proposition 3.4.14, p. 113** — which SM6 already carries through its book
   citation. The survey's single off-disk reduction is therefore *redundant*,
   not *open*. Recorded, not dismissed.
2. **Etnyre, *Handbook of Knot Theory* printing (Elsevier 2005, pp. 105–185)**
   — the bib entry names it; every locator was verified on arXiv v2, which the
   bib note says in as many words. Carried from the SM1 and SM2 seats as an
   **optional operator fetch**: it would settle whether the eq. (9) misprint
   `Π(L)` for `Π(T)` (confirmed here at glyph level on v2) survives into print.
   **Not blocking** — eq. (9) is not the T2 witness for its clause on SM6;
   Geiges is.

## 3. Network, compute, containment

- **Network: none.** Every byte read was already inside the campaign folder. No
  fetch was attempted because none was needed.
- **No GCP instance; no advisor call.**
- Read: `phase25/frames/SM6/` (read-only), `phase25/evidence/source_audit/L-3/`
  and `.../L-3-L-4_SM2/` (predecessor lanes, hash-verified),
  `phase25/evidence/curator/{EXIT_SOURCE_PASS_CHARTER.md,LEDGER.md}`,
  `phase25/{RULINGS.md,KICKOFF_source_audit.md,LITERATURE.md,CHANNEL_source_audit.md}`,
  `phase2/VERIFICATION_STANDARD.md`,
  `phase199/state/shared/literature_sources/` (PDFs above),
  `phase25/evidence/codex/candidate_contact_source_crosscheck_v1/source/`
  (hash comparison only).
- **Not read, not written:** `NEWSM/`, any `v7` letter file under
  `informal draft/`, `challenge/sealed/`, `.env`, any path outside the campaign
  folder.
- Written: this lane only (`phase25/evidence/source_audit/L-3_EXIT/`), plus the
  two append-only posts in `phase25/LITERATURE.md` and
  `phase25/CHANNEL_source_audit.md`.
