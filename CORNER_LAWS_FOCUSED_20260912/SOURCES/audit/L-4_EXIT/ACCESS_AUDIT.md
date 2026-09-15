# L-4 EXIT — ACCESS AUDIT

Seat `source L-4 EXIT` (cold, seated by the curator's
`evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`, 2026-09-06T00:43:39Z).
Audited object: frame **SM6**. Stamp of this pass: 2026-09-06T01:56:55Z
(`date -u`). Standard: `phase2/VERIFICATION_STANDARD.md`, rule 7 in
particular — **a source is never dismissed, downgraded or routed around on
fetchability**; a blocked source is an access audit and an escalation, never
a verdict.

---

## A0 — the frame, verified before anything was read

```
cd phase25/frames/SM6 && shasum -a 256 -c FRAMED_MANIFEST_SM6.sha256
```
**20/20 OK.** Manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`,
equal to the charter's. Files whose bytes this pass cites:

| file | sha256 |
|---|---|
| `sm-3-statesum.tex` | `8785877b7de6bacc9bc620215ca5dc7d5fd366156a89802d6aa6c15279e11129` |
| `sm-11-registry.tex` | `751fd3e09d1505b448f70c54bdebe56149db2d557bb4575e74409d78d6820077` |
| `sm-refs.bib` | `17277432deb730dfd2ae9264038dd36637be5b2eb54ff5cc33eeea34d1246e04` |
| `DAG.md` | `f4f4ecddaef16db062852f1435626076accdeacbbae7b3d31487d71b24b81cce` |
| `sm.pdf` (215 pp.) | `cc2c7d40ed9b24cbdbbc49c4559dfa2d7d4032786df2f6137d5ad32d4c76f95c` |

## A0b — the predecessor lanes, verified before being read

* `evidence/source_audit/L-4/SHA256SUMS` — **46/46 lane entries OK** from the
  campaign root. The single mismatch is `phase25/RULINGS.md`, an append-only
  live file that has grown since that seat sealed; no lane artefact differs.
* `evidence/source_audit/L-3-L-4_SM2/SHA256SUMS` — that file mixes
  root-relative and lane-relative paths: **24 OK** from the campaign root and
  **14 OK** from inside the lane, **0 FAILED** in either run (the remainder in
  each run are "no such file", i.e. the other run's paths). Every deliverable
  and every `work/` artefact of that lane verifies.

Both lanes are used **as evidence, cited as theirs**, never as inherited
verdicts. Where this seat did not re-read something, it says so.

---

## 1. Sources reached, at this seat's own extraction

Extractor `work/extract_exit.py` (PyMuPDF 1.x, page-by-page `get_text()`),
renderer `work/render.py` (3x, clipped) for the places where the text layer
drops accents or the OCR mangles a display.

| source | file on disk | sha256 | pages read | depth this seat reached |
|---|---|---|---|---|
| Ng, *A skein approach to Bennequin type inequalities* | `phase25/evidence/codex/candidate_front_bound_v1/source/ng_skein_bennequin_author.pdf` | `5e57702f34aeb38e305bf4ad8aec00bdc4c8a0055d9b79b5a4518a922d5df920` | 1–9, 14–15; p. 2 also rendered at 3x | **T2** on the consumed item (Lemma 1 + Fig. 1); statement level on §1.1/Thm 1/Cor 1 with Cor 1's proof read on p. 8 |
| Rutherford, *Thurston–Bennequin number, Kauffman polynomial…* (arXiv v1) | `phase25/evidence/codex/candidate_front_bound_v1/source/rutherford_2006.pdf` | `024dc444599fc5ee4f6eafdb905c24c002b25f6ee204441beb3c7356f8c33476` | 8–12 | **T2** at the root: Lemma 3.2 statement (p. 9) and its whole proof (pp. 10–12), both Cases × five SubCases |
| Etnyre, *Legendrian and transversal knots* | `phase25/evidence/codex/candidate_front_bound_v1/source/etnyre_legendrian_transversal_survey.pdf` | `34826016f982ecf0338bafa8a9665499b78929253595989764b0232adc4ac8f1` | 14–15, 19–20 | statement level (T1) on eq. (9) §2.6.4 and on Lemma 2.22 eq. (17); §2.9 pp. 19–20 read in full for the bridge locator |
| Morton, *Seifert circles and knot polynomials* | `phase198/evidence/source_audit/CONTACT_FRONT_BOUND/source/morton_1986.pdf` | `bc91a638440c1192462bbe289032e86f7cbeb9296c137fb1779672fedd4ee310` | 1–3 (p. 1 skein display and Thm 1 rendered at 3x) | statement level, plus the reference list; the **full proof reading is the L-4 seat's**, cited as theirs |

**Second copy of Ng, checked.** `phase199/state/shared/literature_sources/`
`ng_skein_bennequin.pdf` (`e385326c3096816230a14d8d2b85679401efe25315aa6a6086766c290a9145a3`)
is the copy the earlier seats pinned. Diffing this seat's two extractions
(`work/ng_two_copies.diff`) shows the copies are the **same 15-page document**:
the only differences are the arXiv stamp line *"arXiv:0709.2141v1 [math.GT]
13 Sep 2007"*, present in the shared copy and absent from the author copy,
eight `³`/`´` bracket-glyph artefacts, and three figure-caption line breaks.
Pagination is identical, so every page locator in this file resolves on both.

Bennequin was **not** read by this seat (SM6 consumes it in no proof — grep
below); the statement reading on record is the L-4 seat's.

---

## 2. Blocked sources — escalations, restated by name, not verdicts

### E-25-2 — Franks & Williams, *Braids and the Jones polynomial*, Trans. AMS 303 (1987) 97–108

**Still not on disk.** Sweep run this pass over the whole campaign folder:
`find . -iname "*frank*" -o -iname "*william*" -o -iname "*mfw*"` returns only
campaign-authored instruments (`evidence/codex/phase15-s7-mfw-*`,
`evidence/claude/o12-avoiding/mfw_*.py`) and Alekseev's 2022 arXiv paper —
**no Franks–Williams text**. `phase25/LITERATURE.md` carries the eleven-route
audit of 2026-09-05T15:08:37Z and no text.

Routes tried by this seat, this pass:

| route | outcome |
|---|---|
| `WebFetch` AMS PDF `ams.org/journals/tran/1987-303-01/S0002-9947-1987-0896009-2/…pdf` | **HTTP 403 Forbidden**, body not retrieved |
| `WebSearch` "Franks Williams Braids and the Jones polynomial 1987 full text pdf open access" | bibliographic records and citing papers only (MathWorld, Semantic Scholar landing, several arXiv papers that cite it); **no open-access full text**; DOI 10.1090/S0002-9947-1987-0896009-2 confirmed |

**No verdict is recorded against this source.** It stays escalated to the
operator by name. It does **not** block L-4 on the exit frame: SM6 cites
`FranksWilliams` twice, both inside `sm-11-registry.tex`, and in **no proof**
(citation inventory in §3), and Morton's own p. 108 attributes his Corollary 1
to "[5], [2]" with **[2] = "J. FRANKS and R. F. WILLIAMS. Braids and the Jones
polynomial. (Preprint 1985)"** — read at Morton's reference list, p. 109, this
pass.

### E-25-5 — Rutherford, IMRN 2006, Art. ID 78591 (the published version, Lemma 3.3)

**Still not on disk** (same sweep; only the arXiv v1 PDF is present).

| route | outcome |
|---|---|
| `WebFetch` `academic.oup.com/imrn/article-lookup/doi/10.1155/IMRN/2006/78591` | page reached; **abstract, references and metadata only** — full text behind subscription; Lemma 3.3 not visible |
| `WebFetch` `arxiv.org/abs/math/0511097` (submission history) | **only one version exists: [v1] Fri, 4 Nov 2005** |

**New fact for the escalation, and the reason to keep it open:** there is *no*
arXiv route to the published numbering. The retained v1 is the only public
version, so the campaign's typed corrections of the four malformed index
strings (SM6 `sm-3-statesum.tex`:2283–2295) can be checked against the
published proof **only** if the operator supplies the IMRN text. Priority
remains low — not blocking, for the reason the SM2 seat gave and this seat
re-verified at Rutherford's own bytes (`T2_DELTA.md` §3).

Ng's reference list, p. 15, read this pass, gives the target precisely:
*"[23] D. Rutherford, … Int. Math. Res. Not. 2006, Art. ID 78591;
math/0511097."*

---

## 3. Grep inventory used by the criterion-5 half of this pass

Run over `phase25/frames/SM6/sm-*.tex`:

```
Morton            2 cites, all in sm-11-registry.tex
Bennequin         2 cites, all in sm-11-registry.tex
FranksWilliams    2 cites, all in sm-11-registry.tex
Ng                1 in sm-11-registry.tex, 2 in sm-3-statesum.tex
Rutherford        1 in sm-3-statesum.tex
Etnyre            2 in sm-11-registry.tex, 2 in sm-3-statesum.tex
Geiges            1 in sm-11-registry.tex, 2 in sm-3-statesum.tex
GeigesContact     2 in sm-11-registry.tex, 3 in sm-3-statesum.tex
```

Both `sm-3` occurrences of `Ng` are inside literature material
(`ng:deletions`' proof at :2040, `ng:finite-word` at :2172); the single
`Rutherford` occurrence is inside `ng:finite-word`. **No proof of SM6 cites
Morton, Bennequin or Franks–Williams.**

---

## 4. Containment and conduct

All reading and all temporaries stayed **inside the campaign folder**; the
scratchpad was not used, `/tmp` was not used. Not read or written: `NEWSM/`,
any v7 letter file under `informal draft/`, `challenge/sealed/`, `.env`, any
other seat's lane except the two predecessor L-4 lanes (read-only, hashes
verified first), any frame byte (SM6 read only; nothing in `frames/` written).
No advisor call. No GCP instance created, started or touched. Network use:
four fetches, all listed above, all logged in `phase25/LITERATURE.md`.
