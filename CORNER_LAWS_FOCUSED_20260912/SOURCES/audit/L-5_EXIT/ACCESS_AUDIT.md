# L-5 on the EXIT frame SM6 — ACCESS AUDIT

Seat: **cold source auditor, literature input L-5** (the torus input), Phase 2.5
exit-frame pass (`phase25/evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`,
2026-09-06T00:43:39Z). Seat name in posts: `source L-5 EXIT`. Fresh seat: not
the author, not a bench, not the curator, and not the SM1 or SM2 L-5 seats.

Routes are recorded as routes, never as verdicts on a source
(`phase2/VERIFICATION_STANDARD.md` rule 7). **Nothing in this audit was
blocked; nothing is escalated for access.**

## A0. Frame pin, done before reading any frame byte

```
cd phase25/frames/SM6 && shasum -a 256 -c FRAMED_MANIFEST_SM6.sha256
  -> 20/20 OK   (sm.tex, sm-0 … sm-11, sm-refs.bib, checks/treecheck.py,
                 README.md, DAG.md, DISCREPANCIES.md, BUILD_RECEIPT.md, sm.pdf)
shasum -a 256 FRAMED_MANIFEST_SM6.sha256
  -> 38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813
```

Matches the self-hash named in the charter and in R-25-46. Frame bytes read for
this audit (hashes in `SHA256SUMS`):

| file | sha256 |
|---|---|
| `phase25/frames/SM6/sm-7-anchors.tex` | `b6cac9737a1dda1ca72b9cab402e1636ab68f1b54c709f4bce8ffd501d545e23` |
| `phase25/frames/SM6/sm-11-registry.tex` | `751fd3e09d1505b448f70c54bdebe56149db2d557bb4575e74409d78d6820077` |
| `phase25/frames/SM6/sm-refs.bib` | `17277432deb730dfd2ae9264038dd36637be5b2eb54ff5cc33eeea34d1246e04` |
| `phase25/frames/SM6/DAG.md` | `f4f4ecddaef16db062852f1435626076accdeacbbae7b3d31487d71b24b81cce` |

No frame byte was modified. SM1–SM5 were not read except through the curator's
`framediff_SM5_SM6.txt`, used only to locate which L-5 bytes moved in round 5.

## A1. Predecessor lanes: verified, read as evidence, inherited as no grade

Both predecessor lanes were checksum-verified **before** being read:

- `phase25/evidence/source_audit/L-5/SHA256SUMS` — 52 hashes, all verify
  (37 lane-relative from inside the lane, 15 repo-root-relative from the repo
  root; the file mixes both path conventions, which is why a single `-c` run
  reports failures from either directory).
- `phase25/evidence/source_audit/L-1-L-5_SM2/SHA256SUMS` — 68 hashes; **66/66
  content files verify**. The two that do not are `phase25/RULINGS.md` and
  `phase25/evidence/curator/LEDGER.md`, both live append-only files that have
  grown since that seat sealed; expected, not a lane defect.

Those lanes were read in full for **what was read at which bytes**, never as
inherited grades. Every clause graded in `T1_STATEMENT.md` and `T2_DELTA.md`
here was re-established from the source page images listed in A2, rendered and
read by this seat.

## A2. Sources on disk, read for this audit

| # | source | file (repo-relative) | sha256 | what I read, and how |
|---|---|---|---|---|
| S1 | Wenzl, *Hecke algebras of type $A_n$ and subfactors*, Invent. Math. **92** (1988) 349–383 | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/wenzl_1988.pdf` | `a6a55b6166edba2fa05cbcac318d0ce446b1981b8c919029081165585b115c61` | GDZ scan, **no usable text layer**; printed pp. **361, 362, 363, 364, 365, 371, 372, 376, 378** rendered at 2.4× with PyMuPDF and read **as page images**. Offset: printed = PDF + 347 (PDF 1 is the GDZ cover; confirmed on every page by the running head). |
| S2 | Jones, *Hecke algebra representations of braid groups and link polynomials*, Ann. of Math. **126** (1987) 335–388 | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/jones_1987_hecke_algebra.pdf` | `e4b3ac1abf52a99bc79cc34920c2e967f3e646b41d3e07dd9943a5dcec4ff11c` | printed pp. **346, 348, 359** rendered at 2.4× and read as page images. PDF p. 1 = JSTOR cover; PDF page $n$ = printed page $333+n$. Byte-identical to `phase199/state/shared/literature_sources/jones_1987_hecke_algebra.pdf` (hash re-computed this pass). |
| S3 | Wenzl, Ph.D. thesis, Univ. of Pennsylvania, 1985 (UMI 8603724) | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/wenzl_1985_thesis.pdf` | `48fdcc8222f83253d083f0b418e33e353b89c3b6ee537c9a17746cebe68ad1be` | microfilm scan with an OCR layer. OCR scanned for the weight/Schur material; **printed p. 32 (PDF p. 38) rendered at 2.6× and read as a page image** because the OCR of the formulas is unreliable. PDF pp. 2–6 (UMI sheet, title page, acknowledgements, introduction) read from the OCR. |
| S4 | Gorsky, *$q,t$-Catalan numbers and knot homology* | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/gorsky_qt_catalan.pdf` | `b4bf365e4736cf6bf9ba6339564c94abab55a8253b2de4075ee4061e1fe38a72` | text layer; printed p. 11 (Thm 3.1, Cor. 3.3, Cor. 3.4) read. Stamp on p. 1: `arXiv:1003.0916v3 [math.AG] 7 Oct 2011`. |
| S5 | Dunfield–Gukov–Rasmussen, *The superpolynomial for knot homologies* | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/dgr_superpolynomial.pdf` | `09a5ea1104b0424b8cb6719b783a2fe8277abf5770f8581cae7cc3276417976f` | text layer; §§2.2–2.5 (PDF p. 7) read. Stamp on p. 1: `arXiv:math/0505662v2 [math.GT] 7 Dec 2005`. |
| S6 | Brini–Eynard–Mariño, *Torus knots and mirror symmetry*, **arXiv v1** | `phase25/evidence/codex/candidate_l5_source_crosscheck_v1/source/bem_torus_knots_mirror_symmetry.pdf` | `50fae483e6042510802ed5b06c00f0c1b21e8ff04a7a1a7c60778438735b7c42` | text layer; eq. (3.35) and its surrounding paragraph read (preprint p. "– 14 –"). Stamp: `arXiv:1105.2012v1 [hep-th] 10 May 2011`. |
| S7 | Brini–Eynard–Mariño, **published**, Ann. Henri Poincaré **13** (2012) 1873–1910 | `phase198/evidence/source_audit/BEM_TORUS_HOMFLY/source/brini_eynard_marino_2012_published.pdf` | `cc6eec5ead06e815f559e36aae08380a32c443f1ac9b3abb7b1e27ee233efb0b` | text layer; **printed p. 1888** read — this is the edition the SM's bib entry names, and it numbers the generating function **(3.35)**, identically to the preprint. |

Internal (non-published) documents read as locators, not as sources:

| file | sha256 | why |
|---|---|---|
| `phase198/manuscript/RC_v4/torus_dictionary.tex` | `dfd31d827ce85861bb7de8235ec3023061921d8cb0465308c1efd94aa530b024` | `hsm:notation`'s round-5 locator RC `p12:source-evaluation` (lines 50–61, proof to :90) |
| `phase198/manuscript/RC_v4/d7_anchors.tex` | `571f2830f313370a47c33044144084dcaf30c0b1c38d8bce670873482ac01306` | `lit:torus`'s round-5 locator RC `an:bem-catalan` (lines 199–264) |
| `phase198/manuscript/RC_v4/d9b_hecke.tex` | `a59ae7240c9f08329519f52d7436be86bb714e46f3a5b7fc8ba99ce651fc410b` | RC `hd:section`, checked for the F-25-159 claim that it does **not** carry the `lit:torus` statement (closing paragraph, lines 1195–1210) |
| `phase198/manuscript/RC_v4/braid_finite.tex` | `7fc051a03c3785abd67ef12b99793e3ebdbc6c3dc17a2a30a927b1661fd5d8c9` | the superseded SM5 locator; line 189 checked for the deferral |

## A3. Online routes tried

Two, both to arXiv abstract pages, to test the SM6 registry's claim that the
verified Gorsky and DGR bytes are the **final** arXiv versions:

| URL | outcome |
|---|---|
| `https://arxiv.org/abs/1003.0916` | 200. Submission history: v1 3 Mar 2010, v2 22 Mar 2010, **v3 7 Oct 2011 (latest)**. The file on disk is v3. |
| `https://arxiv.org/abs/math/0505662` | 200. Submission history: v1 30 May 2005, **v2 7 Dec 2005 (latest)**, "Minor improvements … To appear in Exp. Math.". The file on disk is v2. |

No other online route was needed: every locator cited by SM6 for L-5 resolved
in bytes already inside the campaign folder.

## A4. Blocked sources

**None.** Every published locator SM6 cites for L-5 — Wenzl 1988 pp. 361–364,
371–372 (and pp. 365, 376, 378 for the disclosures); Jones Def. 6.1, Prop. 6.2,
Fig. 5.3/(5.4)/(5.5), Thm 9.7, (9.6), Check 9.8; Gorsky Thm 3.1, Cor. 3.3,
Cor. 3.4; BEM (3.35); DGR §2.3; the 1985 thesis — was found and read at the
printed page. **No escalation is filed by this seat, and none of E-25-1 … E-25-6
touches L-5.** (E-25-3 is L-1's and already lapsed; E-25-5 is L-3/L-4's.)

## A5. Tooling

`pdftotext`, `mutool` and `pdftoppm` are absent on this machine. Page images
were produced with PyMuPDF 1.28.0 (`fitz`) via `work/render.py`:

```
python3 render.py <pdf> <prefix> <comma-separated 1-based PDF pages> [scale]
```

The two arithmetic controls (`work/jones97_corner.py`, `work/controls_r4.py`)
run on sympy 1.11.1 in exact rational arithmetic. They **evaluate a printed
source formula**; they prove nothing new (rule 8).

## A6. Boundaries

No frame byte, no other seat's lane, no `NEWSM/`, no `informal draft/` file, no
v7 letter file, no `challenge/sealed/`, no `.env` was written or read. No
advisor call. No GCP instance. Compute this pass: page rendering plus two
sympy runs, seconds to a few minutes each, on one core.
