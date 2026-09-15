# L-2 EXIT — ACCESS AUDIT

Seat: `source L-2 EXIT`, cold source seat for literature input **L-2** (the
diagram bridge) on the **exit frame SM6**. Opened 2026-09-06T01:45Z.
Charter: `phase25/evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`.
Standard: `phase2/VERIFICATION_STANDARD.md` (T1/T2/T3; rules 7 and 8).

Rule 7 governs this file: routes and outcomes, never verdicts on a source.
Nothing below downgrades any source for unavailability.

## A0 — pins verified by this seat before anything was cited

| object | check | result |
|---|---|---|
| `phase25/frames/SM6/FRAMED_MANIFEST_SM6.sha256` | `shasum -a 256 <manifest>` | `38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813` — **matches the charter's self-hash** |
| the frame's 20 files | `shasum -a 256 -c FRAMED_MANIFEST_SM6.sha256` from inside the frame | **20/20 OK** |
| previous seat's lane `phase25/evidence/source_audit/L-2/SHA256SUMS` | `shasum -a 256 -c` | **14/14 OK** — read as evidence, not as inherited verdicts |

## 1. Sources ON DISK — hashed and read at the cited pages by THIS seat

Read with PyMuPDF text extraction at the page level, from
`phase199/state/shared/literature_sources/`. Hashes computed by this seat.

| file | sha256 (this seat) | pages read by this seat | depth |
|---|---|---|---|
| `carter_1991_proc_ams.pdf` | `b6763e5100079307260621376af10b250791f991bb66a236df823e5e26323de8` | all 7 PDF pages = printed pp. 281–287; §1.3, §1.4, §2.1 (p. 282), §2.2, §2.3 (p. 283), §3.1 (pp. 284–285), §3.2 proof (pp. 285–286) | **T2 for Carter's own theorem** (statement + printed proof read) |
| `smale_1959_diffeos_s2.pdf` | `f2c495988ae1355fbe01a0878228008ad861bfccb17d6cc9c85d219156622c64` | printed pp. 621 (Thms A, B; the Kneser sentence), 625 (Thm 6 (a)–(d)), 626 (closing composition; reference list) | **T1 verbatim at the cited locator; proof chain read at pp. 625–626 by this seat, pp. 622–624 read by the prior seat (not re-read here)** |
| `dowker_thistlethwaite_1983.pdf` | `d5cc9c445e996d4d074693138b3a53ca069687a263b0f87385d1148ce0564fec` | printed pp. 20 (Rule 1 with its justification paragraph), 21 (standing scope sentence; realization; Thm 1 setup), 23 (end of Lemma 1's proof; Cor. 1.1), 24 (Cor. 1.2) | **T1 verbatim at Cor. 1.2; the refinement's proof is NOT printed (checked at the bytes)** |
| `read_rosenstiehl_1976_gauss_crossing_volume2.pdf` | `7c4ff1c99082a6d5f38123139f6a4a039808135fdcdc57c1e0fbd6eb707798b5` | volume front matter (title page, © page), paper opening printed p. 843, Theorem 6 **with its printed proof** and the worked example at printed p. 871 (PDF page 266), paper end printed p. 876 (PDF page 271) | **T2 for RR Thm 6** (statement + printed proof read at the page) |

Toolchain note, not an access failure: `pdftotext`/poppler are absent; PyMuPDF
(`fitz`) is present in the machine's python and was used for extraction.

## 2. Sources NOT on disk — routes tried by THIS seat

### 2.1 Kneser 1926 (escalation **E-25-4**, standing — reproduced independently)

H. Kneser, *Die Deformationssätze der einfach zusammenhängenden Flächen*,
Math. Z. **25** (1926) 362–372, DOI `10.1007/BF01283844`.

| # | route | outcome (this seat, 2026-09-06T01:47–01:51Z) |
|---|---|---|
| 1 | EuDML record `eudml.org/doc/167886` | fetched OK; advertises full text, sole access URL = the GDZ resolver below |
| 2 | `gdz.sub.uni-goettingen.de/dms/resolveppn/?PPN=GDZPPN002368838` | **HTTP 404** |
| 3 | `gdz.sub.uni-goettingen.de/id/PPN266833020_0025` (Math. Z. vol. 25 by GDZ volume-ID pattern) | **HTTP 404** |
| 4 | `gdz.sub.uni-goettingen.de/id/GDZPPN002368838` (article-ID pattern) | **HTTP 404** |
| 5 | `histmath-heidelberg.de/homo-heid/gdz/kneser-h.htm` (GDZ index of Kneser's papers) | **TLS handshake failure** (`SSLV3_ALERT_HANDSHAKE_FAILURE`) — server side; same failure the prior seat recorded, now independently reproduced |
| 6 | `link.springer.com/article/10.1007/BF01283844` | **303** to `idp.springer.com/authorize…` (institutional sign-in); no free PDF offered |
| 7 | Crossref `api.crossref.org/works/10.1007/BF01283844` | record retrieved; **bibliographic confirmation** — Kneser, Math. Z. **25**(1), 362–372, 1926 — matching Smale's reference [2] exactly as read at Smale p. 626. Links are Springer TDM only; **no OA location** |
| 8 | two web searches (general; and restricted to gdz / digizeitschriften / zbmath) | no free full text surfaced |

**Recorded as an access audit, not a verdict.** GDZ evidently still serves
full text on other identifiers (a `gdz.sub.uni-goettingen.de/fulltext/PPN…`
URL surfaced in search), so the correct PPN for Math. Z. vol. 25 exists and
was not found from here. No paywall was circumvented.

**Bearing on SM6: none.** SM6's sphere-isotopy step is the printed
Lemma `lem:gauss-sphere-isotopy` (sm-3:544–615), which cites neither Smale
nor Kneser; the registry says so at sm-11:149–153. E-25-4 is a would-be
upgrade under the alternative route R2, which R-25-14 did not take.

### 2.2 Roseman 2000 (escalation **E-25-1**, standing — one route re-run)

D. Roseman, *Projections of codimension two embeddings*, Knots in Hellas '98,
Ser. Knots Everything **24** (2000) 380–410, DOI `10.1142/9789812792679_0024`.

| # | route | outcome (this seat) |
|---|---|---|
| 1 | publisher chapter page `worldscientific.com/doi/10.1142/9789812792679_0024` | **HTTP 403** — the prior seat's route 1 reproduced |

The prior seat's eight routes and codex's institutional/BorrowDirect record
stand (`phase25/evidence/source_audit/L-2/ACCESS_AUDIT.md` §2.1;
`phase25/evidence/codex/candidate_roseman_access_v1/OPERATOR_REQUEST.md`).
**Not dismissed — escalated.** Scope on SM6, checked at the bytes: the string
"Roseman" occurs once in the frame, at `sm-11-registry.tex:113–116`, inside
**L-1**, saying the request belongs to L-1's global-Reidemeister route and not
to L-2. **This seat found no step of SM6's L-2 material that needs it.**

## 3. Campaign material consulted as evidence (never as inherited verdicts)

- `phase25/evidence/source_audit/L-2/` (SHA256SUMS 14/14 OK): ACCESS_AUDIT,
  T1_STATEMENT, T2_PROOF, RECOMMENDATION read in full. Every statement of
  theirs repeated here was re-verified first-hand at the PDF bytes.
- `phase25/LITERATURE.md` (grep: Roseman, Kneser, Carter, Smale, Dowker,
  Read), `phase25/RULINGS.md` R-25-13/R-25-14,
  `phase25/evidence/curator/LEDGER.md` rows F-25-58…63, 79, 60, 85, 136, 163,
  E-25-1…5.
- `phase25/frames/SM6/DAG.md` rows 101–106 and 230; `sm-refs.bib` entries 6, 7,
  52, 53.

## 4. What was NOT done

- No advisor call, no GCP, no download of any source into the repository.
- Nothing outside the campaign folder was read or written.
- Smale pp. 622–624 were not re-read by this seat (the prior seat's T2 read
  is cited as theirs, and this seat's own claim is confined to pp. 621,
  625–626).
