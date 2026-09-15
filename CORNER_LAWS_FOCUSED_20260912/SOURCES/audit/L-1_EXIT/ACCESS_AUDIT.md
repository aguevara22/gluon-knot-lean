# L-1 EXIT — ACCESS AUDIT

Seat: `source L-1 EXIT` (cold, Phase 2.5 exit-frame source pass).
Frame audited: `phase25/frames/SM6/`, manifest self-hash
`38f27a90469a28b69caf25b9565284f28a27a48c5b4ab43dafbf513a5981c813`,
`shasum -a 256 -c FRAMED_MANIFEST_SM6.sha256` run from inside the frame
**before any reading**: 20/20 OK.

Charter: `phase25/evidence/curator/EXIT_SOURCE_PASS_CHARTER.md`. Standard:
`phase2/VERIFICATION_STANDARD.md` (T1/T2/T3; rules 7 and 8).
Every consultation logged in `phase25/LITERATURE.md` with its depth.

No network fetch was attempted or needed this pass: every text named below was
already inside the campaign folder. No GCP instance. No advisor call.

## Sources on disk, hashed at this pass

| source | path (campaign-relative) | sha256 | depth reached here |
|---|---|---|---|
| Lickorish–Millett, *A polynomial invariant of oriented links*, Topology **26** (1987) 107–141 | `phase199/state/shared/literature_sources/lickorish_millett_1987_topology.pdf` | `358eb4a9c31367299f1074fac18eaab00cfb4e8b068eddb3ff93d7e7a8ee6979` | **proof read (T2)** at pp. 110–123 and 132–134; page render at p. 111 |
| Lickorish, *An Introduction to Knot Theory*, GTM 175 (1997) | `phase199/state/shared/literature_sources/lickorish_gtm175.djvu` | `65a991aaadc55d1301972d134e83a178977409d9e928211a1d2df77a9f0ea918` | **proof read (T2)** at pp. 167–172 (Thm 15.2); **statement read** at pp. 2–4 |
| Chmutov–Polyak, *Elementary combinatorics of the HOMFLYPT polynomial*, IMRN 2010 | `phase199/state/shared/literature_sources/chmutov_polyak_homflypt.pdf` | `82bf564bf2ae1465aaecabbc90392784ae00402d071f7d47f9b71ba99b0e430d` | **statement read (T1)** at p. 1 eq. (1) and p. 3 Remarks 1–2 |
| FYHLMO, Bull. AMS **12** (1985) 239–246 | `phase199/state/shared/literature_sources/fyhlmo_1985_bull_ams.pdf` | `bf76c6c1bda967e5f0cf46ef7d498d916b281a8fd59fe8fac88f68c21d26a06d` | **statement read (T1)** at p. 240, Main Theorem |
| Przytycki–Traczyk, *Invariants of links of Conway type* | `phase199/state/shared/literature_sources/pt_conway_type.pdf` | `702aa879e8cb149b0b076acf233a6fa5a546619aa4715b7b28af113cf4ef9431` | **not re-read this pass**; the SM1 L-1 seat's reading is carried, not re-established |

Journal-page map used for LM: PDF page *n* = printed page 106 + *n*
(independently re-derived here from the running heads). Text layer extracted
with PyMuPDF into `work/lm1987.txt`; the OCR layer of this scan is noisy, so
every load-bearing sentence quoted in `T1_STATEMENT.md` was **also** read on a
2.4× page render (`work/lm-05.png`, `lm-06.png`, `lm-14.png`) or is quoted only
where the OCR is unambiguous. GTM 175 extracted with `djvutxt` into
`work/lickorish_gtm175.txt` and page-indexed into `work/gtm175_pages.txt`;
DjVu page *n* = printed page *n* − 9.

## Route audit for the one item that is NOT at T2: Reidemeister's theorem (E-25-6)

E-25-6 (2026-09-05T19:10:03Z) records Reidemeister's theorem at proof depth as
an open source item and states that Reidemeister 1927 and *Knotentheorie* are
"neither on disk".

**That premise is stale for the campaign folder as a whole.** Before relaying
any escalation I searched the whole folder (`find . -iname '*burde*' -o -iname
'*zieschang*'`, then the containing lane). The following are on disk **inside
the campaign folder**, in a Phase 1.98 evidence lane:

| text | path | sha256 |
|---|---|---|
| Reidemeister, *Knot Theory* — 1983 English translation of the 1932 *Knotentheorie* | `phase198/evidence/codex/rc2_reidemeister_depth_author_v1/source/reidemeister_1932_english.pdf` | `1883e4509ef53f8d2aa011f89c7bca136d7c9cd0fb250e5c81e80e699b7288ce` |
| Burde–Zieschang–Heusener, *Knots*, 3e — publisher preview, Ch. 1 §§A–C | `.../rc2_reidemeister_depth_author_v1/source/burde_zieschang_heusener_2014_preview.pdf` | `46963f3af8b6e2d3fda6c02e0bed8a9598164cebbc841e9cc8e68ae057dec995` |
| Burde–Zieschang–Heusener, *Knots*, 3e (fuller copy) | `phase198/evidence/codex/rc2_tame_category_source_author_v1/burde_zieschang_heusener_3ed.pdf` | `debb55e5caa1dea967cbd8261a8d6473d6bec126f5c02dfe7c4569156b828978` |
| Alexander–Briggs, *On types of knotted curves* (1927) | `.../rc2_reidemeister_depth_author_v1/source/alexander_briggs_1927.pdf` | `3edcfed7d3482e2aebd7402d92fcf2d96b960bd5b7d577652b5d62253528493a` |
| Queffelec, *Reidemeister's theorem using transversality* (2024) | `.../rc2_reidemeister_depth_author_v1/source/queffelec_2024.pdf` | `367f98ee80fa8aef2dc5a7c5d7168d0c2ab3f91ef65d21ec5309740c8b35d1f7` |

Deflated, and this is the part that matters: **their presence on disk does not
by itself lift Reidemeister's theorem to T2, and this seat did not read them at
proof depth this pass.** The Phase 1.98 lane's own report
(`rc2_reidemeister_depth_author_v1/REPORT.md`, 2026-08-30) says outright "no
safe depth-only integration found", "Do not integrate this package as positive
evidence", and records that BZH Ch. 1 "explicitly defers topological/PL
equivalence to Corollary 3.17", absent from the preview. Phase 1.98 is frozen
reference and confers no positive status; I cite it here only as **evidence of
what is on disk and of which routes were already walked**, not as a verdict.

Consequence for the escalation: E-25-6 is **not withdrawn** and **not
downgraded** — it is **restated** (see `RECOMMENDATION.md` §4). The operator's
open question is no longer "is any text on disk"; it is the narrower one
below, which is what a T2 reading would actually have to close.

## Routes tried and their outcomes, this pass

1. Frame manifest verification from inside `phase25/frames/SM6/` — 20/20 OK, self-hash matches the charter. **Success.**
2. Prior seats' lanes `evidence/source_audit/L-1/` and `L-1-L-5_SM2/`: `shasum -a 256 -c` run from the campaign root. L-1: 37 of 37 checkable lines OK (4 header lines are not checksum lines). L-1-L-5_SM2: 66 OK, 2 FAILED — `phase25/evidence/curator/LEDGER.md` and `phase25/RULINGS.md`, both living documents that have changed since that seat sealed. **Both lanes verify on their own artifacts**; `L-1-L-5_SM2/RECOMMENDATION.md` hashes `49e97077a9f03d3136331a744876f19d5d122471b3ed43d8d18a292682774a18`, matching the hash the ledger cites at F-25-53/54/55. **Success.**
3. LM 1987 at pp. 110–123, 132–134: text layer + page renders. **Success.**
4. GTM 175: `djvutxt` full-text, page-indexed; Ch. 1 pp. 2–4 and Ch. 15 pp. 167–172 read. **Success.**
5. Chmutov–Polyak 2010, pp. 1–4. **Success.**
6. FYHLMO 1985, pp. 239–240. **Success.**
7. Jaeger, European J. Combin. **11** (1990) 549–558 — the source of the state-sum identity behind CP's Remarks 1–2. **Not on disk; not sought online this pass.** This is the standing E-25-3, conditional, and it stays conditional: nothing in SM6 consumes CP, so no goal pauses on it.
8. Reidemeister 1927 (Abh. Math. Sem. Hamburg **5**, 24–32) — **not on disk** in any form; only the bibliographic record, already in `sm-refs.bib` and marked "not on file" there. **Not sought online this pass** (the 1932 book's English translation is on disk and is the more useful text; see §4 of the recommendation).

No source was dismissed for fetchability. No paywall was circumvented. No
credential was read, echoed or transmitted; `.env`, `challenge/sealed/`,
`NEWSM/` and every `v7` letter file were not opened.
