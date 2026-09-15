# Literature sources shipped with this package

The five literature interfaces of the focused target (six in the full handoff)
are admitted as axioms stated verbatim from blueprint/AXIOM_REGISTRY.md. The
sources below are for the reviewer's confidence and for the CV translations;
they are not needed to state the axioms. Everything the campaign could legally
redistribute (arXiv author versions) is in SOURCES/files/. Publisher versions
are not redistributed; SOURCES/NOT_INCLUDED.md identifies each one exactly
(DOI, edition, pages consumed, sha256 of the copy the auditors read). The pages
actually consumed are on file as text extractions and page images under
SOURCES/audit/<lane>/work/. Map and evidence: SOURCES/INDEX.md.

| interface | source of record | in SOURCES/files | consumed pages on file as text/images | not on file |
|---|---|---|---|---|
| lit:homfly, lp:lm, lp:lm-uniqueness (L-1) | Lickorish–Millett 1987, Topology 26 (Elsevier); Lickorish GTM 175 Thm 15.2 (Springer); FYHLMO 1985; Chmutov–Polyak 2010 | no (publisher versions) | yes: audit/L-1_EXIT/work/lm1987.txt (full paper OCR), lickorish_gtm175.txt and gtm175_pages.txt (Thm 15.2 pages), fyhlmo1985.txt, cp2010.txt, page images lm-05/06/14.png | Reidemeister 1927 proof (see note) |
| ng:finite-word (L-4) | Ng 2007 arXiv:0709.2141v1; Rutherford arXiv:math/0511097v1 Lemma 3.2; Morton 1986 (statement) | yes: ng_2007 (two copies), rutherford_2005; Morton no | Morton text and page images in audit/L-4_EXIT/work | Rutherford IMRN 2006 Lemma 3.3 (arXiv v1 suffices); Franks–Williams (not needed, Morton covers the used half) |
| src:contact (L-3) | Etnyre arXiv:math/0306256v2; Geiges survey arXiv:math/0307242v2; Geiges, Contact Topology, CUP 2008; DeTurck–Gluck | yes: Etnyre, Geiges survey, DeTurck–Gluck; Geiges book no | Geiges book pp. 108–132 text and the Prop. 3.5.9 page image in audit/L-3_EXIT/work | nothing needed beyond that |
| hd:tableau-source (L-5, full handoff only) | Wenzl 1988; Jones 1987; Wenzl thesis; Brini–Eynard–Mariño; Gorsky; Dunfield–Gukov–Rasmussen | yes: BEM arXiv, Gorsky, DGR; Wenzl, Jones, thesis no | page images wz-*, jn-*, wt-38 and exact-arithmetic control scripts in audit/L-5_EXIT/work | nothing needed beyond that |
| hyp:R | not literature: proved in reference/R (CV, RA) and reference/BRIDGE | — | — | — |

Note on Reidemeister's theorem: no printed proof is on file (SOURCES/OPEN_ITEMS.md,
E-25-6). The SM's literature inputs are stated on diagrams. Define links in Lean as
diagrams modulo the three Reidemeister moves and planar isotopy (SOURCES/INDEX.md,
section D) and the theorem is outside the formal scope; it is then neither an axiom nor
a gap. If a topological definition of links is chosen instead, Reidemeister's theorem
becomes an additional axiom that the policy does not permit; do not choose that.
Queffelec 2024 (in files/) is a modern proof, held, not read at depth by the campaign.

Not needed by any proof (records only): Roseman 2000, Franks–Williams 1987, Whitney,
Mehlhorn–Yap, Murakami–Nakanishi, Bennequin 1983.
