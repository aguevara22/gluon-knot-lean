# Sources addendum intake — 2026-09-10

The user supplied the sibling delivery directory
`LEAN_HANDOFF_20260909_SOURCES_ADDENDUM/` and its ZIP. No original handoff or
addendum files were changed. Use its `SOURCES/INDEX.md` to locate literature.

Executed `python3 verify_addendum.py` after reading the verifier: 8 checks,
0 failures, all 11 source PDF hashes and all 103 manifest entries match. Its
optional original-bundle check was skipped because that particular historical
directory was not beside it. This verifies supplied bytes, not theorem fidelity,
proof completeness, redistribution rights, or closure of the literature audit.

## Availability for the focused handoff

The addendum includes Ng, Rutherford, Etnyre, the Geiges survey and other PDFs,
plus source-to-interface locators and detailed historical audit records.
Lickorish–Millett's 35-page paper has a text extraction in
`SOURCES/audit/L-1_EXIT/work/lm1987.txt`; Lickorish's book also has extracted text.
Geiges book pp. 108–132 are extracted, with a page image for Prop. 3.5.9.
Thus absence of the publisher PDFs is not absence of all supporting passages.

Useful remaining originals for independent verification are Lickorish–Millett
1987, Lickorish GTM 175, and Geiges's 2008 book. Figure-dependent arguments are
not fully represented by OCR text and the limited supplied page images. Their
precise editions, consumed pages and historical hashes are in NOT_INCLUDED.md.
The existing geometric Lean proofs use none of these interfaces and continue.

The Reidemeister proof-depth review remains unresolved in the historical audit.
Queffelec 2024 is included as a candidate; obtaining another document is not
automatically necessary. This issue must be reviewed at the required geometric
scope when the literature-dependent chain is implemented.

## Interpretive cautions for execution

The frozen source and the focused five-interface policy control. The addendum
is a locator and historical evidence, not permission to narrow a source theorem
or enlarge the axiom list. In particular:

- INDEX section D suggests adding a separate Reidemeister axiom for topological
  links, or omitting ambient-isotopy identification for diagram quotients. Neither
  is automatically valid for this handoff. Preserve every consumed geometric
  conclusion and use only the five permitted interfaces; any additional needed
  equivalence requires proof. Do not silently replace link equivalence by a
  quotient definition or polynomial equality.
- INDEX section A describes `lp:lm-uniqueness` as over the SM's ring. The exact
  frozen input is uniqueness over the source ring Z[l±1,m±1]. Transport to the
  target coefficient ring is the separate theorem `lp:coefficient-transport`.
  Formalize the source input and prove that transport rather than broadening it.
- Historical statements that sources were reviewed or that gaps do not block
  the SM do not establish new Lean theorems or current independent acceptance.

No author answer is needed for these decisions. This intake does not accept any
literature-interface checklist row and does not change the proof denominator.

Rechecked on 2026-09-11 UTC after the user asked whether more sources are needed:
8 checks again passed, including all11 PDF hashes and103 manifest entries. No
additional source was identified as necessary to continue the focused work.
The optional-original and Reidemeister-review qualifications above remain.
