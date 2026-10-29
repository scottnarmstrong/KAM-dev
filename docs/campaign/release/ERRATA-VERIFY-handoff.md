# Errata verification request (release preparation; main orchestrator)

Branch inp-errata (fd88b57a): a writer's draft of docs/ERRATA-AND-DEVIATIONS.md (457 lines),
built from docs/errata/ledger.json (99 candidate errata, 14 dropped, 64 deviations). Every erratum is marked
"candidate erratum, not yet verified". The release procedure (skill lean-orchestrator,
references/errata-and-deviations.md) requires each erratum to be checked against the pinned PDF by an independent,
refute-first verifier before it may be called an erratum.

VERIFICATION (refute-first; do not edit the draft or the ledger; pinned PDFs are in sources/pdf/, hashes in
sources/SHA256SUMS, registry docs/sources.json):
1. For EVERY candidate erratum in the draft: open the pinned PDF at the cited location; confirm the quoted text is
   verbatim; decide whether the claim (what is wrong) is CORRECT, WRONG (the source is right; say why) or UNCLEAR, and
   whether the cited evidence (Lean theorem or audit) actually establishes it. Give one row per erratum with its ledger
   id.
2. For every deviation: check that it is described accurately against the frozen statement (docs/STATEMENTS.md and
   the frozen file) and the source.
3. Check the draft contains no claim beyond the ledger, no internal campaign language, and never credits one author
   or one author's team with any part of the work.
Write docs/campaign/release/ERRATA-VERIFY-audit-1.md: the per-erratum table, counts (correct / wrong / unclear), the
deviation findings, and the edits the draft needs.
