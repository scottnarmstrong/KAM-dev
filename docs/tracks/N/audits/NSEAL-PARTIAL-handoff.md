# Seal-key audit request: N-PARTIAL-CONVEX `KAM.Nekhoroshev.partialConvex_nekhoroshev` (sealed by Zohar's team)

Context: lane N was handed to Zohar Komargodski's team on 2026-10-28 (docs/campaign/LANE-N-HANDOFF.md on origin
branch lane-n-handoff). They finished the N11 chain and sealed the frozen anchor in commit a88de4b6 (author zkomargo,
2026-10-29 01:21 UTC: "Seal N-PARTIAL-CONVEX anchor partialConvex_nekhoroshev (D26)"), merged into main via their PR #7
(merge cd1a35ad) and into inp at 677cbecf. The campaign's two-key rule requires an independent seal-key audit by our
side before the P14 package E11 relies on it (P14 design gate N2: "an independently audited sealed anchor with the exact
frozen type").

Audit (refute-first, read-only except your report):
1. Frozen bytes: KAM/Frozen/Nekhoroshev/Theorems/PartialConvexNekhoroshev.lean differs from its pre-seal version ONLY
   in the registered proof body (git diff of the file across a88de4b6); the statement is byte-identical; the manifest
   entry nekhoroshev.d25.partialConvex_nekhoroshev.v1 moved DRAFT_SORRY -> SEALED with the ABI hash unchanged
   (manifest/frozen-anchors.json, docs/MANIFEST-CHANGES.md); scripts/lint_sources.sh (frozen guard, ABI) passes.
2. Exact-type probe: in a scratch file, `example : type_of% @KAM.Nekhoroshev.partialConvex_nekhoroshev :=
   @KAM.Provider.Nekhoroshev.partialConvex_nekhoroshev` elaborates; the seal body is the binder-applied exact (D26).
3. `#print axioms KAM.Nekhoroshev.partialConvex_nekhoroshev`: only propext, Classical.choice, Quot.sound (no sorryAx).
4. Provider quarantine: no module other than the frozen anchor imports KAM.Provider.Nekhoroshev.PartialConvexNekhoroshev.
5. Spot-check the provider's assembly against the N11 design's binder-by-binder plan
   (docs/tracks/N/design/N11-LEAN-DESIGN.md ~L393-420): no conclusion-shaped premise in any N11 theorem the provider
   applies (each N11 package should have an audit report under docs/tracks/N/audits/; list which N11 packages from
   Zohar's team lack one).
Write docs/tracks/N/audits/NSEAL-PARTIAL-audit-1.md with a verdict (PASS / PASS WITH NOTES / FAIL) and findings.
