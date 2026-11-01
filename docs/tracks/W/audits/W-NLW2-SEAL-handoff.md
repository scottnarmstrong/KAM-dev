# Seal audit handoff: `wave.nlw2.v1` (`KAM.Wave.nlw2`)

Owner approval: D61 ("Approve, now get everything sealed and audited!", 2026-11-01, relayed by the main
orchestrator). Branch `inp-w8adapt` (final seal branch: inp with W5, W6, W4-LIECONT landed, plus W8, the provider,
W5 action-angle/initial with their F1 fix, and the W6 tori modules). The seal edit itself is NOT made on this
branch; it is staged in `.drafts/W/SEAL-NLW2-STAGED.md` and is performed by the lander after this audit.

Package audits on this code (all final rounds PASS / PASS WITH NOTES): W5 (W5-STEP-A-1, W5-STEP-B-1, W5-R2A-2),
W5-AA (audit 1, audit 2), W6 (audit 1, audit 2), W7 (audit 1, 2), W8 (audit 1, audit 2 incl. provider),
W3/W4/W4-COMPLETE/W4-LIECONT (landed). W8-ADAPT changed no Lean file.

## SEAL AUDIT FOCUS (fail closed)
1. **Provider** `KAM.Provider.Wave.nlw2` (`KAM/Provider/Wave/Nlw2.lean`): its type is exactly the frozen
   `KAM.Wave.nlw2` (`KAM/Frozen/Wave/Theorems/Nlw2.lean`, read only); body `KAM.Wave.nlw2_proof hm`; the module
   does not import the frozen theorem.
2. **Proof** `KAM.Wave.nlw2_proof` (`KAM/Wave/Assembly/Nlw2Proof.lean`): type exactly the frozen statement;
   imports only frozen DEFINITIONS (`KAM/Frozen/Wave/Defs/*`, `KAM/Frozen/Defs/IsDiophantine`), never a frozen
   theorem anchor or provider; `#print axioms` exactly `[propext, Classical.choice, Quot.sound]`.
3. **Seal body**: in a TEMPORARY copy only, replace the anchor body `by sorry` between the
   FROZEN_ANCHOR_PROOF markers by `by exact KAM.Provider.Wave.nlw2 hm`; it elaborates and
   `#print axioms KAM.Wave.nlw2` = `[propext, Classical.choice, Quot.sound]`. Revert the copy; do not commit it.
4. **Import closure / quarantine**: no module other than the anchor imports `KAM.Provider.Wave.Nlw2`; no module
   imports any `DRAFT_SORRY` anchor; the transitive closure of `nlw2_proof` contains no `sorry`, `axiom`, `admit`,
   `opaque`, `unsafe`, heartbeat or recursion-depth override.
5. **Frozen surface untouched**: `git diff inp...HEAD -- KAM/Frozen manifest` is empty; frozen-anchor guard and
   ABI hashes pass.
