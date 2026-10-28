# P11A-W0 prover handoff (branch inp-p11aw0, 6c02f4e; base inp; offloaded package run by the main orchestrator; prover on claude-12)


**File (new):** KAM/Planetary/WeakMeasure/Basic.lean (285 lines). Imports only Mathlib + KAM.Nekhoroshev.Interfaces.Norms.

**Signature declarations copied verbatim** from P11ASignatures.lean: P11Vec, P11CVec, P11Phase, P11Family, p11euclid, p11dot, p11dotZ, p11dotC,
p11thick, p11dg, p11op, p11scalar, p11maxJet, index_def, p11JetBound, p11eta, P11Patch, P11SublevelHyp, p11Csub, p11RNondegenerate,
p11Good, P11DioHyp, p11Index, p11Amount. (Not included: p11CDio, p11GammaStar — they belong to the W8 PowerLaw module; the design table assigns W0 only conv#data/index-def.)

**Added (N3 gate) lemmas:** p11euclid_continuous/_nonneg/_zero; compactness of unit sphere/ball/tuple sets; p11sphere_nonempty;
p11dg_nonneg, le_p11dg, p11dg_attained (n ≥ 1); p11op_nonneg, le_p11op, p11op_attained; p11dg_le_p11op; p11maxJet finite/le/attained/nonneg;
index_def_set_nonempty/_bddBelow, index_def_nonneg, index_def_le, le_index_def (greatest-lower-bound with nonemptiness gate);
p11Index_spec, p11Index_le, p11Amount_pos.
Approach: iteratedFDeriv is a continuous multilinear map, so each sup set is the image of a compact set under a continuous map; sSup_mem gives attainment. No smoothness needed.

**Not proved:** attainment of the infimum in `index_def` (needs joint continuity in (c,y) under ContDiffOn). Downstream uses (stability, rank_compact) need only le/greatest-lower-bound, provided here. Flag if W1/rank_compact needs actual attainment.

**Checks:** `inp_lake_build.sh ... KAM.Planetary.WeakMeasure.Basic`: Build completed successfully, no warnings. `scripts/lint_sources.sh`: check_lean_modules PASS, frozen guard OK, ABI OK; reports "KAM.lean is out of date" (expected: new module; KAM.lean is generated, not edited by me).
`#print axioms` of p11dg_attained, p11op_attained, p11maxJet_attained, le_index_def, p11Amount_pos, p11sphere_nonempty: [propext, Classical.choice, Quot.sound].

**Uncertainties / errata / deviations:** none. No heartbeat options; file well under 1500 lines.

AUDIT FOCUS (design docs/tracks/P/design/P11A-LEAN-DESIGN.md row P11A-W0 and proof plan; audits DESIGN-P11A-design-audit-{1,2,3}.md; signatures .drafts/design/P11ASignatures.lean): (1) statements/definitions = design signatures (conventions, gauges, amounts, attachments of WeakMeasure/Basic), faithful on their whole carrier; (2) proofs sound; no added premises; (3) hygiene. Audit ONLY WeakMeasure/Basic*.

## Round 2 (after audit 1 FAIL W0-01)
Prover fix on inp-p11aw0 at 766c00c; notes in /root/code/KAM-inp-p11aw0/.drafts/handoff-P11A-W0b.md.

AUDIT FOCUS round 2: verify W0-01 of docs/tracks/P/audits/P11A-W0-audit-1.md is fully resolved: joint continuity of the index function, compactness of the nonempty parameter set, attainment of the index_def infimum (an actual minimizing (c, y)), and boundedness/attainment for every supremum/infimum on positive-dimensional unit spheres and nonempty compact patches (retained N3); nothing that passed in round 1 weakened; hygiene. Audit ONLY KAM/Planetary/WeakMeasure/*.
