# E2 prover handoff (P14; branch inp-p14-e2, 047abcbd; off inp (E0 on inp); offloaded package run by the main orchestrator; prover on claude-10)


**Files:** new `KAM/Planetary/Exponential/Enlargement.lean` (83 lines).

**Declarations:** `KAM.Planetary.enlarge` (`bpP:p14:enlarge`, with `stepP:p14:en-lim`, `stepP:p14:en-choice`), signature copied verbatim.
"Positivity of slow erosion" (epsD > 0) is `A⁺ > A₁`, i.e. the `amd_lt` field of `EnlargedData`; the signature file has no separate declaration for it, so none was added.
`EnlargedData` and the other definitions come from E0 `Exponential/Setting` (imported, not redefined).

**Approach:** along the path `t ↦ (t, e_*+t, A₁+t)` as `t → 0⁺` (filter `𝓝[>] 0`), each of the finitely many inequalities (small, deficit, radii, gaps, e<1) is strict at t=0, hence eventually true by `ContinuousAt.eventually_lt`.
Radii and gaps use `d/2 < d` (d>0).
Combine with `Filter.eventually_all` and take `.exists`.

**Checks:**
- `inp_lake_build.sh ... KAM.Planetary.Exponential.Enlargement`: Built successfully, no warnings from my file.
- `scripts/lint_sources.sh`: no long lines, `check_lean_modules` PASS, frozen guard OK, ABI hashes OK. Only message: "KAM.lean is out of date" (the orchestrator regenerates it; I did not edit it).
- `#print axioms KAM.Planetary.enlarge`: `[propext, Classical.choice, Quot.sound]`.

**Uncertainties / errata / deviations / design signals:** none. No heartbeat overrides.

AUDIT FOCUS (design docs/tracks/P/design/P14-LEAN-DESIGN.md row E2, Appendix A and node rows; audits DESIGN-P14-design-audit-{1,2}.md; signatures .drafts/design/P14Signatures.lean): (1) enlarge = signature file exactly, and the E2 slice COMPLETE (the prover says 'positivity of slow erosion' is the amd_lt field of EnlargedData from E0, with no separate signed declaration: confirm against the design and node table); (2) proof sound (en-lim, en-choice; E0 definitions and admissibility consumed as designed); no added premises; (3) hygiene (no EuclideanSpace; no public name already used elsewhere in KAM). Audit ONLY KAM/Planetary/Exponential/Enlargement.lean.
