# Handoff LP-FREEZE7R: FREEZE-PROPOSAL draft 7 revision 1 (audit 7-1 F1, F2, N2; modeSize scope addition)

Branch `inp-lp-freeze7` (worktree `/root/code/KAM-inp-lp-freeze7`), audited base `809aa0dd`, brief at `b5f8d503`.
Nothing was created, edited or copied under `KAM/Frozen/` or `manifest/`, not even transiently:
`git diff 809aa0dd -- KAM/Frozen manifest KAM.lean README.md` is empty.

**Status: part A complete. Part B (staged providers) is pending**: when part A finished,
`/root/code/KAM-inp-lp-providers` was still on branch `inp-lp-w5a`, so I am waiting for the orchestrator's
message. This section is updated when part B is done.

## Part A result

Draft 7 revision 1 applies the auditor's exact texts for F1, F2 and N2. It also applies the orchestrator's
scope addition (received mid-package): `KAM.Fourier.modeSize` is no longer frozen, and the Diophantine premise of
LP1, LP1-H, LP2, LP2-H is the already-frozen `KAM.IsDiophantine`. No premise was added and none was weakened.
Every anchor and characterization still closes by a sorry-free implementation theorem whose type is Expr-equal
to the draft text. Its axioms are exactly `[propext, Classical.choice, Quot.sound]`.

Counts: 5 anchors, **89** new definitions (88 + 2 new source maps − `modeSize`), 34 characterizations,
**128** frozen file texts, plus 20 already-frozen definitions referenced directly (`KAM.IsDiophantine` added).
The closure has 86 new and 22 already-frozen definitions.

- **F1.** New `KAM.Planetary.Spatial.spatialSourceBarycentricPositions` and `…Velocities`, using **the auditor's
  exact declaration text, without docstrings** (orchestrator note: LP-FREEZE8 used a stand-in with exactly
  these two declarations). Implementation: `KAM/Planetary/Spatial/SourceBarycentric.lean` (same names; plus `rfl`
  equations `…_def`). In LP2 and LP2-H: `∀ μ : ℝ, ∀ hμ : 0 < μ, μ ≤ μ₀ →` and
  `spatialSourceBarycentricPositions ν μ hν hμ (z t).1` / `spatialSourceBarycentricVelocities ν μ hν hμ (z t).2`.
  **Characterizations: `N/A_LITERAL`.** The implementation proves no barycentric identity for these maps:
  `Spatial/Newton.lean:58–80` has only the coordinate unfoldings `…_succ_sub_zero`, `…_succ_sub_succ`, `…_zero`,
  `…_succ`, and no zero mass-weighted sum or `p_i = ν_i V_i`. MAIN L1 (100–106) defines the reconstruction by
  these explicit formulas. This matches draft 7's treatment of the frozen planar `barycentricPositions/Velocities`
  (inherited D20 formulas, no characterization). The remaining asymmetry is recorded in proposal §4.2 and was not
  changed: LP1 and LP1-H still apply the inherited planar maps directly.
- **F2.** `actionAxis`, `eccDeficit`, `spatialBarycentricPositions` and `spatialBarycentricVelocities` now have
  role `internal` (§4.2 cells), and their module docstrings carry the auditor's role paragraph verbatim, line
  breaks included. Their bodies are unchanged. They are added to the §4.4 inventory, which now also states that
  LP0 uses `actionAxis` and `eccDeficit` on the guarded domain (`I ∈ U ⊆ chamber`, `hν`, `e ∈ [0,1]ⁿ`).
- **N2.** The auditor's exact sentence is now in the preamble, with his three line breaks.
- **N1.** The limitation is stated in the proposal's verification summary and in `verification-draft-7r1.txt`
  §2: check (a) is a simulation and does not exercise the real provider/import graph.
- **Scope addition (modeSize).** New bridge `KAM.Planetary.StrongAMD.isDiophantine_iff_forall_modeSize`
  (`KAM/Planetary/StrongAMD/DiophantineBridge.lean`):
  `KAM.IsDiophantine γ τ ω ↔ ∀ k : Fin n → ℤ, k ≠ 0 → γ * (KAM.Fourier.modeSize k : ℝ) ^ (-τ) ≤ |∑ i, (k i : ℝ) * ω i|`.
  It holds for every γ, τ and ω with no premise, since `Real.rpow_neg` needs only `0 ≤ Σ|k_i|`, so the premises are
  literally equivalent. LP1-H and LP2-H use `KAM.IsDiophantine γ ((n : ℝ) - 1 / 2) …`. `modeSize` is removed from
  the frozen set, the closure, the manifest drafts (`fourier.d59.modeSize.v1` removed) and the rebase plan (§7
  point 1 is withdrawn). The proposal's Appendix A records the change and its reason (rebuild of the shared
  `KAM/Fourier/Derivative.lean`).

## Files

New implementation (track LP, non-frozen; every module docstring contains "The statement surface is proposed in
docs/tracks/LP/FREEZE-PROPOSAL."):
- `KAM/Planetary/Spatial/SourceBarycentric.lean` (48 lines): the two F1 definitions and their `_def` equations.
- `KAM/Planetary/StrongAMD/DiophantineBridge.lean` (43 lines): `isDiophantine_iff_forall_modeSize`.
- `KAM/Planetary/StrongAMD/PlanarSafety/SourceDiophantine.lean` (189 lines):
  `lp1_planar_strongAMD_safety_source_isDiophantine`, `…_isDiophantine_halfInteger` (closing LP1, LP1-H).
Changed: `KAM/Planetary/Spatial/SpatialSafety/SourceCorollary.lean` (now 304 lines), with
`lp2_spatial_strongAMD_safety_source_isDiophantine` and `…_isDiophantine_halfInteger` (closing LP2, LP2-H);
`KAM/Root/Planetary.lean` (generated, +3 imports).
Docs: `docs/tracks/LP/FREEZE-PROPOSAL.md` (regenerated); `docs/tracks/LP/freeze/draft7/**` (128 texts and
manifest drafts); `docs/tracks/LP/freeze/verification-draft-7r1.txt` (new; the audited `verification-draft-7.txt`
is kept as it was).

Each restated closing theorem's statement is the anchor text, generated from `spec/<X>.stmt`. Each proof is
`simp only [isDiophantine_iff_forall_modeSize]` followed by `exact <unchanged original theorem> <binders>`. The
F1 maps unfold by definition.

## Hash diff against the audited draft 7 (809aa0dd), verification §9

The 8 changed texts are `SpatialBarycentricPositions`, `SpatialBarycentricVelocities`, `ActionAxis`, `EccDeficit`
(F1/F2 role paragraph only) and the 4 anchors LP1, LP1-H, LP2, LP2-H; `manifest-entries.json` also changed.
The two `SpatialSourceBarycentric*` texts are new, and `Fourier/Defs/ModeSize.lean.txt` is removed. **All other
118 files are byte-identical.** In the manifest, the only changes are 2 new ids, 1 removed id
(`fourier.d59.modeSize.v1`) and the `definition_closure` of the 4 anchors. The other 122 entries are unchanged.
Anchor text diffs vs draft 7 are in §6: LP0 unchanged; LP1/LP1-H only the Diophantine premise; LP2/LP2-H the F1
replacements plus the Diophantine premise.

## Checks (wrappers only, one Lean process at a time; outputs in verification-draft-7r1.txt)

- Build `lp_build.sh /root/code/KAM-inp-lp-freeze7 KAM.Planetary.StrongAMD.DiophantineBridge
  KAM.Planetary.Spatial.SourceBarycentric KAM.Planetary.StrongAMD.PlanarSafety.SourceDiophantine
  KAM.Planetary.Spatial.SpatialSafety.SourceCorollary`: rc=0, "Build completed successfully" each; 0 warnings in
  these files.
- (a) 128/128 exit 0; only the 39 expected sorry warnings. (b) 89/89 `rfl`, all TYPE_EQV and REDUCIBILITY_SAME;
  78 VALUE_EQV and 11 VALUE_NOT_EQV, the latter differing only in proof auxiliaries (b2, unchanged list).
  (c) 39/39 close by `exact` and are TYPE_EQV; axioms are standard for all 39. Closure: 86 new + 22 frozen,
  including `KAM.IsDiophantine`; the 3 extra source wrappers are as before.
- `#print axioms` (ax_freeze7r.lean): bridge, both `_def`s, and all 4 restated closing theorems give
  `[propext, Classical.choice, Quot.sound]`.
- `lp_lint.sh`: exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK). The short-name check on
  the 4 modules: OK.

## AUDIT FOCUS

- The F1 declaration bytes vs the auditor's block (no docstrings; `_hν`/`_hμ`; `:=` on the type line).
- The Diophantine replacement: the `KAM.IsDiophantine` argument `fun i => ν i ^ 3 / keplerAction ν z₀ i ^ 3` (and
  the spatial source action), and `τ := (n : ℝ) - 1 / 2` in the corollaries. The bridge is an iff with no premise.
- Role texts of the four F1/F2 helpers, and the two source maps' role note (N/A_LITERAL reason).
- §4.4: LP0's direct use of `actionAxis`/`eccDeficit` is on their source domain.

## Notes for the orchestrator

- Draft 7's `gen.py` `DOC_EDITS` asserts the OLD `spatialKeplerAxis` docstring ("Osculating semimajor axis …"),
  which inp-lp has since corrected. On a merged tree `gen.py` will fail that assertion. Regenerate against
  `.drafts/freeze7/records.json`, or drop that DOC_EDITS entry.
- Part B decision (noted): the providers stay on `inp-lp-providers` until freeze; the roots are not regenerated
  there, scripts are not edited, and the sole accepted lint deviation is "KAM.lean is out of date …
  (KAM/Root/Provider.lean)".
- Generator scratch (gitignored): `.drafts/freeze7/` (`gen.py`, `extract_anchors.py`, `mk_*.py`, `mk_r1_impl.py`,
  `mk_extra_r1.py`, `mk_summary_r1.py`, `mk_providers.py` for part B; draft-7 snapshot in
  `.drafts/freeze7-draft7-snapshot/`, anchor specs of draft 7 in `spec.draft7/`).

## Errata, deviations, design signals

- MAIN errata: none new. Deviations: the modeSize/IsDiophantine switch (orchestrator ruling; literally equivalent
  premise); the role-note wording for the two new source maps (generated module docstrings; the declarations are
  exact). Design signals: none; no heartbeat issue; largest new file 304 lines.
