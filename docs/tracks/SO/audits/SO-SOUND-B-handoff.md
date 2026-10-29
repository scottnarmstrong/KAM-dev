# Handoff SO-SOUND-B (branch inp-sosoundb)

Status: all six signed theorems proved, with part A (inp-sosounda, through 803fb551) merged in.
Signed statements are byte-identical to SOSignatures.lean §G. Nothing in Defs.lean, A's files,
KAM/Frozen, manifest, README.md or KAM.lean was touched.

## Files (new)
| File | Lines | Contents |
|---|---|---|
| KAM/Certificate/Sound/Smallness.lean | 71 | `checkSmallness_sound` |
| KAM/Certificate/Sound/Torsion.lean | 77 | `checkTorsion_sound_of` (helper), `checkTorsion_sound` |
| KAM/Certificate/Sound/Energy.lean | 109 | `checkEnergy_sound_of` (helper), `checkEnergy_sound` |
| KAM/Certificate/Sound/Invariance.lean | 149 | `sumVec_hamiltonianVectorFieldℂ`, `sumVec_fderiv_apply`, `dkFreqModel_encloses`, `checkInvariance_sound_of` (helper), `checkInvariance_sound` |
| KAM/Certificate/Soundness.lean | 76 | `checkTorusCertificate_hyps`, `checkTorusCertificate_sound` |

The `_of` helpers take extra hypotheses that are verbatim the signed CONCLUSIONS of A's
`checkHamBounds_sound` and `checkEmbedding_sound`. Each signed theorem is a one-liner that
discharges them with A's theorems.

## Per signed theorem: lemmas consumed
- `checkSmallness_sound`: `checkStatic_sound`, `isoC1_le_isoC1Q`, `isoC2_le_isoC2Q`, `Real.rpow_natCast`
  (after `4*(τ:ℝ) = ((4τ:ℕ):ℝ)`), `0 ≤ err`, and positive denominators (`div_lt_one`, `div_le_iff₀`).
- `checkTorsion_sound`: `torsionModels_sound` (with `D = c.D`, which is open by `isOpen_certDomain`;
  `hnv` from `checkHamBounds_sound`; `K θ ∈ D` from the μ-ball of `checkEmbedding_sound`, with μ > 0;
  the δβ that `checkTorsion` itself computes in its `gramCheck`; `hW`/`hpe` from Static;
  `weight.rho = rho`), then `torsionAvgCheck_sound` (`ρ > 0`). The signed premise `hg`
  (checkGram) is not needed, because the torsion check repeats the Gram certificate itself. It is
  kept in the signature and discarded.
- `checkEnergy_sound`: `Slp.compose_sound` on `[v0]` → `HamExpr.jet_v0` (H∘K) → `Encloses.toDeg`,
  `Encloses.addMixed` with `constModel_encloses (-E0)` → `CertModel.Encloses.average`. Continuity of
  H∘K on the strip uses `HamExpr.contDiffOn_eval` with `hnv` and `K θ ∈ D`. Then
  `torusAverage(H∘K − E0) = energyAverage − E0` (`integral_add`, `integral_const`,
  `volume_unitCube`). The zero-mode ball uses `CertPoly.mem_coeffSumBall` / `coeff_zero_eq`. Last
  come `CC.norm_le_normUp`, `upAdd_ge`, `ble_sound` and `ofRatDown_le`.
- `checkInvariance_sound`: `Slp.compose_sound` on `d1Slots` → `HamExpr.jet_d1` (needs `hnv` and
  `K θ ∈ D`). `dkFreqModel_encloses` follows from `freqModel_encloses`, `dkModels_encloses`,
  `Encloses.mul`, `modelSum_encloses` and `toDeg`. `swapNat_phaseNat` handles the `X_H` swap and
  sign. Each coordinate is bounded with `CertModel.norm_le_supBound`, then combined with
  `norm_sumVec` and `pi_norm_le_iff_of_nonneg` (max norm, never Euclidean).
- `checkTorusCertificate_hyps`: `checkStatic_sound`, `checkStatic_freq`, `checkHamBounds_sound`,
  `TorusCertificate.ham_structural`, `TorusCertificate.emb_structural`, `checkEmbedding_sound`,
  `checkGram_sound`, `checkInvariance_sound`, `checkEnergy_sound`, `checkTorsion_sound` and
  `checkSmallness_sound`. Every `G1Hyps` field comes from exactly one of these.
- `checkTorusCertificate_sound`: `checkTorusCertificate_hyps`, then `KAM.Iso.Apost.g1_explicit`
  (an ordinary implementation module, `KAM.Iso.Apost.G1`; no frozen anchor or provider is
  imported), applied to `(c.D, c.H, c.K, s, γ, err, E0)` with the given `hdio`. Its last two
  bounds are composed with `hdisp`.

## Checks
- `inp_lake_build.sh /root/code/KAM-inp-sosoundb KAM.Certificate.Soundness` →
  `Build completed successfully (3299 jobs).` This covers all four Sound files, Soundness, and A's
  Ham/Embedding/Gram. My files produce no warnings and no `sorry`.
- `scripts/lint_sources.sh`: check_lean_modules PASS (1378 files), FROZEN-ANCHOR GUARD OK, ABI
  HASHES OK (144). Its only failure is `KAM.lean is out of date; run scripts/gen_root_imports.py`.
  KAM.lean is generated (rule 10), so I left it for the orchestrator to regenerate. A reported the
  same failure.
- `main_shortname_check.py` on the five modules: `short-name check OK`.
- Every line is ≤ 100 columns. None of the forbidden tokens appear: native_decide, ofReduceBool,
  elab, macro, run_cmd, addDecl, sorry, implemented_by, extern, and heartbeat overrides.

## Axioms
```
checkSmallness_sound          [propext, Classical.choice, Quot.sound]
checkInvariance_sound         [propext, Classical.choice, Quot.sound]
checkEnergy_sound             [propext, Classical.choice, Quot.sound]
checkTorsion_sound            [propext, Classical.choice, Quot.sound]
checkTorusCertificate_hyps    [propext, Classical.choice, Quot.sound]
checkTorusCertificate_sound   [propext, Classical.choice, Quot.sound]
```

## Uncertainties / design signals / errata
- There were no heartbeat problems, and no sub-check was too weak for its contract.
- `checkTorsion_sound`'s `hg` premise is unused, as explained above. This is not a defect.
- New public helper names, all checked: `sumVec_hamiltonianVectorFieldℂ`, `sumVec_fderiv_apply`,
  `dkFreqModel_encloses`, and the three `_of` helpers. `phaseBasis_inl` was already in KAM, so
  I reused it.
- Suspected errata in pinned sources: none. Deviations introduced: none.

AUDIT FOCUS: scope is part B only: Sound/{Smallness,Invariance,Energy,Torsion}.lean and Soundness.lean (part A's Sound/{Static,Ham,Embedding,Gram} are audited separately as SO-SOUND-A; treat their signed statements as given). (1) the six signed theorems (checkSmallness_sound, checkInvariance_sound, checkEnergy_sound, checkTorsion_sound, checkTorusCertificate_hyps, checkTorusCertificate_sound) byte-identical to /root/code/KAM-inp/.drafts/design/SOSignatures.lean §G (lines ~1069-1117); (2) THE BLACK BOX: checkTorusCertificate_sound applies the sealed implementation theorem KAM.Iso.Apost.g1_explicit (never a frozen anchor or provider) at exactly the instantiation its docstring states, and CertifiedTorus is exactly what g1_explicit concludes with the displacement bound replaced by disp; confirm that no hypothesis of g1_explicit is supplied by anything but a checker-derived fact, the box membership hω, or the Diophantine premise hdio; (3) checkSmallness_sound: isoC1 ≤ isoC1Q / isoC2 ≤ isoC2Q directions, rpow versus Nat powers, strict < 1 and ≤ disp; (4) checkInvariance_sound and checkEnergy_sound: the invariance error and energy average are the exact frozen KAM.Iso objects at (s : ℝ) • ωstar, the frequency models enclose s·ω for every ω in the box, and every DK term is paid; (5) checkTorsion_sound: torsionModels_sound plus torsionAvgCheck_sound at the certificate's own n, and the handoff's claim that the hg premise is unused (signed, harmless?); (6) the three `_of` helpers carry only part A's signed conclusions verbatim as extra hypotheses (parametric pattern) and the signed theorems are one-liners from them; (7) kernel replay and axioms of all six (standard three only). Suspected design or source defects go in the report as errata candidates.
