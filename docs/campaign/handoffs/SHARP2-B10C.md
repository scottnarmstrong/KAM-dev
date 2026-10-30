# Handoff SHARP2-B10C: the ℓ¹ entry step on route A (B10c), its theorems (route-A part of B10e), and PlasmaLean with the entry

30 October 2026. Branch `sharp-b10c`, from `sharp-v2` at 5c55a5e0. Worktree `/home/scott/KAM-dev-worktrees/sharp-b10c`.

## Verdict

- **Step 1.** The repaired signature file re-elaborated unchanged against this `sharp-v2`, which has B9's PLCERT
  follow-ups (`NumA.bbar`, `Cert.bar` at `bbar s`). No declaration changed. The only edit is a header note recording
  the re-elaboration and where each target is proved.
- **Step 2.** All six B10c targets of the repaired signatures are proved verbatim:
  - fixed frequency: `schemeAL1_isNewton`, `routeAOkL1.runData`, `g1_v2A_l1`;
  - isoenergetic: `routeAOkIL1.runData`, `schemeIAL1_isNewton`, `iso_g1_v2A_l1`.

  The 23 definitions and structures around them are verbatim too. No signature was false or unprovable.
- **Step 3.** `KAM.Sharp2.Examples.plasmaLean_torus_l1` certifies **e\* = 94/10¹⁷ = 9.4·10⁻¹⁶ = 10^(−15.03)**, with
  closeness `‖K∞ − K‖ ≤ 795750·e`.
  - PLCERT's sup run `plasmaLean_torus` certifies 10^(−16.71), so this is 1.69 orders more. The design expected
    "up to 10^(−15.2)"; the extra 0.15 orders come from retuning the caps for the entry run.
  - The ℓ¹ data of the torus are explicit hypotheses (`CAL1Like`). Their numbers are the design's reading (a) and are
    *assumed*. The result is a conditional comparison of scalar tolerances, not a dominance certificate for
    PlasmaLean's torus (AUDIT-B10D-1 F7).
  - Every other input is certified: `Γ_∞(ω*, δ₀) ≤ 5.51` and `Γ_∞(ω*, ρ) ≤ 1.54` (new fibered checker), B9/PLCERT's
    sup constants, and `e⁻¹ ≤ 0.3679`.
- **Hard rules.** No `sorry`, axiom or override of any kind. Every main result prints
  `[propext, Classical.choice, Quot.sound]`.
- **Audit notes.** AUDIT-B10C-1's two notes are applied:
  - C1: the iso blueprint now names B9's `SchemeA.run` on the original schedule, not `converge_checked`.
  - C2: the F4 row of design §9 now reads "schedule solve bite δ_s and certified average bite `bbar_s ≤ r_s`; entry
    `Γ_∞` additionally at δ₀ and ρ".

**Brief names vs repaired names.** The brief uses the B10D names; the repaired signatures replaced them.
- `entry_step_A` is proved under that name; it is stage 0 in B9's engine.
- `g1_l1A` with its frozen form is `g1_v2A_l1`; `iso_g1_l1A` is `iso_g1_v2A_l1`. Both take the minimum of three
  branches (v1, B9's sup route A, the ℓ¹ entry), proved by cases, so they are never worse than v1 or B9's route A.
- "Stage constants with the entry record" are `entryConsts` and `Ent.*`; positivity is `Ent.nonneg`; downward closure
  is `EntryCond.down`. Monotonicity in `e⁻¹` is the `StepQ.le_*` lemmas of the mirror.
- The engine embedding is `schemeAL1` with `schemeAL1_isNewton`, `routeAOkL1.runData` and `g1_core_AL1`.

## Files

| File | Lines | Content |
|---|---:|---|
| `KAM/Sharp2/L1/EntryA.lean` | 455 | `FrameL1`, `EntryA`, `EntryA.Wf`, `EntryHypA`, `EntryConstsA`, `entryConsts`, `EntryCond`, `entryStageA`, `stageL1`, `condL1`, `xSL1` (verbatim). Named constants `Ent.*`, `entryConsts_eq` (rfl), `Ent.nonneg`, `EntryCond.down`, rate nonnegativity |
| `KAM/Sharp2/L1/NormsOps.lean` | 82 | `L1Vec.sub`, `L1Mat.mono`, `L1Vec.congr_real`, `L1Vec.le`, `L1Mat.le` |
| `KAM/Sharp2/L1/EntryCorrection.lean` | 318 | `EntryData`, `EntryHypA.toData`, `entry_correction_bounds`: each solve is the min of its sup and ℓ¹ bound, plus ℓ¹ bounds of `ξᴺ`, `ξᴸ` |
| `KAM/Sharp2/L1/EntryError.lean` | 213 | `entry_lagrange_le_of`/`entry_lagrange_le` (`C^K_Ω`), `entry_newton_error` |
| `KAM/Sharp2/L1/EntryFrames.lean` | 237 | `BarBdG`, `rBOf`, `frames_barG` (B9's `frames_bar` with general increments), `l1_frame_increment_of` (any correction `ΔK = Lξᴸ + Nξᴺ`), `l1_frame_increment` |
| `KAM/Sharp2/L1/EntryTorsion.lean` | 240 | `torsion_sub_leG` (B9's `torsion_sub_le` with general increments, two frequencies) |
| `KAM/Sharp2/L1/EntryStep.lean` | 480 | `EntryCond.facts`, `entry_frame_rates_of`, `entry_frame_rates`, `entry_torsion_arith`, `entry_step_A` |
| `KAM/Sharp2/L1/EntryScheme.lean` | 225 | `schemeAL1`, `schemeAL1_isNewton`, `routeAOkL1`, `routeAOkL1.runData` (verbatim) |
| `KAM/Sharp2/L1/G1A.lean` | 304 | `c2AL1`, `G1BodyAL1`, `g1_v2A_l1` (verbatim); `g1_core_AL1`, `g1_branch_AL1` |
| `KAM/Iso/Sharp2/L1/EntryCorrection.lean` | 409 | `iso_entry_correction_bounds` |
| `KAM/Iso/Sharp2/L1/EntryError.lean` | 251 | `iso_entry_newton_error` |
| `KAM/Iso/Sharp2/L1/EntryStep.lean` | 335 | `iso_entry_step` |
| `KAM/Iso/Sharp2/L1/Scheme.lean` | 288 | `entryStageIA`, `stageIL1`, `xIL1`, `routeAOkIL1`, `routeAOkIL1.runData`, `schemeIAL1`, `schemeIAL1_isNewton` (verbatim) |
| `KAM/Iso/Sharp2/L1/G1A.lean` | 409 | `c2IL1`, `c3IL1`, `IG1BodyAL1`, `iso_g1_v2A_l1` (verbatim); `iso_g1_core_AL1`, `iso_g1_branch_AL1` |
| `KAM/Sharp2/Examples/PlasmaLean/GammaInf.lean` | 296 | `GInfData` (fibered `Γ_∞` checker at ω*), `GInfData.sound`, `gammaInf_d0`, `gammaInf_rho` |
| `KAM/Sharp2/Examples/MirrorL1.lean` | 615 | `EntryQ`; the rational entry constants `StepQ.e*`; `ecast_*` (exact) and `le_*` (through `e⁻¹ ≤ ei`); `econd_sound`; `NumQ.okL1`, `okL1_sound` into `routeAOkL1`; `sumDL1_le` |
| `KAM/Sharp2/Examples/PlasmaLeanL1.lean` | 292 | `CAL1Like`, `l1Entry`, `l1Var`, `l1Xs`, the kernel checks, `cAL1_core`, `plasmaLean_torus_l1` |
| `KAM.lean` | — | regenerated by `scripts/gen_root_imports.py` (17 new imports). This branch predates the D43 root split, so there is no `KAM/Root` |
| `docs/campaign/design/APOST-SHARP-V2-L1-SIGNATURES.lean.txt` | — | header note only (step 1) |
| `docs/campaign/design/APOST-SHARP-V2-L1.md` | — | §9 F4 wording (C2) and a B10C status paragraph |
| `blueprint/parts/p2s2-l1hybrid.tex`, `blueprint-I/parts/p2s2-iso-l1hybrid.tex` | — | C1 engine wording; `\Lean` tags of the two route-A theorems |
| `scripts/apost_sharp/l1_entry_lean_mirror.py` | — | exact Python mirror of `entryConsts` and `okL1` at τ = 1, fixed frequency; reproduces the PlasmaLean run |

Every Lean file is a module: copyright, `module`, `public import`, docstring, `@[expose] public noncomputable section`.
All are ≤ 615 lines with every line ≤ 100 characters. Helpers live in package namespaces: `KAM.Sharp2.L1`, `Ent`,
`KAM.Iso.Sharp2.L1`, `GInfData`, and the `e`/`l1_` prefixed members of `StepQ`/`NumQ`.

Commits (after 5c55a5e0): 75d51ab0 (fixed frequency), 994d9901 (PlasmaLean, iso correction), 1bc61ea0 (iso route),
36c363f7 (root imports, namespaces, docs, mirror), and this handoff.

## Approach

**Entry constants.** `entryConsts` (verbatim) is a nest of `let`s. `Ent.CS`, `Ent.CXiN`, … name every intermediate,
and `entryConsts_eq` identifies the record with them by `rfl` after destructuring `E`. All proofs then work with the
names, not with `let` bodies.

**The step is B9's, with the ℓ¹ ingredients substituted.**
- `entry_correction_bounds` is `correction_boundsA`, with:
  - `𝓡ηᴺ ≤ min(c σ_Lᵀ, G₀ a_N g) u` (B9's `SDConst` and `l1_cohR`);
  - `⟨T𝓡ηᴺ⟩ ≤ min(t, t_R)·min(c_a σ_Lᵀ, G_ρ a_N g) u` (real points: `SDConst.real` and `l1_cohR_real`);
  - `ξᴸ = 𝓡gᴸ ≤ min(c C_g, C¹_ξᴸ) E`, where `gᴸ = Tξᴺ − ηᴸ` is bounded in ℓ¹ by `L1Mat.mulVec`, then `l1_cohR`.
- `entry_newton_error` is `newton_error_boundsA` with `|Ω_K| ≤ min(C_Ω, (n/e)G₀ a_N g) ε/(γδ^{κ+1})` (the B10b identity
  bound at bites δ, δ).
- Frame increments are the min of the sup Cauchy estimate and, with the certificate, the ℓ¹ one.
  `l1_frame_increment_of` bounds `‖ΔK‖₁ ≤ ν_K A + ν_N B` by Wiener products, then applies the row-sum Cauchy estimate
  to `jac(sumVec ∘ ΔK) = L̄ − L`.
- `frames_barG` and `torsion_sub_leG` are B9's `frames_bar` and `torsion_sub_le` with general increments. In the
  entry's torsion rate `2C^K_Ω ≤ C_Ω + C^K_Ω` absorbs the defect terms. That is the design's (looser) form of `CDT0`.
- The twist and averaged torsion updates are B9's.

**Engine and G1.** `schemeAL1_isNewton` splits on `s = 0`: stage 0 is `entry_step_A`, every later stage is B9's
`schemeA_isNewton.step`. `routeAOkL1.runData` gets nonnegativity from `Ent.nonneg`, the tail from `1 ≤ kp`, and
downward closure from `EntryCond.down`. `g1_core_AL1` is B9's `g1_core_A` on the new scheme; the one change is that
`(stageL1 s).rate 0 = (stageL1 s).CD` needs a case split, since it is no longer definitional. `g1_v2A_l1` cases on
v1 / B9 sup / ℓ¹ for `C₁ = min`, `C₂ = max`. The iso files are B9's iso files with the same substitutions; the
bordered `gᴸ` carries the constant `ξ^ω ω` with `|ω| ≤ Θ`, matching `C¹_ξᴸ`.

**PlasmaLean.**
- **`Γ_∞` certificate.** `GInfData.check` gives one entry per fiber `0 < |k'| ≤ N`: the nearest integer of `−k'ι`, a
  lower bound of `|k'ι + p|` from the enclosure of ι, and the bounds `E₁^j`, checked over an integer list. A
  degree-4 Taylor polynomial with `2π ≥ 6.283` certifies `E₁ ≥ e^{−2πδ}`. Soundness is
  `KAM.smallDivisorSup_snoc_le`. N = 175 at δ₀ (350 fibers) and N = 25 at ρ.
- **Entry mirror.** `NumQ.okL1` is the Boolean form of `routeAOkL1` at τ = 1, with `e⁻¹` replaced by `ei = 0.3679`.
  Constants without `e⁻¹` are cast exactly; the others are monotone in `e⁻¹`. Soundness goes through downward
  closure of the conditions and monotonicity of the error recursion and of the cap sums.
- **The run.** PLCERT's certified sup constants and certificates (prefix 3, classical tail), caps and θ retuned for
  the entry (`l1Var`), `X⋆ = 43/2000`. The run binds on J2 (the stage-3 tail decay) just above `X⋆`.

## Checks and their output

**Step 1, re-elaboration** (before any edit):
```
$ cp docs/campaign/design/APOST-SHARP-V2-L1-SIGNATURES.lean.txt .drafts/b10c/L1Signatures.lean
$ nice -n 5 lake env lean .drafts/b10c/L1Signatures.lean     (exit 0; six "declaration uses `sorry`", nothing else)
```
Rerun after the header note: the same output.

**Targeted builds** (one niced process at a time; final state):
```
$ nice -n 5 lake build KAM.Sharp2.L1.G1A KAM.Iso.Sharp2.L1.G1A KAM.Sharp2.Examples.PlasmaLeanL1
Build completed successfully (3460 jobs).
```
The replayed logs show no warning in any new module. The kernel checks are cheap: `PlasmaLeanL1.lean` (`l1Var_ok`,
`l1Var_close`) builds in 2.6 s; `GammaInf.lean` (`gInfD0_check`, `gInfRho_check`) elaborates in about 6 s.

**Signature probe and axioms.** `.drafts/b10c/SigProbe.lean` restates the six target statements copied from the
signature file and closes each by `apply KAM…<name> <;> assumption`. It exits 0, with only style-linter notes on `<;>`.
```
'KAM.Sharp2.L1.schemeAL1_isNewton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.L1.routeAOkL1.runData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.L1.g1_v2A_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.L1.routeAOkIL1.runData' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.L1.schemeIAL1_isNewton' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.L1.iso_g1_v2A_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.L1.entry_step_A' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Iso.Sharp2.L1.iso_entry_step' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.L1.l1_frame_increment_of' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.Examples.plasmaLean_torus_l1' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.Examples.gammaInf_d0' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.Examples.gammaInf_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Sharp2.Examples.NumQ.okL1_sound' depends on axioms: [propext, Classical.choice, Quot.sound]
```
A whitespace-normalised text comparison of all 29 declarations of the signature file against the modules gives
`29 of 29 verbatim`.

**Lint.** `scripts/lint_sources.sh` exits 1, from the known causes only:
- long lines in sibling `KAM/Sharp2/{Data,Geometry,ModConstants*}.lean`;
- `KAM.lean` over 1500 lines;
- the ABI scratch step missing `FixedSunPlanetaryKAM.olean`.

It reports nothing in `KAM/Sharp2/L1`, `KAM/Iso/Sharp2/L1` or the new example files.
`check_lean_modules: PASS (1567 Lean files, 0 comparator configurations)`; `FROZEN-ANCHOR GUARD OK`.

**Root imports.** `python3 -I scripts/gen_root_imports.py` exits 0 and adds 17 `public import` lines to `KAM.lean`,
committed in 36c363f7. This branch's generator predates D43, so there is no `KAM/Root`. On the next merge of
`sharp-v2`, use the orchestrator's recipe (`checkout --theirs KAM.lean`, rerun, add `KAM.lean KAM/Root`).

**Name clashes.** Every new declaration in the shared namespace `KAM.Sharp2.Examples` was grepped against the
rest of `KAM`.
- No fully qualified name collides.
- Near-misses are in distinct sub-namespaces: `GInfData.fiberOk` and `GInfData.modeNat_one` versus `Balanced`'s, and
  `GInfData.check`/`expLow` versus C5CORE's records.
- Generic helpers were moved into `NumQ`/`GInfData` with `l1_` prefixes.
- Everything else is in `KAM.Sharp2.L1` and `KAM.Iso.Sharp2.L1`, which belong to this package.

**Blueprints.** `latexmk -pdf` of `blueprint/sharp2-l1.tex` and `blueprint-I/sharp2-l1.tex` in a scratch directory
exits 0, with no undefined reference.

**Python** (design tooling, untrusted). `python3 -I scripts/apost_sharp/l1_entry_lean_mirror.py`:
```
X* = 43/2000: ok = True ; e* = 9.422e-16
X* = 109/5000: ok = False ['J2']; e* = 9.554e-16
closeness constant sumD/(X* delta0^4 gamma^2) = 795749.7
sup run (PLCERT): X* = 441/10^6 ok = True
```

## Uncertainties

- **`CAL1Like` is assumed data.** Its numbers read PlasmaLean's declared bounds as ℓ¹ bounds:
  `‖ηᴺ‖₁ ≤ 12.4e`, `‖ηᴸ‖₁ ≤ 24.8e`, `‖T‖₁ ≤ 19.84`, `|T|_ℝ ≤ 19.84`, `‖L‖₁ ≤ 3.1`, `‖N‖₁ ≤ 6.2`.
  - A sup bound alone does not give these readings. Nothing here establishes them for PlasmaLean's torus, whose
    field is not canonical.
  - In the theorem, `e` bounds both the sup error and the scale of the ℓ¹ data. That is reading (a): e is the ℓ¹ error
    bound, and the sup error is ≤ e.
  - The number is a conditional comparison (F7).
- **Tight claims.** The `Γ_∞` claims are tight but certified: 5.505 against 5.51 at δ₀, and 1.535 against 1.54 at ρ.
  The binding modes are `k = (−29, 4)` and `(−7, 1)`.
- **A loose torsion term.** The entry torsion rate keeps the design's `σ_B³w(C_Ω + C^K_Ω)g`, valid since
  `C^K_Ω ≤ C_Ω`. The proof only needs `2C^K_Ω`, so a slightly smaller rate would also be valid. Changing it would
  change a frozen-by-signature definition, so I left it.
- **Both certificates required.** `g1_v2A_l1` and `iso_g1_v2A_l1` take both run certificates (`routeAOk` at `X⋆_A`
  and `routeAOkL1` at `X⋆`). With positive budgets, B9's holds at small `X⋆_A`, so this does not restrict the theorem.
- **The old mirror.** `scripts/apost_sharp/thresholds_v2.py`'s ℓ¹ path still uses the B10D conventions. The new
  `l1_entry_lean_mirror.py` is the exact mirror of the Lean definitions.
- **Route B** stays withdrawn, as in the repaired signatures; it is not part of this package.

## Suspected errata and deviations

- **Pinned sources: none.**
- **Deviations (ours):**
  - The PlasmaLean run retunes caps and θ (`l1Var`) instead of reusing `freqVar`'s. The certified small-divisor
    constants and certificates are reused unchanged.
  - The `Γ_∞` checker uses its own degree-4 exponential test (`2π ≥ 6.283`) rather than
    `KAM.CertificateSharp.SdsData.expLow`. With 6.28, `E₁ = 0.9793` fails at δ₀ by 5·10⁻⁶.
- **Tooling note (not an erratum).** On a check that evaluates to `false`, `decide +kernel` reported "failed to
  reduce … stuck at" an unrelated early conjunct, not that the check was false. This cost a bisection.
- **B9 helpers generalized, not modified:** `frames_barG`, `torsion_sub_leG`, `l1_frame_increment_of`,
  `entry_lagrange_le_of` and `entry_frame_rates_of` are new lemmas in this package. No B9, PLCERT or frozen file
  was edited.
