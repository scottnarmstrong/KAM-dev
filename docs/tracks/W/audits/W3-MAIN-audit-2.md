# W3-MAIN independent package audit 2 — tight delta

**Verdict: PASS WITH NOTES for the requested repair delta. F1, F2 and F3 are closed. N1's explicit real-series interface is supplied; the coefficient interpretation is verified by composition with the existing multilinear-reality export.** No frozen theorem is sealed by this infrastructure audit. The remaining notes concern documentation and intentional API migration, not an unpaid source inequality.

Auditor: `maud-wpka-2`, 2026-11-01. Report-only work in `/root/code/KAM-inp-wpka` (physical path `/mnt/HC_Volume_106379410/kam-w/KAM-inp-wpka`). Read AGENTS.md, docs/PLAN.md, docs/DECISIONS.md, `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, round-1 findings, the full current handoff and its W3-MAIN-FIX AUDIT FOCUS. The user's D53 and tight-delta instructions override the generic build priority and broad re-audit requirements.

## Scope and pinned revisions

- HEAD: `9de271c73e55c7cc7ade1a502d9c314a414c7e59`.
- Repair baseline: `574a5b12215879ca080c8ddb810a2c525c5fc141`.
- `inp`: `df53c399b79cada73dd5127697673a2ff0ae6d2a`.
- Compared `git diff inp...HEAD` to identify package/protected-path scope, then reviewed only `git diff 574a5b12..HEAD`: 25 files, 2,090 insertions, 323 deletions. This includes 23 implementation files, six generated root imports, and the handoff. Unchanged round-1 PASS proofs were not re-audited.
- Repair commits: `0176cd0a`, `bdde1482`, `b0f0e487`, `235c5422`, `f7ba7091`, `6d809163`, `9de271c7`.
- Blueprint `blueprint-W/parts/w3-birkhoff.tex`, SHA256 `1e09a1eb1b06815116809f1f45e996b1ba79962ebfb755e3c75b797e5a19b161` (same bytes as round 1).
- Handoff SHA256 `39473af5c6e9924034a8709a5bedbcacab3447fd15f44320b3abfa903bc835a4`.

There is no provider or frozen seal in this delta; provider/frozen type-equality and seal-body probes are N/A. Round-1 findings outside F1–F3/N1 are not reopened. Protected frozen/manifest bytes were compared, not modified.

## Finding disposition

| Finding / source clause | Reviewed exports | Verdict | Evidence |
|---|---|---|---|
| F1: weak transport, blueprint 837–855 | `birkGradML_add`, `birkQuartX_add`, `birkCoefBarNor_eq`, `birkHamBarX_add_birkHamNorX`, `norm_birkHamBarX_add_birkHamNorX_le` | PASS | The bar/normal supports are proved disjoint; their coefficient sum is one masked coefficient family bounded by the original quartic coefficient. The combined field therefore has cubic constant exactly `waveCubicConst p`. |
| F1: actual consumers | `norm_birkRestFieldExt_le`, `norm_birkRestField_le`, `birk_transport_tori_weak`, `birk_transport_tori_weak_real` | PASS | MainWeak consumes the combined estimate before applying the inclusion's norm bound. Both restricted public weak-transport conclusions have `C_*‖Ψ‖³ + 66 C_* C_F‖Ψ‖⁵`; no factor 2 remains and the input weak equation/domain/derivative premises are preserved. |
| F2: literal integrand and inverse | `birkGammaDPlus`, `birkGammaDPlusInv`, `birkGammaDPlus_embed`, inverse identities, `birkY`, `birkY_eq_tsum` | PASS | Operator on the higher-weight carrier is characterized through the injective inclusion; its unit and two-sided inverse are proved on the entire declared carrier. `birkY` is literally the inverse pullback minus the original field, not a substitute series definition. |
| F2: coefficient bound and absolute expansion | `birkYj`, `summable_norm_birkYj`, `tsum_norm_birkYj_le`, `summable_norm_birkY_terms`, `birkY_hasSum` | PASS | `Y_0=0`, `Y_j=V_j` for nonzero j. The zero-term refinement closes the formerly unpaid sum bound `Σ‖Y_j‖ρ₁^(2j+3) ≤ 4 C_*ρ₁³` at the exact source radius. |
| F2: integral and formal series | `birkYInt`, `birkYInt_hasSum`, `birkYInt_eq_tsum`, `birkYSeries_odd`, `birkYSeries_eq_zero`, `hasFPowerSeriesOnBall_birkYInt`, `analyticOnNhd_birkYInt` | PASS | Actual Bochner interval integral; dominated-convergence termwise integration proves coefficients `Y_j/(j+1)`. Unused degrees vanish. The series/analytic statement holds for every ambient extension agreeing on the source ball. |
| F2: reality and remainder attachment | `birkYInt_rho`, `birkYInt_eq_birkXK2` | PASS | Integral reality follows from the proved equality to the genuine K₂ Hamiltonian field and field reality; no integral identity or reality hypothesis is assumed. The alternative proof route changes no conclusion. |
| F3: complex local objects | `birkPsi`, `birkXi`, `birkAF`, `birkBF`, `birkK1`, `birkK2`, `birkK`, `birkXK1`, `birkXK2`, `birkXK` | PASS | First four are functions on `birkBall0`; remainder and fields on `birkBall1`. Every admitted argument has the former semantic guard. `birkInvData` proves the inverse data for all admitted arguments. |
| F3: real/transport local objects | `birkGammaR`, `birkRestField`, `birkTransportQP` and the restated real/conjugacy/transport exports | PASS | Real ball uses 320; complex ball uses 160; transport map requires the already-source pointwise membership proof. The theorem bodies specialize the original guarded helpers without changing physical inclusions, signs, or normal-form equations. |
| F3: extension interface | `IsBirkExtension`, `IsBirkClassAOn`, `IsBirkClassA.of_eqOn` | PASS | Agreement on an open domain gives equality in a neighbourhood and hence equality of derivatives. Every extension is covered; canonical Ext helpers witness that extensions exist. These are representation premises, not assumptions of analyticity, fields, bounds, or conjugacy. |
| N1: real coefficients and radius | `birkGammaRSeries`, `_apply`, `_odd`, `_even`, `birkRealRho1`, `birkRealBall1_eq_ball`, `hasFPowerSeriesOnBall_birkGammaR` | PASS WITH NOTES | Explicit real formal series on `r₁=ρ₁/√2`, all even coefficients zero, odd coefficients `Π Φ_k(𝒵v_i)`. Existing `birkLieMulti_rho` proves reality for distinct arguments, so `Π` gives exactly the real inverse coordinates. A scratch elaboration checks that bridge. The handoff's contrary “Not done” claim is stale; see below. |

## Attempts to refute the repairs

**F1.** Inspected MainQuartSum:37–114 and the changed proof in MainWeak:102–120. Coefficient additivity is proved from absolutely summable gradient terms; disjointness is proved from the bar/normal set definitions. This prevents paying the bound by silently enlarging `C_*`. The weak equation remains in weight `p−1`; its conclusion still produces a weight-`p+1` representative. Constants 44, 22 and 66 are unchanged. No source-premise change was needed.

**F2.** Inspected the inverse semantics in MainYInt:170–226, the literal definition at :233, and its pullback identification at :240. The coefficient estimate in MainYSeries:95–146 uses `j≥1` after the actual zero coefficient is removed; thus the previous geometric-series obstruction does not survive. The domination for integration is the summable family of evaluated coefficient norms, uniformly bounding `t^j` for `t∈[0,1]`. `Set.IccExtend` supplies only values outside the integration interval. The power-series radius is identified with the source ball by `birkBall1_eq_ball`. Reality uses an independently proved K₂ field identity and the nondegenerate symplectic-form argument in `IsBirkClassA.field_rho`; this is not circular through the requested integral reality. Triangular recursion instead of Neumann-composite coefficients remains an acceptable proof-route deviation.

**F3.** Read all six new modules and all changed implementation hunks. Public source objects now have literal subtype/guarded domains. Globally totalized series, derivatives and Ring.inverse remain only under distinctly named `Ext` helpers, documented with their local semantics. They are public for inter-module use; visibility alone does not claim whole-carrier source semantics. The replacement source-facing bounds/fields/reality/conjugacy/transport statements use the restricted objects. The extension hypotheses supply values only; theorems prove the analytic and differential properties for every such extension. There is no vacuity: `.domRestrict` of each existing Ext helper has the helper itself as an extension (`isBirkExtension_restrict`).

Source `K` is defined on Bρ₁; the former stronger helper analyticity on Bρ₀ is retained under `birkKExt_analyticOnNhd`. Exporting the source object on Bρ₁ is the F3 repair, not an evasion of a source hypothesis. Membership formerly passed as `hw` is now carried by a subtype. `hΨ` in transport is exactly the former membership premise. No conclusion-shaped hypothesis or new mathematical premise was found.

**N1.** MainGammaRSeries supplies the formerly missing explicit HasFPowerSeriesOnBall statement. To test the distinction between projection and inverse, the audit probe imports the existing W3-FLOW module `KAM.Wave.Birkhoff.LieBirkC1` and checks, for every tuple of distinct real inputs:

```lean
example (m : ℝ) (hm : 0 < m) {a p : ℝ} (ha : 0 ≤ a) (hp : 1 / 2 ≤ p)
    (k : ℕ) (v : Fin (2 * k + 1) → BirkReal) :
    birkZR (birkGammaRSeries m hm ha hp (2 * k + 1) v) =
      lieMulti (birkT m hm ha hp) k (fun i => birkZR (v i)) := by
  rw [birkGammaRSeries_odd]
  apply birkZR_birkPi
  have h := birkLieMulti_rho (hm := hm) (ha := ha) (hp := hp) k
    (fun i => birkZR (v i))
  simpa only [birkRho_birkZR] using h.symm
```

This uses the unchanged imported producer receipt without re-auditing its proof. Since `birkZR` is the real restriction of `𝒵`, the equality is precisely the identification needed to read the displayed real coefficients as `𝒵⁻¹Φ_k`. No polarization assumption, symmetry assumption or new hypothesis is introduced. A dedicated named bridge in MainGammaRSeries would improve discoverability, but the bridge already follows by direct composition of public exports.

## Source-facing names and intentional migration

Principal source-facing names are restored in MainBall/MainBallReal: the K/K₁/K₂ bounds and fields, `birkK_isClassA`, real identities, conjugacy, all strong/weak and frozen transport exports. `IsBirkClassA.of_eqOn` is declared and used by `.isBirkClassAOn`; there is no remaining reference to `IsBirkClassA.congr`. The later name only changes the congruence helper's identifier, not its premises or conclusion.

This repair intentionally changes the argument carriers and defining modules; it is not byte-for-byte backward API compatibility. In particular:

| Former name | Current interface / disposition |
|---|---|
| `birkGammaR_injOn` | `birkGammaR_injective` for the subtype map; total helper `birkGammaRExt_injOn` retained. Documented in handoff. |
| `birkXK1_analyticAt`, `birkXK2_analyticAt`, `birkXK_analyticAt` | Source-facing `birkXK1_analyticOnNhd`, `birkXK2_analyticOnNhd`, `birkXK_analyticOnNhd` for every extension; old pointwise helper facts renamed with `Ext`. |
| `birkPsi_analyticAt` | Internal `birkPsiExt_analyticAt`; source map `birkPsi` and its inclusion characterization are restricted to Bρ₀. |
| `birkXK2_eq_Q` | Internal antiderivative helper `birkXK2Ext_eq_Q`; public source integral identification is `birkYInt_eq_birkXK2`. |

A repository search found no remaining references to those six removed names. These deliberate helper/API migrations are not missing source-node results. Consumers of the old defining modules must import MainBall/MainBallReal (or MainGammaRSeries for the real series). No universal compatibility claim for untracked external clients is made. Source-facing theorem statements elaborated successfully through the terminal build and declaration probe below.

## Definition classification

- Ball/radius definitions (`birkBall0`, `birkBall1`, `birkRealBall1`, `birkRho1`, `birkRealRho1`): exact source domains and positive radii under the standing mass/weight assumptions; ball equalities proved.
- `birkBarNorSet`, `birkCoefBarNor`: literal union and masked coefficient; disjointness and coefficient admissibility proved.
- `IsBirkExtension`, `IsBirkClassAOn`: logical interfaces for genuine restricted maps, with explicit canonical extensions and local invariance theorem.
- Restricted source maps in MainBall/MainBallReal: literal restrictions of the former formulas; all series/inverse semantics are established at every argument of the public carrier. `birkTransportQP` has the exact source membership guard even though its proof argument is computationally unused.
- `birkGammaDPlus`, `birkGammaDPlusInv`: actual higher-weight derivative/inverse on the entire declared time/point domain; unit and both inverse identities proved.
- `birkY`, `birkYInt`: literal pullback difference and Bochner integral on their source domains; no choose/default object or unsupported totalized inverse on the public carrier.
- `birkYj`, `birkYSeries`: actual integrand coefficients and degree placement; the zero coefficient is required by subtraction, not a junk fallback. `birkGammaRSeries`: explicit real restriction/composition of the complex flow series.
- New `*Ext` helpers (including time-dependent helpers): internal totalizations with explicit local specifications, not asserted as global source objects. All renamed helper bodies retain their former formulas.

## Notes, errata and limitations

1. Handoff `W3-MAIN-handoff.md:206–208` says that only diagonal reality exists and the distinct-input coefficient reality is not exported. This is inaccurate for the checked source tree: `LieBirkC1.lean:37` exports `birkLieMulti_rho` on all ordered tuples, backed by `LieRealMulti.lean:31`. The scratch bridge above closes the projection/inverse distinction. The existing theorem is outside MainGammaRSeries's import closure, so consumers wanting that spelling should also import LieBirkC1. Report the documentation discrepancy; no production repair made.
2. Integral reality is proved by a different route from the blueprint proof, with exactly the same conclusion. No need to require the blueprint's particular commute-integral proof after the identity and reality have been proved.
3. Generated `KAM/Root/Wave.lean` adds exactly six imports in the repair delta (33 over inp). This continues the producer regeneration exception already documented in round-1 N3; the auditor did not edit or regenerate it.
4. No newly suspected defect in the pinned mathematical source or blueprint. Original PDF verification and unchanged round-1 PASS proofs are outside this tight-delta review. No new mathematical deviation was introduced by the auditor.

## Verification

Every audit Lean/Lake subprocess ran serially inside the exact D53 scope:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 <command>
```

No heartbeat, recursion-depth or synthesis-budget override. No clean, package update, cache download, core-root build, or application build. The audit started no leanchecker process.

**Prescribed lint**, exact command (exit 0):

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 \
  /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpka
```

Complete output:

```text
check_lean_modules: PASS (3694 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; checked by file hash only, not built by this run: KAMLunarBand: KAM.SpinOrbit.lunar_barriers, KAM.SpinOrbit.lunar_spin_confinement (--lib KAMLunarBand))
```

**Targeted build**, through the compile-gate driver:

```sh
/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpka \
  KAM.Wave.Birkhoff.MainGammaRSeries
```

The inspected driver holds a compile slot and invokes exactly:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 lake build KAM.Wave.Birkhoff.MainGammaRSeries
```

Driver and Lake exit 0. Output success markers:

```text
[w_build] slot 1: KAM.Wave.Birkhoff.MainGammaRSeries (02:07:48)
✔ [3419/3419] Built KAM.Wave.Birkhoff.MainGammaRSeries (11s)
Build completed successfully (3419 jobs).
```

Lake also replayed deprecation/unused-simp warnings from dependencies; no build error. The terminal module imports MainBallReal/MainBall/MainYSeries/MainYInt and the changed main/transport chains, including MainQuartSum and LieFlow2. The job count includes reused dependencies; this was not a clean library rebuild.

**Fresh axiom/name and N1 probe.** Scratch `.lake/abi-scratch/W3-MAIN-audit-2.lean`, SHA256 `b42e7243e4e439a6f997ac38f06e814c67bd3289402cc81cd2bbd1f29cb0f9f2`. Imports MainGammaRSeries and the unchanged producer LieBirkC1; issues `#print axioms` for all 201 declarations in the inventory and for `birkLieMulti_rho`, and elaborates the N1 identity displayed above. Exact successful invocation:

```sh
systemd-run --user --scope --quiet -p MemoryMax=4G -p MemorySwapMax=0 \
  nice -n 10 env LEAN_NUM_THREADS=1 lake env sh -c \
  'LEAN_PATH="/root/code/KAM-inp-wpka/.lake/abi-scratch/W3-MAIN-audit-2-overlay:$LEAN_PATH" exec lean .lake/abi-scratch/W3-MAIN-audit-2.lean'
```

Exit 0; exactly 202 axiom output lines, no diagnostic. 198 lines report `[propext, Classical.choice, Quot.sound]`, one reports `[propext, Quot.sound]`, three report no axioms. Every result uses only the permitted axioms. Principal findings' theorem exports have `[propext, Classical.choice, Quot.sound]`, including the sharp weak bound, coefficient sum, integral/formal-series/reality, restricted class-A and real-series results. Exact per-declaration axiom sets are in the inventory below. The extra producer axiom line is:

```text
'KAM.Wave.birkLieMulti_rho' depends on axioms: [propext, Classical.choice, Quot.sound]
```

An initial probe invocation with two separate KAM search roots exited 1 before checking declarations: `object file '/root/code/KAM-inp-wpka/.lake/build/lib/lean/KAM/Wave/Birkhoff/LieBirkC1.olean' ... does not exist`. The main snapshot has that unchanged producer artifact, but the worktree does not. Corrected only the scratch search environment: a symlink overlay of the main snapshot, overridden by worktree artifacts, following the prescribed lint overlay model. Reran the identical probe successfully. No producer theorem was edited or newly proved. Scratch probe and scratch overlay were removed after recording results.

**Kernel replay and short-name checker:** launcher-attested as already run in the user instruction. Its output and exit codes are unavailable in this pane. Not rerun; no invented command, output or independently observed exit code. Fresh full-name elaboration/axiom checks and the targeted build are separate evidence, not a claim to have observed the launcher's kernel replay.

**Static delta checks**, exact commands:

```sh
git diff --check 574a5b12..HEAD
git diff --check inp...HEAD
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff 574a5b12..HEAD --name-only -- KAM/Frozen manifest README.md KAM.lean
```

Each exited 0 with empty output. Separately inspected generated-root diff is exactly the imports noted above. All 23 changed implementation files are at most 409 physical lines (`MainYSeries`), with no forbidden proof-escape tokens or option overrides; prescribed lint validates module structure/width and frozen/ABI invariants. Working tree was clean on entry; final only tracked-scope change is the requested new audit report. No state-changing git command and no implementation edit.

## Declaration inventory for this delta

The following inventory includes new definitions/theorems, renamed Ext/aux helpers, and source-facing declarations moved into the restricted-interface modules. It does not re-audit unchanged round-1 declarations. Each row was included in the fresh axiom probe. All names are under `KAM.Wave`; locations are relative to `KAM/Wave/Birkhoff/`.

Axiom legend: `PCQ` = `[propext, Classical.choice, Quot.sound]`; `PQ` = `[propext, Quot.sound]`; `none` = no axioms.

| Declaration | File:line | Verdict / classification | Axioms |
|---|---|---|---|
| `IsBirkExtension` | MainBall.lean:35 | PASS — internal guarded helper / renamed proof | none |
| `isBirkExtension_restrict` | MainBall.lean:42 | PASS — internal guarded helper / renamed proof | none |
| `IsBirkExtension.eqOn_restrict` | MainBall.lean:44 | PASS — internal guarded helper / renamed proof | none |
| `IsBirkExtension.eventuallyEq_restrict` | MainBall.lean:47 | PASS — internal guarded helper / renamed proof | PQ |
| `IsBirkClassAOn` | MainBall.lean:56 | PASS — restricted definition | PCQ |
| `IsBirkClassA.of_eqOn` | MainBall.lean:65 | PASS — restricted interface; source premises preserved | PCQ |
| `IsBirkClassA.isBirkClassAOn` | MainBall.lean:78 | PASS — restricted interface; source premises preserved | PCQ |
| `birkPsi` | MainBall.lean:90 | PASS — restricted definition | PCQ |
| `birkXi` | MainBall.lean:93 | PASS — restricted definition | PCQ |
| `birkAF` | MainBall.lean:97 | PASS — restricted definition | PCQ |
| `birkBF` | MainBall.lean:101 | PASS — restricted definition | PCQ |
| `birkK1` | MainBall.lean:105 | PASS — restricted definition | PCQ |
| `birkK2` | MainBall.lean:108 | PASS — restricted definition | PCQ |
| `birkK` | MainBall.lean:111 | PASS — restricted definition | PCQ |
| `birkXK1` | MainBall.lean:114 | PASS — restricted definition | PCQ |
| `birkXK2` | MainBall.lean:118 | PASS — restricted definition | PCQ |
| `birkXK` | MainBall.lean:121 | PASS — restricted definition | PCQ |
| `birkPsi_embed` | MainBall.lean:132 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXi_embed` | MainBall.lean:137 | PASS — restricted interface; source premises preserved | PCQ |
| `birkAF_eq` | MainBall.lean:143 | PASS — restricted interface; source premises preserved | PCQ |
| `birkInvData` | MainBall.lean:150 | PASS — restricted interface; source premises preserved | PCQ |
| `birkAF_eq_birkGammaDPlus` | MainBall.lean:161 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_eq` | MainBall.lean:173 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkK1_le` | MainBall.lean:177 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkK2_le` | MainBall.lean:182 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkK_le` | MainBall.lean:187 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_rho` | MainBall.lean:192 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK2_rho` | MainBall.lean:198 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkXK1_le` | MainBall.lean:204 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkXK2_le` | MainBall.lean:209 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkXK_le` | MainBall.lean:214 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK_eq` | MainBall.lean:219 | PASS — restricted interface; source premises preserved | PCQ |
| `birkYInt_eq_birkXK2` | MainBall.lean:222 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_analyticOnNhd` | MainBall.lean:230 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK1_field` | MainBall.lean:236 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK2_field` | MainBall.lean:243 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_field` | MainBall.lean:250 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK1_analyticOnNhd` | MainBall.lean:257 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK2_analyticOnNhd` | MainBall.lean:263 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK_analyticOnNhd` | MainBall.lean:269 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_isClassA` | MainBall.lean:275 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK2_isClassA` | MainBall.lean:280 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK_rho` | MainBall.lean:286 | PASS — restricted interface; source premises preserved | PCQ |
| `birkRealBall1` | MainBallReal.lean:35 | PASS — restricted definition | PCQ |
| `isOpen_birkRealBall1` | MainBallReal.lean:37 | PASS — restricted interface; source premises preserved | PCQ |
| `birkZR_mem_birkBall1` | MainBallReal.lean:40 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR` | MainBallReal.lean:46 | PASS — restricted definition | PCQ |
| `birkRestField` | MainBallReal.lean:50 | PASS — restricted definition | PCQ |
| `birkTransportQP` | MainBallReal.lean:55 | PASS — restricted definition | PCQ |
| `birkGammaR_analyticOnNhd` | MainBallReal.lean:67 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_sub` | MainBallReal.lean:76 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_inv` | MainBallReal.lean:84 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_injective` | MainBallReal.lean:89 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_surj` | MainBallReal.lean:93 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_hasFDerivAt` | MainBallReal.lean:99 | PASS — restricted interface; source premises preserved | PCQ |
| `birkGammaR_symplectic` | MainBallReal.lean:107 | PASS — restricted interface; source premises preserved | PCQ |
| `birkH_gammaR` | MainBallReal.lean:116 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_real` | MainBallReal.lean:131 | PASS — restricted interface; source premises preserved | PCQ |
| `birkXK_real` | MainBallReal.lean:145 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_real_fderiv` | MainBallReal.lean:158 | PASS — restricted interface; source premises preserved | PCQ |
| `birkK_real_gradient` | MainBallReal.lean:172 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_conjugacy` | MainBallReal.lean:197 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori` | MainBallReal.lean:214 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_real` | MainBallReal.lean:236 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_frozen_coord` | MainBallReal.lean:262 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_frozen` | MainBallReal.lean:283 | PASS — restricted interface; source premises preserved | PCQ |
| `norm_birkRestField_le` | MainBallReal.lean:311 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_weak` | MainBallReal.lean:319 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_weak_real` | MainBallReal.lean:336 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_weak_frozen_coord` | MainBallReal.lean:364 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_transport_tori_weak_frozen` | MainBallReal.lean:382 | PASS — restricted interface; source premises preserved | PCQ |
| `birk_conjugacy_aux` | MainConj.lean:44 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_frozen_coord_aux` | MainFrozenForm.lean:32 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_frozen_aux` | MainFrozenForm.lean:73 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_weak_frozen_coord_aux` | MainFrozenForm.lean:101 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_weak_frozen_aux` | MainFrozenForm.lean:125 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt` | MainGamma.lean:29 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_analyticOnNhd` | MainGamma.lean:47 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_sub` | MainGamma.lean:80 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_inv` | MainGamma.lean:123 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_injOn` | MainGamma.lean:134 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_surj` | MainGamma.lean:142 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRSeries` | MainGammaRSeries.lean:32 | PASS WITH NOTES — explicit real series (N1) | PCQ |
| `birkRealRho1` | MainGammaRSeries.lean:37 | PASS — exact real radius/domain | PCQ |
| `birkGammaRSeries_apply` | MainGammaRSeries.lean:41 | PASS WITH NOTES — explicit real series (N1) | PCQ |
| `birkGammaRSeries_odd` | MainGammaRSeries.lean:46 | PASS WITH NOTES — explicit real series (N1) | PCQ |
| `birkGammaRSeries_even` | MainGammaRSeries.lean:63 | PASS WITH NOTES — explicit real series (N1) | PCQ |
| `birkRealRho1_pos` | MainGammaRSeries.lean:72 | PASS — exact real radius/domain | PCQ |
| `birkRealBall1_eq_ball` | MainGammaRSeries.lean:77 | PASS — exact real radius/domain | PCQ |
| `hasFPowerSeriesOnBall_birkGammaR` | MainGammaRSeries.lean:94 | PASS WITH NOTES — explicit real series (N1) | PCQ |
| `birkGammaRExt_hasFDerivAt` | MainGammaSympl.lean:68 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGammaRExt_symplectic` | MainGammaSympl.lean:83 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK1Ext` | MainK.lean:71 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK2Ext` | MainK.lean:76 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt` | MainK.lean:82 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_eq` | MainK.lean:88 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkK1Ext_le` | MainK.lean:155 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkK2Ext_le` | MainK.lean:181 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkKExt_le` | MainK.lean:213 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_analyticOnNhd` | MainK.lean:223 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_rho` | MainK.lean:240 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkPsiExt` | MainK1.lean:30 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXiExt` | MainK1.lean:34 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkAFExt` | MainK1.lean:38 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkBFExt` | MainK1.lean:43 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkPsiExt_embed` | MainK1.lean:48 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkPsiExt_analyticAt` | MainK1.lean:58 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXiExt_embed` | MainK1.lean:68 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkInvDataExt` | MainK1.lean:95 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXK1Ext` | MainK1.lean:151 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK1Ext_field` | MainK1.lean:156 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkXK1Ext_le` | MainK1.lean:202 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXK1Ext_analyticAt` | MainK1.lean:248 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXK2Ext` | MainK2a.lean:53 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXK2Ext_analyticAt` | MainK2a.lean:76 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK2Ext_field` | MainK2e.lean:28 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXK2Ext_eq_Q` | MainK2f.lean:105 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkXK2Ext_le` | MainK2f.lean:130 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXKExt` | MainK3.lean:29 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_field` | MainK3.lean:34 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkXKExt_le` | MainK3.lean:62 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXKExt_analyticAt` | MainK3.lean:71 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_isClassA` | MainK3.lean:78 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkGradML_add` | MainQuartSum.lean:37 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkQuartX_add` | MainQuartSum.lean:52 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkBarNorSet` | MainQuartSum.lean:61 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkCoefBarNor` | MainQuartSum.lean:64 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkCoefBarNor_isCoef` | MainQuartSum.lean:66 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkBarSet_disjoint_birkNormalSet` | MainQuartSum.lean:73 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkCoefBarNor_eq` | MainQuartSum.lean:80 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkHamBarX_add_birkHamNorX` | MainQuartSum.lean:98 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `norm_birkHamBarX_add_birkHamNorX_le` | MainQuartSum.lean:107 | PASS — combined quartic coefficient/field repair (F1) | PCQ |
| `birkKExt_real_fderiv` | MainRealId.lean:32 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_real_gradient` | MainRealId.lean:72 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkH_gammaR_aux` | MainRealId.lean:124 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkKExt_real` | MainRealK.lean:27 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXKExt_real` | MainRealK.lean:40 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkTransportQPExt` | MainRealTori.lean:33 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_real_aux` | MainRealTori.lean:140 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_weak_real_aux` | MainRealWeak.lean:29 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_aux` | MainTori.lean:27 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkRestFieldExt` | MainWeak.lean:94 | PASS — internal guarded helper / renamed proof | PCQ |
| `norm_birkRestFieldExt_le` | MainWeak.lean:102 | PASS — internal guarded helper / renamed proof | PCQ |
| `birk_transport_tori_weak_aux` | MainWeak.lean:123 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkBall0` | MainYInt.lean:38 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkBall1` | MainYInt.lean:41 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkBall1_subset_birkBall0` | MainYInt.lean:43 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `isOpen_birkBall0` | MainYInt.lean:50 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `isOpen_birkBall1` | MainYInt.lean:53 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkRho_mem_birkBall1` | MainYInt.lean:56 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkPsiTExt` | MainYInt.lean:63 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXiTExt` | MainYInt.lean:67 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkAFTExt` | MainYInt.lean:71 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkPsiTExt_embed` | MainYInt.lean:81 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkPsiTExt_analyticAt` | MainYInt.lean:91 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkXiTExt_embed` | MainYInt.lean:100 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkAFTExt_embed` | MainYInt.lean:125 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkAFTExt_inverse` | MainYInt.lean:139 | PASS — internal guarded helper / renamed proof | PCQ |
| `abs_lt_two_of_mem_Ioo` | MainYInt.lean:160 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `mem_Ioo_of_mem_Icc01` | MainYInt.lean:164 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaDPlus` | MainYInt.lean:170 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaDPlusInv` | MainYInt.lean:176 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaDPlus_embed` | MainYInt.lean:185 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `isUnit_birkGammaDPlus` | MainYInt.lean:190 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaDPlus_mul_inv` | MainYInt.lean:195 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaDPlusInv_mul` | MainYInt.lean:199 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `norm_birkGammaDPlusInv_le` | MainYInt.lean:204 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkGammaD_embed_birkGammaDPlusInv` | MainYInt.lean:217 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkY` | MainYInt.lean:233 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkY_eq_tsum` | MainYInt.lean:240 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkRho1` | MainYSeries.lean:41 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYj` | MainYSeries.lean:45 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYSeries` | MainYSeries.lean:50 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYj_zero` | MainYSeries.lean:56 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYj_of_ne_zero` | MainYSeries.lean:59 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkRho1_pos` | MainYSeries.lean:63 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkRho1_sq` | MainYSeries.lean:68 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkRho1_q` | MainYSeries.lean:75 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkBall1_eq_ball` | MainYSeries.lean:83 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `norm_lt_birkRho1` | MainYSeries.lean:94 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `norm_birkYj_le` | MainYSeries.lean:100 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `summable_norm_birkYj` | MainYSeries.lean:132 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `tsum_norm_birkYj_le` | MainYSeries.lean:139 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `abs_le_two_of_mem_Icc01` | MainYSeries.lean:153 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYj_term_eq` | MainYSeries.lean:157 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `norm_birkYj_apply_le` | MainYSeries.lean:165 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `summable_norm_birkY_terms` | MainYSeries.lean:172 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkY_hasSum` | MainYSeries.lean:180 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYInt` | MainYSeries.lean:198 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYInt_hasSum` | MainYSeries.lean:202 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYInt_eq_tsum` | MainYSeries.lean:232 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYSeries_coef_eq` | MainYSeries.lean:238 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYSeries_odd` | MainYSeries.lean:253 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkYSeries_eq_zero` | MainYSeries.lean:273 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `hasFPowerSeriesOnBall_birkYInt` | MainYSeries.lean:283 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `analyticOnNhd_birkYInt` | MainYSeries.lean:314 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |
| `birkXK2Ext_hasSum` | MainYSeries.lean:328 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkYInt_eq_birkXK2Ext` | MainYSeries.lean:354 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK2Ext_rho` | MainYSeries.lean:360 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkK2Ext_isClassA` | MainYSeries.lean:378 | PASS — internal guarded helper / renamed proof | PCQ |
| `birkYInt_rho` | MainYSeries.lean:399 | PASS — source-domain integrand/series/integral interface (F2) | PCQ |

The mathematical repair delta is accepted within the stated scope. Only this report was written to the tracked source tree.
