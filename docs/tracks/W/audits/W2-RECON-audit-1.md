# W2-RECON independent audit 1

**Verdict: PASS WITH NOTES for W2-RECON, including its attachment to W-NLW2 clause (5).** No blocking finding. This is an infrastructure-package verdict, not a seal-ready verdict for `KAM.Wave.nlw2`: `wave.nlw2.v1` remains `DRAFT_SORRY`, and this package has no provider or seal. Audit item 1 is inapplicable under the handoff's AUDIT FOCUS.

Audit date: 2026-10-30. Auditor: `maud-wpi-1`. Focused, refute-first source-correspondence audit, report-only. All five new modules and their proofs were read against all of `blueprint-W/parts/w2-reconstruction.tex`; all 68 new public declarations are classified below. No production changes, git mutations, root regeneration, or delegated Lean work were performed. Temporary probes were confined to `.lake/abi-scratch/` and removed at closeout.

## Frozen inputs and scope

- Worktree: `/root/code/KAM-inp-wpi`; HEAD `511cef64524d81764d5f7eeef9aea771e9681fb3`.
- Live comparison ref `inp`: `b81fbefc559ce8a25f8c9711b77d7061b2ba44b7`; three-dot merge base `e6a8449294520ccbdf817e7f1a1c7321612aa5d7`.
- Compared the full `git diff inp...HEAD`: 1028 diff lines, seven files, 981 insertions, no deletions. The five new Lean files total 888 lines; the other changes are the handoff and five authorized generated root imports.
- Authorities read: `AGENTS.md`, `docs/PLAN.md`, `docs/DECISIONS.md` (in particular D41/D43), `/root/code/KAM-inp/.drafts/briefs/inp-audit-package.md`, and `docs/tracks/W/audits/W2-RECON-handoff.md` including AUDIT FOCUS.
- Track W has no `docs/tracks/W/statement.md`. Used `docs/tracks/W/W-STATEMENTS.md`, `docs/tracks/W/FREEZE.md`, the actual manifest, eleven frozen Wave definitions, and actual `Nlw2.lean`; the older DRAFT heading in W-STATEMENTS does not supersede D41 or the manifest.
- The focus's `/root/code/KAM/KAM/Frozen/Wave/Theorems/Nlw2.lean` is byte-identical to this worktree's frozen theorem. Manifest ID `wave.nlw2.v1`, export `KAM.Wave.nlw2`, ABI `eca3aee797e9040ce3fde0e946ce30e10fe8550faa413b6a83fc9abda495ddb7`, state `DRAFT_SORRY`. Its twelve definition-closure file hashes match. All eleven frozen Wave definitions are `SEALED` and their whole-file hashes match the manifest.

Snapshot SHA256 (all line locators below refer to these bytes at the recorded HEAD):

| File | SHA256 |
|---|---|
| `KAM/Wave/Recon2/Curve.lean` | `f3c82bd3f0f81da3987f968e56294676da35fced60b23d31ade6926306a20a1f` |
| `KAM/Wave/Recon2/Force.lean` | `8e70eabb1a0de9c7e10e3e34eb52fe19e0ae1fc739928f2d6f8bc057010c8b87` |
| `KAM/Wave/Recon2/Functionals.lean` | `020f45a5b9ca5bc25d5c2b7349082bbc5b05736a9f10c2042c8d159e6a5ff8e9` |
| `KAM/Wave/Recon2/Main.lean` | `575f82a975b3eb2cf379ea9b1f508a6409d3fd1d245c42aa6d311d7b6ee5b139` |
| `KAM/Wave/Recon2/Orbit.lean` | `48bf3f324415df7e3692db9c07700cdc86497ca2ebfef4e2edda1a329f9e1969` |
| `blueprint-W/parts/w2-reconstruction.tex` | `918a2df76dd4b837f6c4a3eff8dc9b5b3caf7a6748bfa4bd116d41c054eb2de7` |
| `KAM/Frozen/Wave/Theorems/Nlw2.lean` | `9ce65519e3108c55e50565b268e7138d5a47ed68fbfade07166d0641b2e2dde6` |

## Focus: frozen clause (5), hypotheses and constants

`Main.lean:40` (`reconWave_main`) agrees with `bpW:w2:main` at blueprint lines 303–334. `Main.lean:90` (`reconWave_clause5`) agrees with `bpW:w2:clause5` at lines 347–361. The intermediate `reconWave_main_le` has a distinctly named, explicitly relaxed bound; it is not substituted for an unconditional result.

| Frozen clause (5), Nlw2.lean:68–78 | Package evidence | Verdict |
|---|---|---|
| “∀ z ∈ Set.univ ×ˢ Set.Icc 0 Real.pi, AnalyticAt ℝ … z” | Main first conjunct; joint analyticity on all ℝ² is proved in Curve before restriction | PASS |
| “IsClassicalSolution m hm (fun t x => reconU …)” | Main second conjunct; Curve:147 supplies `ut`, `ux`, `utt`, `uxx`, all five continuity facts, four derivatives, the PDE and both boundary values | PASS |
| “HasDerivAt … (reconV …) t” for all real t and x in Icc | Main third conjunct; Curve:101 identifies the derivative using actual coefficients of the Banach-space curve derivative | PASS |
| Absolute-value sum with “derivWithin … (Set.Icc 0 Real.pi) x” and “≤ C * Real.sqrt (I 0 + I 1)” | Main has `M_m * B`; main_le relaxes it; clause5 supplies the literal frozen RHS | PASS |

Endpoint refutation attempt: `derivWithin` could otherwise be a totalized default. Curve:177 identifies it with `reconUx` using `uniqueDiffOn_Icc Real.pi_pos x hx`, including x=0 and x=π. No endpoint or differentiability hypothesis is lost. Time derivatives are two-sided. The cubic force identity is used only on `[0,π]`, its actual domain; no unjustified global extension is used for the PDE.

Expanded binder test for the two priority theorems (each data binder or expanded logical premise is one row; nested quantified test points belong to that premise). SOURCE includes the exact H1 embedding components explicitly requested by the blueprint, even though only analyticity is used. There are no extra typeclass premises beyond the concrete ambient types.

| Theorem | Binder / expanded premise | Bin | Authority |
|---|---|---|---|
| main | `m : ℝ` | TYPING | W2 standing data |
| main | `hm : 0 < m` | STANDING | `bpW:w0:mass`, W2 line 24 |
| main | `K : (Fin 2 → ℝ) → WaveSpace` | TYPING | `bpW:w2:main` |
| main | `ν : Fin 2 → ℝ` | TYPING | same |
| main | `B : ℝ` | TYPING | same |
| main | hemb: integer periodicity | SOURCE | H1, frozen IsAnalyticTorusEmbedding:31 |
| main | hemb: AnalyticOnNhd ℝ K univ | SOURCE | H1, same definition |
| main | hemb: injectivity modulo integer translations | SOURCE | H1, same definition |
| main | hemb: injectivity of fderiv everywhere | SOURCE | H1, same definition |
| main | hinv: first coordinate HasDerivAt at 0 | SOURCE | H2, frozen (4) |
| main | hinv: second coordinate HasDerivAt at 0 | SOURCE | H2, frozen (4) |
| main | hbd: ∀ θ, norm K θ ≤ B | SOURCE | H3 |
| main | `θ₀ : Fin 2 → ℝ` | TYPING | “for every θ₀” |
| clause5 | `m : ℝ` | TYPING | `bpW:w2:clause5` |
| clause5 | `hm : 0 < m` | STANDING | W2 standing mass |
| clause5 | `C₃ : ℝ` | TYPING | corollary data |
| clause5 | `hC₃ : 0 < C₃` | SOURCE | corollary “C₃>0” |
| clause5 | `Γ : Set (Fin 2 → ℝ)` | TYPING | corollary data |
| clause5 | `ν : (Fin 2 → ℝ) → Fin 2 → ℝ` | TYPING | corollary data |
| clause5 | `K : (Fin 2 → ℝ) → (Fin 2 → ℝ) → WaveSpace` | TYPING | corollary data |
| clause5 | hemb: periodicity for every I∈Γ | SOURCE | corollary embedding premise |
| clause5 | hemb: analyticity for every I∈Γ | SOURCE | same |
| clause5 | hemb: injectivity modulo integers for every I∈Γ | SOURCE | same |
| clause5 | hemb: derivative injectivity for every I∈Γ | SOURCE | same |
| clause5 | hbd: norm K I θ ≤ C₃ sqrt(I₀+I₁) | SOURCE | corollary bound premise |
| clause5 | hinv: first coordinate HasDerivAt for I∈Γ | SOURCE | corollary frozen-(4) premise |
| clause5 | hinv: second coordinate HasDerivAt for I∈Γ | SOURCE | same |

Counts: main SOURCE=7, STANDING=1, TYPING=5, RULED=0, EXCESS=0; clause5 SOURCE=8, STANDING=1, TYPING=5, RULED=0, EXCESS=0. None of these premises states an obligation about the reconstructed PDE solution. The coefficient equations are source inputs (3)–(4), not a concealed assumption of (5). `IsAnalyticCoeffSolution` expands literally to analyticity and the two coordinate ODEs at every time, as W2 C1/C2 prescribe.

Constant refutation attempt: choosing C after I or θ₀ would weaken the frozen statement. Here `C = max 1 (reconWaveBound m) * C₃` is explicit and precedes all conclusion quantifiers over I, θ₀, t and x. The proof uses `sqrt_nonneg` to obtain both the clause-(3) bound and `M_m*C₃*sqrt ≤ C*sqrt`; it does not assume positive actions to justify this multiplication. `M_m` depends only on m; C depends only on m and the already supplied C₃. The fact that construction supplies C₃ depending only on m remains W6/W8's responsibility, as blueprint lines 363–371 explicitly say.

Fresh scratch composition check: copied the entire frozen clause (3) (including its `hI` and closeness binders), clause (4), and literal clause (5) from the specified frozen file into a fresh `example`, importing Main and frozen LinearTorus but neither the frozen theorem nor its provider. Added `hpos : ∀ I∈Γ, ∀ i, 0<I i`, which is supplied by the frozen Γ-subset conclusion. The result includes `C = max 1 M_m * C₃`, `0<C`, the norm bound with C, and the frozen clause-(5) text. Its complete assembly proof was:

```lean
obtain ⟨C, hC, h0, _, hb, h5⟩ := reconWave_clause5 hm hC₃
  (fun I hI => (h3 I (hpos I hI) hI).1)
  (fun I hI => (h3 I (hpos I hI) hI).2.2) h4
exact ⟨C, hC, h0, hb, h5⟩
```

The probe elaborated at default resource settings. This verifies actual term-level consumption of the frozen (3)/(4) surface and the exact conclusion, not merely matching names. It does not assert a proof of the other clauses of nlw2.

## Definition classification

All five new definitions are literal formulas or the manuscript's literal predicate; no new abbrev, structure, instances or choice construction.

| Definition | Source and body check | Verdict |
|---|---|---|
| `reconUx` (Functionals:33) | W2 derived: coefficient / √λ times √(2/π) j cos(jx); matches for every lp vector and real x | PASS |
| `reconUxx` (Functionals:37) | W2 derived: minus coefficient / √λ times √(2/π) j² sin(jx); minus is inside tsum, equivalent by summability | PASS |
| `reconWaveC0` (Functionals:42) | c₀=√(2/π)/√(exp 2−1) | PASS |
| `reconWaveBound` (Functionals:46) | M_m=c₀(2+√√(1+m)); used only under m>0; no branch or off-domain repair | PASS |
| `IsAnalyticCoeffSolution` (Orbit:35) | W2 C1 plus both C2 HasDerivAt statements at every t,j | PASS |

For each definition: BODY_MATCH=OK; PUBLIC_CARRIER=OK; WELL_DEFINEDNESS=N/A_LITERAL; CHARACTERIZATION=N/A_LITERAL; CHOICE_INDEPENDENCE=N/A; DEFINITION_VERDICT=PASS. The positive denominator follows from m>0, j≥1. Absolute convergence of the derived reconstructions is proved by `summable_abs_reconUx_terms` and `summable_abs_reconUxx_terms`, so neither tsum uses a non-summable default. The predicate is a genuine source-defined analytic coefficient solution, not an invented assumption bundle.

A fresh Lean example proved the exponent bridge:

```lean
example (m : ℝ) (hm : 0 < m) :
    Real.sqrt (Real.sqrt (1 + m)) = (1 + m) ^ (1 / 4 : ℝ) := by
  rw [Real.sqrt_eq_rpow, Real.sqrt_eq_rpow,
    ← Real.rpow_mul (by linarith : 0 ≤ 1 + m)]
  norm_num
```

## Declaration ledger

All names below are in namespace `KAM.Wave`. Supporting elementary lemmas are compared with the indicated blueprint proof steps, rather than misrepresented as additional source theorems. Every public theorem listed also passed the fresh axiom probe. Definitions are separately classified above.

| Node / proof step | Declaration (file:line) | Verdict | Reason / scope |
|---|---|---|---|
| bpW:w2:curve | `analyticAt_coeffSol_fst` (Curve:41) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_coeffSol_snd` (Curve:46) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_reconWave_u` (Curve:53) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_reconWave_ux` (Curve:59) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_reconWave_uxx` (Curve:65) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_reconWave_ut` (Curve:71) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `analyticAt_reconWave_utt` (Curve:77) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `lam_mul_div_sqrt_lam` (Curve:85) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `reconU_eq_reconV_of_coeff` (Curve:92) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `hasDerivAt_reconWave_ut` (Curve:101) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve | `hasDerivAt_reconWave_utt` (Curve:115) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve (iv) | `hasDerivAt_reconWave_ux` (Curve:140) | PASS | Stronger: arbitrary vector; no curve/ODE premise |
| bpW:w2:curve | `isClassicalSolution_reconWave` (Curve:147) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:curve (vi) | `reconWave_bound` (Curve:171) | PASS | Stronger: arbitrary Y; spatial derivative and bound need no coefficient ODE |
| bpW:w2:curve | `reconWave_curve` (Curve:192) | PASS | Exact curve component; analytic coefficient solution premises as C1/C2 |
| bpW:w2:force | `lam_sq_eq` (Force:29) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_lin_term` (Force:33) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_force_summable_lin` (Force:49) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_force_summable_cub` (Force:59) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_force_lin` (Force:68) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_force_cub` (Force:77) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:force | `reconWave_force` (Force:89) | PASS | Exact force component; cubic identity restricted to Icc |
| bpW:w2:derived | `reconUx` (Functionals:33) | PASS | Literal first spatial reconstruction |
| bpW:w2:derived | `reconUxx` (Functionals:37) | PASS | Literal second spatial reconstruction |
| bpW:w2:functionals | `reconWaveC0` (Functionals:42) | PASS | Explicit c₀ |
| bpW:w2:curve | `reconWaveBound` (Functionals:46) | PASS | Explicit M_m |
| bpW:w2:functionals | `sineModeIter_one_eq` (Functionals:48) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `sineModeIter_two_eq` (Functionals:55) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:derived / pairing | `reconUx_eq_iter` (Functionals:61) | PASS | Equality to existing first derivative reconstruction |
| bpW:w2:derived / pairing | `reconUxx_eq_iter` (Functionals:67) | PASS | Equality to existing second derivative reconstruction |
| bpW:w2:functionals | `hasSum_exp_neg_two_pnat` (Functionals:77) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `ellWeight_one_one_eq` (Functionals:99) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `sqrt_lam_sq` (Functionals:103) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconFeatureU_coord_sq_le` (Functionals:117) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconFeatureV_coord_sq_le` (Functionals:149) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `norm_le_sqrt_tsum_of_sq_le` (Functionals:182) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `sqrt_tsum_const_mul` (Functionals:188) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `summable_const_mul_exp` (Functionals:197) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconWaveC0_nonneg` (Functionals:201) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `norm_reconFeatureU_le` (Functionals:205) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `norm_reconFeatureV_le` (Functionals:212) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconU_eq_inner` (Functionals:218) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconUx_eq_inner` (Functionals:222) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconUxx_eq_inner` (Functionals:226) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconV_eq_inner` (Functionals:230) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `abs_reconU_le` (Functionals:234) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `abs_reconUx_le` (Functionals:240) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `abs_reconV_le` (Functionals:246) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `summable_abs_reconU_terms` (Functionals:254) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `summable_abs_reconUx_terms` (Functionals:258) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `summable_abs_reconUxx_terms` (Functionals:263) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `summable_abs_reconV_terms` (Functionals:270) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `hasDerivAt_reconU_reconUx` (Functionals:275) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `hasDerivAt_reconUx_reconUxx` (Functionals:280) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconU_apply_zero` (Functionals:285) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconU_apply_pi` (Functionals:291) | PASS | Functional representation, convergence, calculus or norm proof step |
| bpW:w2:functionals | `reconWave_functionals` (Functionals:299) | PASS | Bundle plus separate abs/convergence exports jointly supply all source items |
| bpW:w2:main / clause5 | `reconWaveBound_nonneg` (Main:32) | PASS | Exact torus reconstruction or constant-management step |
| bpW:w2:main | `reconWave_main` (Main:40) | PASS | Exact H1–H3 and four conclusions with M_m B |
| bpW:w2:main bound monotonicity | `reconWave_main_le` (Main:65) | PASS | Distinct helper with explicit hR; consumed inside clause5 |
| bpW:w2:clause5 | `reconWave_clause5` (Main:90) | PASS | Literal frozen (5), common C, positive C and preserved (3) bound |
| bpW:w2:coeffsol | `IsAnalyticCoeffSolution` (Orbit:35) | PASS | Literal C1/C2 definition |
| bpW:w2:orbit | `isAnalyticCoeffSolution_orbit` (Orbit:44) | PASS | Analytic K and exact invariance at 0 imply ODE at every t by translation |
| bpW:w2:curve-deriv | `hasDerivAt_coeffSol` (Orbit:71) | PASS | Actual curve differentiability and coordinate derivative identification |
| bpW:w2:curve-deriv | `hasDerivAt_coeffSol_fst` (Orbit:77) | PASS | Actual curve differentiability and coordinate derivative identification |
| bpW:w2:curve-deriv | `hasDerivAt_coeffSol_snd` (Orbit:82) | PASS | Actual curve differentiability and coordinate derivative identification |
| bpW:w2:curve-deriv | `coeff_deriv_coeffSol_fst` (Orbit:88) | PASS | Actual curve differentiability and coordinate derivative identification |
| bpW:w2:curve-deriv | `coeff_deriv_coeffSol_snd` (Orbit:97) | PASS | Actual curve differentiability and coordinate derivative identification |

The sole new private lemma, `recon2_lam_le_sqrt_mul` (Functionals:107), proves λ_j≤√(1+m)j from m>0 and j≥1. It implements the blueprint's feature norm estimate and avoids the pre-existing short-name clash noted in the latest commit. It introduces no public premise.

## Refutation notes, provenance and limits

- **Dropped hypothesis:** `reconWave_bound` proves spatial derivative identification and a pointwise functional bound for arbitrary `Y : ℝ → WaveSpace`. Differentiation is in x, so time regularity and the coefficient ODE are unnecessary. `reconWave_curve` still assumes the full C1/C2 predicate for its time derivative and PDE assertions. This is a strict strengthening, not premise deletion from a proof that needed it.
- **Bundled functionals:** `reconWave_functionals` does not itself include every convergence or pointwise norm consequence in its conjunction. Those claims are public exports `summable_abs_recon{U,Ux,Uxx,V}_terms` and `abs_recon{U,Ux,V}_le`; together they supply the full blueprint lemma. No node is marked complete merely from the bundle's name.
- **Force:** linear summability is derived from the two reconstructed derivative series; cubic summability and completeness enter through existing `summable_abs_sqrtLam_waveCubic` and `wave_force_identity`. The new proof keeps the negative force sign and the factors √λ and λ exactly. Those upstream results were inspected at the application boundary and kernel-replayed transitively, not independently re-audited against the entire original paper.
- **Imports:** source traversal from Main reached 42 project modules and no provider or frozen theorem. The ten frozen imports are Wave definitions (Coeff, CubicGrad, EllWeight, IsAnalyticTorusEmbedding, IsClassicalSolution, Lam, ReconU, ReconV, SineMode, WaveSpace), all SEALED. Probe-only LinearTorus is also SEALED. No draft-anchor dependency is hidden in this package.
- **Source defects:** no new suspected blueprint defect. Known `E-W-N-4` / N-4 is retained: P96-W p.278, second line of the u_tt display, prints “λ_j² q_j − √λ_j ⟨f(u),φ_j⟩” where the first term must be “−λ_j² q_j”, by q̇=λp and ṗ=−λq−∂G/∂q. This audit read the existing record at `docs/tracks/W/errata-check-W0.md:152` and W2:390–392; it did not freshly inspect the PDF page image. The package uses the corrected sign. The handoff's “None found” is read as no newly discovered defect, consistent with that carried erratum.
- **Scope limits:** no proof or seal of the full frozen theorem; no audit of the remaining KAM construction, density, frequencies or family injectivity. No claim that W6/W8 already produce the required C₃ or embeddings. No mathematical repair or deviation introduced.

## Verification receipts

All Lean-related commands ran serially with `LEAN_NUM_THREADS=1`; `nice -n 5` was used directly or by the prescribed wrapper. No heartbeat, recursion-depth or synthesis-budget override; no clean, update, cache fetch or package-directory changes.

1. Targeted build:

```sh
env LEAN_NUM_THREADS=1 /mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpi KAM.Wave.Recon2.Main
```

Exit 0. Output began `[inp-gate] slot 1 acquired 21:24:08 for KAM.Wave.Recon2.Main` and ended `Build completed successfully (3292 jobs).` Existing replay warnings: CubicSelect:159–160 deprecated `if_pos`/`if_neg` (four); CubicHeadline:70 unused `Real.rpow_two`; PdeForward:83 unused variable `z`. None comes from Recon2. This was an incremental targeted build over the existing slim overlay, not a clean rebuild.

2. Exact frozen-clause composition, fourth-root bridge and axioms:

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env lean .lake/abi-scratch/W2ReconAudit.lean
```

Exit 0; no probe errors or warnings. The first two examples above elaborated. The same file contained one `#print axioms KAM.Wave.<name>` for each of the 63 public theorem/lemma declarations (extracted from the five source files). Every output line was exactly of the form:

```text
'KAM.Wave.<name>' depends on axioms: [propext, Classical.choice, Quot.sound]
```

In particular the main results printed:

```text
'KAM.Wave.reconWave_functionals' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconWave_force' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.isAnalyticCoeffSolution_orbit' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconWave_curve' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconWave_main' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconWave_main_le' depends on axioms: [propext, Classical.choice, Quot.sound]
'KAM.Wave.reconWave_clause5' depends on axioms: [propext, Classical.choice, Quot.sound]
```

The declaration ledger enumerates all 63 checked names. None has sorryAx or a project-specific axiom.

3. Kernel replay (one invocation for all five modules):

```sh
env LEAN_NUM_THREADS=1 nice -n 5 lake env leanchecker --verbose KAM.Wave.Recon2.Functionals KAM.Wave.Recon2.Force KAM.Wave.Recon2.Orbit KAM.Wave.Recon2.Curve KAM.Wave.Recon2.Main
```

Exit 0; complete output:

```text
replaying KAM.Wave.Recon2.Main
replaying KAM.Wave.Recon2.Curve
replaying KAM.Wave.Recon2.Orbit
replaying KAM.Wave.Recon2.Force
replaying KAM.Wave.Recon2.Functionals
```

4. Slim-worktree lint:

```sh
env LEAN_NUM_THREADS=1 /root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpi
```

Exit 0. Complete output:

```text
check_lean_modules: PASS (1725 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
```

No generated-root exception or substantive lint failure was needed. This wrapper executes `nice -n 5 sh scripts/lint_sources.sh` with its prescribed ABI overlay.

5. Protected paths, formatting and module checks:

```sh
git diff inp...HEAD -- KAM/Frozen manifest KAM.lean README.md
git diff --check inp...HEAD
rg -n 'sorry|admit|axiom|unsafe|opaque|maxHeartbeats|maxRecDepth|synthInstance|EuclideanSpace' KAM/Wave/Recon2
```

Protected-path diff empty, exit 0; diff-check empty, exit 0; forbidden-token search empty, exit 1 (no matches). The allowed generated `KAM/Root/Wave.lean` delta is exactly the five Recon2 `public import` lines. Source line counts: Functionals=328, Force=103, Orbit=110, Curve=220, Main=127, all below 1500. Each has copyright, `module`, public imports, a module docstring and `@[expose] public noncomputable section`. Frozen manifest hash checks independently matched all eleven Wave definitions and all twelve nlw2 definition-closure paths.

## Closeout

Every assigned W2 definition/lemma/theorem has a premise-faithful export or the explicitly documented collection of exports. Literal frozen clause-(5) consumption, the common constant, endpoint behavior, fourth-root normalization, serial build, all public theorem axioms, five-module kernel replay and prescribed lint have been checked. The generated-root additions are authorized by AUDIT FOCUS; the auditor did not regenerate them. Only this report is a repository edit. W2-RECON is suitable for downstream assembly; full W-NLW2 remains FROZEN_UNPROVED.
