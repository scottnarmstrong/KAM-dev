# W5-MODIFIED handoff (track W, branch `inp-wpq`)

Package: blueprint lemma `bpW:w5:w4-modified` (`blueprint-W/parts/w5-kamstep.tex` lines 170-260), parts
(i)-(iii), all proof steps (`m-sup`, `m-other`, `m-lip`, `m-act`, `m-ass`, `m-const`), constants `B^♮_σ`, `b^♮(τ)`.
Status: **done** (no `sorry`, default heartbeats, every file < 600 lines). Only new files were created; no
existing file was edited.

## Files (all new)

| File | Content | Blueprint |
|---|---|---|
| `KAM/Wave/Homological/ModifiedDivisors.lean` | `HomMelnikovMod` (the hypothesis: `(H_α̂)` for every divisor of `bpW:w4:melnikov` except `δ^Q_{k,ij}`, `i≠j`, which only satisfy `bpW:w5:modified`); `homModRatio` (`ρ_j = ω_{a,p₊}(j+2)/ω_{a,p+1}(j+2) = (j+2)^{-c}`); twisted multipliers `homModDQ`, `homModDQt` (`ρ_i/(iδ^Q_{k,ij})`); gates `HomModMultBounds`, `HomModMultLip`; **`homModMultBounds_of`** (from `HomMelnikovMod`, `0 ≤ β ≤ p+1-p₊`), **`homModMultLip_of`** (from `HomFreqHyp`, `HomMelnikovMod`, `2β ≤ p+1-p₊`); `homModPP1`, `homMod_pb_le`, `homMod_beta_le` | hypotheses, steps `m-sup`, `m-lip` |
| `.../ModifiedReweight.lean` | `homModRho` (`D_ρ`, the inclusion `ℓ^N_{a,p+1} ⊂ ℓ^N_{a,p₊}` on representatives), `homReweight R` (`R ∈ 𝒯_s`, `p̄=p+1`, read with gradient weight `p₊`), invariance of entries/pairings/dual and bilinear norms, `homRval_reweight`, `homNhat_reweight`, `homXnorm_reweight_le`, `homFieldBound_reweight`, `homReweight_homSub` | step `m-other` |
| `.../ModifiedSolve.lean` | multiplier CLMs `homModTdp/Tdm/TP/TP'/TQ/TQt`, their norms and Lipschitz norms; `homModSolve_entry` (true entries of the twisted solve = scalar solves with `1/(iδ^Q)` of the `(p,p+1)` entries); **`homModSolveTaylor`** (the function `F ∈ 𝒯_{s-σ}` with gradient weight `p₊`, symmetry and transposition proved) | (i) class, step `m-sup` |
| `.../ModifiedAct.lean` | **`norm_homPartial_homSolve_le`** (`‖∂_{θ_i}𝒮u‖ ≤ 2πκB^W_σ m/α`), **`norm_homPartial_homSolve_sub_le`** (`≤ 2πκB^♮_σ(m^L+2Mm/α)d/α`), by termwise differentiation of the solved series | step `m-act` |
| `.../ModifiedBounds.lean` | `homModF_compBounds` (component bounds, `K = K_S`, `E₀ = B^W_σε/α`; `Q`-part of `∂_θF` by `m-act` in the operator norm `ℓ^N_{a,p} → ℓ^N_{a,p₊}`); **`homModLemma_fieldBound`** | (i) `|X_F|_{p₊,r} ≤ C₁B^W_σ ε/α̂` |
| `.../ModifiedLip.lean`, `.../ModifiedLipDeriv.lean` | component Lipschitz bounds (`b, c^±, P, P', Q, Q^T`, `∂a, ∂b, ∂c^±, ∂P, ∂P'` at scale `E^W`; `∂Q` by `m-act` at scale `E^♮`); `HomCompBounds_gen.mono_scale` | (ii), steps `m-lip`, `m-act` |
| `.../ModifiedLipField.lean` | `homModF_sub_compBounds`; **`homModLemma_lipschitz`**; **`homModLemma2`** (`λ`-form, `B^W ≤ B^♮ ≤ b^♮σ^{-(2τ+4)}`) | (ii), (iii), step `m-ass` |
| `.../ModifiedEq.lean`, `.../ModifiedEquation.lean` | entrywise equations (`homModEq_a/b/cp/cm/P/P'/Q`; `Q` via `homFamily_eq_two`, two functionals); `homModLemma_equation_fin`; **`homModLemma_equation_all`** (`L_N F + N̂ = R - â₀` on `T_{s-σ}×ℂ²×(ℓ^N_{a,p})²`) | (i) "the equation (ii) of W4 holds" |
| `.../ModifiedReal.lean` | `homModSolveTaylor_cp/cm/P/P'` (these components are the W4-type solves in the `p+1` spaces, read through `D_ρ`: "all other components as in W4"); **`homModLemma_zero_modes`**; **`homModSolveTaylor_isReal`** (+ `homReweight_isReal`); **`homMelnikovMod_of_melnikov`** (sanity: `(H_α)` implies the modified hypothesis for every `β ≥ 0`) | (i) |
| `KAM/Wave/KamStep/ModifiedStepSolve.lean` | `KamPhase` packaging for the step: **`stepSolveMod_fieldBound`**, **`stepSolveMod_fam`** (`|X_F|^λ_{r,D(s-σ,r)} ≤ (3C₁B^♮_σ/α̂)(ε+λε^L)` as `FamBound`), **`stepSolveMod_equation`** (`R + DN·ιX_F = N̂ + â₀` under the guard) | (i), (ii) for the consumer |

Part (iii) (`B^♮_σ ≤ b^♮(τ)σ^{-(2τ+4)}`, step `m-const`) was already `waveBN_le` (`KamStep/LatticeBN.lean`, W5-STEP);
it is re-exported in `homModLemma2`.

Part (iv) of W4 ("the bounds (iv) of Theorem `bpW:w4:lemma1` hold"): these bounds concern `ω̂, Ω̂, X_{N̂}` and
depend on `R` only; they are W4's `homNhat_coeff_bounds_gen`, `homNhat_fieldBound_gen`, `homNhat_lipschitz_gen`
applied verbatim to `R` (`p̄ = p+1`, so `sup_j (j+2)|Ω̂_j| ≤ ε`). No new Lean was needed.

## Design
* `F` is built from `R` (`p̄ = p+1`) and lives in `HomTaylor_gen a p p₊ (s-σ)`. The inclusion
  `ℓ^N_{a,p+1} ⊂ ℓ^N_{a,p₊}` commutes with the diagonal and the (untwisted) Hadamard multipliers, so
  `c^±, P, P'` are W4's solves of `homReweight R`; all W4 component lemmas (`homComp_first_gen`,
  `homComp_angle_gen`, solve lemmas) apply to `homReweight R`, whose field bound is `≤ ε` in the `p₊` norm.
* `Q, Q^T` are solved from `R.Q, R.Qt` (`p+1`-weighted matrices) with the twisted multipliers
  `ρ_i/(iδ^Q_{k,ij})`; `HomHadamardBound` with `A_k/α̂` holds because `ρ_I·min(I,J)^β ≤ 1` (`β ≤ c`), and the
  Lipschitz bound with `homLipC` because `ρ_I·min(I,J)^{2β} ≤ 1` (`2β ≤ c`) and `|i-j|² ≥ |i-j|`.
* Step `m-act` bounds `‖Λ∂_θQ_F‖_bil ≤ ‖∂_θQ_F‖ ≤ 2πK_SB^W_σε/α̂ ≤ 16πK_SB^W_σε/α̂`, so W4's assembly
  (`homXnorm_le_of_components_gen`, `C₁ = 7+10K_S`) applies unchanged.
* W4's lemmas are keyed to the gate `HomMultBounds` (which fails for the modified `Q` divisors), so the
  component/Lipschitz/equation proofs were transcribed for the gate `HomModMultBounds`; they are line-by-line
  W4's proofs with the new multipliers.

## Checks
* Builds (each through `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpq <Module>`, default
  heartbeats): `KAM.Wave.Homological.ModifiedDivisors`, `…ModifiedReweight`, `…ModifiedSolve`, `…ModifiedAct`,
  `…ModifiedBounds`, `…ModifiedLip`, `…ModifiedLipDeriv`, `…ModifiedLipField`, `…ModifiedEq`,
  `…ModifiedEquation`, `…ModifiedReal`, `KAM.Wave.KamStep.ModifiedStepSolve` — all `Build completed
  successfully` (last: `✔ [3344/3344] Built KAM.Wave.KamStep.ModifiedStepSolve`).
* `#print axioms` (all main declarations): `homModMultBounds_of`, `homModMultLip_of`, `homModLemma_fieldBound`,
  `homModLemma_equation_all`, `homModLemma_zero_modes`, `homModSolveTaylor_isReal`, `homModSolveTaylor_cp`,
  `homModSolveTaylor_P`, `homModLemma_lipschitz`, `homModLemma2`, `waveBN_le`, `stepSolveMod_fieldBound`,
  `stepSolveMod_fam`, `stepSolveMod_equation`, `homMelnikovMod_of_melnikov`, `norm_homPartial_homSolve_le`,
  `norm_homPartial_homSolve_sub_le`: each `depends on axioms: [propext, Classical.choice, Quot.sound]`.

## Deviations (none strengthen a hypothesis)
* Generality: `a, p ≥ 0` (blueprint `a = p = 1`); only `0 ≤ β` is used (blueprint `β ∈ (0,1/2]`); of
  `p₊ ∈ [p+½, p+1]` only `p ≤ p₊` and (from `β ≤ p+1-p₊`) `p₊ ≤ p+1` are used. The equation needs `1 ≤ p+p₊`
  (carrier of `L_N`) and, in the `DN` form, W4's guard `HomGuard a p γ`; both hold for `a = p = 1`
  (`homGuard_one_one`), exactly as in W4/W5-STEP. `M > 0` is used only for the `λ`-form.
* `HomMelnikovMod` lists the divisor bounds individually (`δ⁰`, `δ^±`, `δ^P`, `δ^{P'}`, `δ^Q_{k,jj}` with
  `k≠0`, and the modified `δ^Q_{k,ij}`, `i≠j`); the field `dQd` duplicates `d0` (`δ^Q_{k,jj} = δ⁰_k`) and is kept
  to mirror "every divisor of `bpW:w4:melnikov`".
* `(min(i,j)+2)^β` is `Real.rpow`; `ρ_j = (j+2)^{p₊-p-1}` (`homModRatio_eq`).
* "`Q_F, Q_F^T` bounded `ℓ^N_{a,p} → ℓ^N_{a,p₊}`" is the type (`p₊`-weighted matrices in `HomOp`) plus the bound
  `‖Q_F‖ ≤ K_SB^W_σε/α̂` (`homModF_compBounds`).

## Blueprint defects
None found. Steps `m-sup`, `m-lip`, `m-act` (including the exact constants `2πK_SB^W_σ/α̂` and
`2πK_SB^♮_σ(ε^L+2Mε/α̂)/α̂`) and `m-ass` go through as written.

## Design signals
None: every module elaborates at default heartbeats in < 15 s.

## Lint
`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpq` after regenerating the root
(`python3 scripts/gen_root_imports.py`, committed: `KAM/Root/Wave.lean`, +56 lines, of which 12 are the new
Modified modules and the rest W5-STEP modules missing from the snapshot root). Tail:
```
check_lean_modules: PASS (3683 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (177 frozen declarations of KAM; ...)
```
**Exit status 1**, solely from the stage "Lean lines over 100 characters": 66 lines, all in pre-existing
W5-STEP files of the `84141b69` snapshot (`KamStep/HoloFderiv.lean`, `NewHam*`, `ParamIntegral.lean`,
`PullbackAbstract.lean`, `Step*.lean`, `Taylor*.lean`; already noted as "to be wrapped" in
`W5-STEP-handoff.md`). None is in a W5-MODIFIED file (all new files have lines ≤ 100). This package was
instructed not to edit existing files (the other W5 prover owns them), so they were left untouched; wrapping
them in the W5-STEP worktree (or at landing) makes the lint exit 0. Every other lint stage passes.
