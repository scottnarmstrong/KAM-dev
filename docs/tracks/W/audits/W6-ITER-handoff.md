# W6-ITER handoff

Package W6-ITER (blueprint `blueprint-W/parts/w6-iteration.tex`, `bpW:w6`), worktree `/root/code/KAM-inp-wpr`,
branch `inp-wpr` (base `d3a1a47f`: W6-PREP + W8-PREP merged with `inp` (W3, W4, W7-MEASURE) and W5-STEP
`inp-wpj@5e45b8b0`). Off the frontier: source-faithful infrastructure used by several nodes; the dependency graph
is still being built. New modules under `KAM/Wave/Iteration/`, namespace `KAM.Wave`. Nothing under
`KAM/Wave/KamStep` was edited; no `KamStep/Real*` file was created. No `sorry`, `axiom`, `admit`, `opaque`,
`unsafe`, no `maxHeartbeats` or other budget override. Largest new file 413 lines (`ConvFreq`); new code 2390
lines. No frozen file, provider or frozen theorem anchor is imported or edited. `KAM/Root/Wave.lean` regenerated
by `scripts/gen_root_imports.py` (not hand-edited).

## STEP 0 (rebuild on this base)

All of `KAM/Wave/Iteration/*` (W6-PREP) and `KAM/Wave/Assembly/*` (W8-PREP) rebuild on this base. Only
`Assembly/ShellGeom.lean` needed a repair: W7's `shellInner` is now `{I ∈ R_k | a < infDist I R_kᶜ}` (W7-FIX), so
`w8Pi_subset_shellInner` (now definitional) and `shellInner_subset_w8Pi_of_lt` (`hab.trans`) were re-proved with
unchanged statements. The W5 API change (`StepHyp` built on `StepCore`) broke nothing in W6-PREP (it only reads
W5's constants). W8-PREP interface defect 1 (W7 inner shell vs W8 trimmed shell) is resolved by W7-FIX:
`shellInner (1/2) t₀ n α_n = Π_n` definitionally.

## Files

| module | lines | content |
|---|---|---|
| `Iteration/Bridge` | 132 | W7 ↔ W5 normal-mode index; `W6Mel` (the conditions `(bpW:w6:melnikov)`); `(bpW:w6:melnikov) ⇒ HomMelnikov 24` |
| `Iteration/Stage` | 220 | hypotheses of `iter-lemma` at stage `ν`; W5's `StepHypSrc` at stage `ν`; the stage objects |
| `Iteration/IterLemma` | 349 | `iter-lemma` |
| `Iteration/Sequence` | 236 | the iteration (`W6State`, `w6Seq`), `W6ConvHyp`, stage 0, step `c-ind` |
| `Iteration/ConvFreq` | 413 | `convergence` (i), (ii) for the iteration outputs |
| `Iteration/PrepMel` | 290 | `prep-step` (i): Ξ-complement ⇒ W5's modified conditions |
| `Iteration/PrepStep` | 278 | `prep-step` (W5's modified step on `Π ∖ Ξ`, clauses (ii)–(v)) |
| `Iteration/WaveInst` | 267 | `wave-iteration`, `applicable`; freq-pair helper at shift weight `J^{1/2}` |
| `Iteration/FreqInst` | 205 | wave instances of `freq-lip`, `exclusion`, `final-freq` |

## The two W5 dependencies (hypotheses of the conditional helpers)

* `W6StepReal` (`IterLemma`): W5's reality clause for `P_+`, unmodified case, for `a = p = 1`, `p_+ = 3/2`,
  `τ = 24`, `γ_G = w6GamG`. Exactly the second conjunct of `stepTheorem_reality` (branch inp-w5r,
  `KamStep/RealStep.lean`): once landed, `fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ H _ => (stepTheorem_reality H).2`.
* `W6StepRealMod` (`WaveInst`): the same for `StepHypMod` with `β = 1/4`
  (`(stepTheoremMod_reality H).2`).

The iteration applies W5's step at every stage, which needs `P_ν` real (`StepHypSrc.hreal`); so every statement
about the whole iteration (convergence and the wave instances) is a conditional helper on these clauses. Each
helper has the suffix `_of_stepReal` / `_of_stepRealMod`, assumes only these W5 clauses (stated for arbitrary step
data, never for the W6 objects), and does not stand in for a label (AGENTS rule 6). Instantiating them is a
one-line change per helper once inp-w5r lands.

## Labels and declarations

| label | status | declarations |
|---|---|---|
| `iter-lemma` | **done, except the reality of `P_{ν+1}`** (W5 reality clause) | `Bridge`: `w6Om7`, `w6L7`, `W6Mel`, `w6_homMelnikov_of_mel` (`bpW:w4:wave` (ii)), `inZ_w6L7`, `japL_w6L7`, `linF_w6L7`, `l1Norm_w6L7`, `kAk_eq_waveA`; `Stage`: `W6StageCore`, `W6Stage` (hypotheses at stage `ν`), `W6Stage.stepHyp` (W5's `StepHypSrc` with `s_ν, σ_ν, η_ν, r_ν, α_ν, λ_ν, ε_ν`, step `il-small`), objects `W6Stage.{omN, OmN, PhiN, PN, XN, PiN}`; `IterLemma`: **`W6Stage.w6IterLemma`** (bundle: `q` bounds; `Φ_{ν+1} : D_{ν+1} → D(s_ν-4σ_ν, 2η_νr_ν) ⊆ D_ν`; given the `k = 0` conditions at `ν+1` (`W6Mel0`), all hypotheses at `ν+1` except reality (`W6StageCore`); `|Φ-id|^λ ≤ 2M_F`, `|DΦ-I|^λ ≤ 16M_F/σ ≤ 2^{-ν-2}`; `ω`, `Ω` increments), `phiN_mapsTo`, `next_core`, `phiN_bounds`, `omN_inc`, `OmN_inc`, `OmN_inc_abs`, `w6_mel_perturb` (step `il-div` with the Dirichlet weight), `w6_newerror_eq`; helper `next_stage_of_stepReal` |
| `k0` | done in W6-PREP; **used along the iteration** | `Sequence`: `w6Seq_k0` (unconditional given the earlier stages) |
| `convergence` (i) | **conditional on `W6StepReal`** | `Sequence`: `W6State` (`Pi, om, Om, P, X`), `W6State.{next, phi, w6Stage, Std, w6next_eq, phi_eq, next_Pi_subset}`, `w6Seq`, `w6Seq_Pi_antitone`, `W6ConvHyp`, `w6Pi0`, `w6Start`, `w6Start_stage` (stage 0, unconditional), helper `w6Seq_stage_of_stepReal` (step `c-ind`); `ConvFreq`: `w6PiStarIt`, helpers `w6Seq_Pi_eq_of_stepReal`, `w6PiStarIt_eq_of_stepReal`, `w6ConvParams_of_stepReal` (`Π_{-1}∖Π_* = ⋃_ν⋃_{\|k\|>K_{ν-1}} R^ν_{kl}`), `w6ConvBorel_of_stepReal` |
| `convergence` (ii) | **conditional on `W6StepReal`** | `ConvFreq`: `w6_uniform_limit` (unconditional), `w6OmStar`, `w6OmStar7`, `w6_continuousOn_of_lip`, helpers `w6Seq_om_inc`, `w6Seq_Om_inc`, `w6Seq_om_partial`, `w6Seq_Om_partial` (the bounds for `(ω_ν, Ω_ν)` on `Π_{ν-1}`), `w6Seq_om_limit`, `w6Seq_Om_limit`, **`w6ConvFreq_of_stepReal`** (uniform convergence on `Π_*`, `\|ω_*-ω_0\| ≤ 8πε₀`, Lipschitz `≤ 64πε₀/λ₀`, `sup_j (j+2)^{1/2}\|Ω_*-Ω_0\| ≤ 4ε₀`, Lipschitz `≤ 16ε₀/λ₀`, divisors `≥ (α₀/2)⟨l⟩/A_k` on `Π_*`) |
| `prep-step` | **done with two W5-interface deviations (D2, D3); reality of `Φ_P`, `P_0` pending** | `PrepMel`: `w6_prep_divisors` ((i), step `p-div`), `w6_prep_single`, `w6_prep_sum`, `w6_prep_diff`, `w6_prep_zero`, `waveFreqNor_eq_omegaNor`, `waveFreqTan_eq_omegaTan`, **`w6_homMelnikovMod_of_prep`** ((i): W5's `(bpW:w5:modified)`, `β = 1/4`, level `α̂`); `PrepStep`: `W6PrepHyp` (hypotheses), **`W6PrepHyp.stepHyp`** (W5's `StepHypModSrc`: the step applies, steps `p-data`, `p-div`), objects `W6PrepHyp.{om0, Om0, PhiP, w6P0, X0}`, `shift_omega`, `shift_Omega`, `freq0` ((ii)), `phiP_bounds` ((iii)), `w6size` ((iv), (v): `ε^♭_0 ≤ γ₁α̌`, `λ_0`-norm), `w6BB`, `w6_abs_waveB_le` |
| `wave-iteration`, `applicable` | **conditional on `W6StepRealMod`** (reality of `P_0`); all other hypotheses proved | `WaveInst`: `W6StepRealMod`, `w6applicable_k0_of_shift_half`, `W6PrepHyp.waveConv_parts` (unconditional), `W6PrepHyp.waveSeq_lam_zero`, helper **`W6PrepHyp.w6Applicable_of_stepRealMod`** (`W6ConvHyp` for every `ε₀ ∈ [ε^♭_0, γ₁α̌]`) |
| `freq-lip` (wave instance) | **conditional on both clauses; deviation D4** | `WaveInst`: `w6IsFreqPair_of_bounds_half`; `FreqInst`: `W6PrepHyp.{waveSeq, waveD, waveD_mem, waveD_subset, waveD_meas, w6wavePair}`, helper **`w6WaveFamily_of_stepReal`** (W7 `AdmissibleFamily`, `D_ν = Π_{ν-1}`, `K_ν`) |
| `exclusion` (wave instance) | **conditional on both clauses** | `FreqInst`: `W6PrepHyp.wavePiStar`, helper **`w6Exclusion_of_stepReal`** (`Π ∖ Π_* ⊆ ℰ`) |
| `final-freq` (wave instance) | **conditional on both clauses** | `FreqInst`: helper **`w6FinalFreq_of_stepReal`** |

## Labels not done, and why

* `convergence` (iii) (transformations on the torus: uniform convergence of `Φ^ν∘ι`, holomorphy, periodicity,
  reality, joint continuity, the bound `e_Φ`) and (iv) (operator bounds, symplecticity, `DΦ^ν` onto `𝒫^{p_+}`).
  The ingredients available here: `phiN_bounds` (`|DΦ_{ν+1} - I| ≤ 2^{-ν-2}` in `|·|_{r_ν}`), `phiN_mapsTo`,
  `w6prod_le_two`, `cauchy_tail_le` (W6-PREP), `W6State.phi`. Missing: the reality of `Φ_{ν+1}`
  (`stepTheorem_reality` (1), inp-w5r), `DΦ` onto `𝒫^{p_+}` (`stepTheorem_dPhi_smooth_onto`, inp-w5r), and a large
  amount of new work (compositions `Φ^ν` across the spaces `StepPhase r_μ`, chain rule, mean-value Cauchy step,
  W1's uniform-limit lemma for holomorphy). Recommended as its own package once inp-w5r lands.
* `strong` (as stated): needs W5's fields valued in `𝒫^{p-1}` and the weight-`(p-1)` pairing (inp-w5r commit 3:
  "field `X_N`, Riesz representation of `DN`, weak conjugacy in field form"); only W6-PREP's `w6Strong_core`.
* `invariance`: needs `strong`, the weak conjugacy in field form (inp-w5r) and `convergence` (iii), (iv).
* `tori`: needs all of the above, and W5's `bpW:w5:action-angle`, `bpW:w5:initial`, which have no Lean statement.
* W8-PREP re-check (`patch-cont`, `nu-injective`, `injective`): they need W8's `freq-shell` and `shell-inv`
  (W8's per-shell application of W6, plus `shell-iter`), which do not exist; not cheap. The W8-PREP conditional
  helpers (`*_of_pieces`) are unchanged and still build.

## Deviations (none strengthens a source hypothesis)

* **D1** (`iter-lemma`): the conclusion "all hypotheses hold at stage `ν+1`" is proved except the reality of
  `P_{ν+1}` (W5's reality clause, pending); the full stage `ν+1` is the conditional helper
  `next_stage_of_stepReal`. W5's `(bpW:w5:freq)` constants: `M_ω` is enlarged to `M_ν - M_Ω` (Lipschitz constants
  may be enlarged) so that `λ_ν = α_ν/(M_ω + M_Ω)` exactly; the tail constant `M₀` and the splitting `ε₀ + λε₁ ≤ ε`
  are chosen (`Classical.choose`) from the stage hypotheses. Normal modes use W7's index (`n : ℕ`, label
  `n + 3`); `w6Om7 Ω n = Ω (n+1)` converts W5's (`j : ℕ+`, label `j + 2`).
* **D2** (`prep-step` (ii)): W5's `stepTheoremMod` (iii) bounds the normal shift with the weight `(j+2)^{p_+-p} =
  J^{1/2}`, not `J` as the blueprint's (ii) states (blueprint: "with `p̄ - p = 1`"). The `J`-weighted bound needs
  the shift of W5's Taylor family at `p̄ = p+1` (`StepHypMod.R1`) to equal that of the reweighted family used by
  the core, which W5 does not expose. Proved: `shift_Omega` with `J^{1/2}`. **W5 interface defect** (report).
* **D3** (`prep-step` (iii)): W5's clause (v) gives `|Φ_P - id|^λ ≤ 2M_{F,P}`; the blueprint's sharper sup bound
  `M_{F,P}` (step `f-flow` of `bpW:w5:flow`) is not exposed by `stepTheoremMod`. Proved: `phiP_bounds` with
  `2M_{F,P}`. This doubles the `M_{F,P}` part of `e_tor` in `tori` (iv) / W8's `etor`. **W5 interface defect.**
* **D4** (`freq-lip`): by D2 the normal shift `3εJ^{-1/2}` enters `ε₂`: constants `ε_ω = 6πγα + 8πε₀`, `ε₁ = 0`,
  `ε₂ = 3γα + 4ε₀` (both `≤ α`), `θ` unchanged. W7's measure estimate holds for every admissible family, so W8's
  use is unaffected; the blueprint's `ε₁ = 3γα`, `ε₂ = 4ε₀` are recovered once D2 is fixed (W6-PREP's
  `w6IsFreqPair_of_bounds` then applies verbatim).
* **D5** (`applicable`, `k = 0`): proved from the `J^{1/2}`-weighted shift (`w6applicable_k0_of_shift_half`:
  `|⟨l, Ω̂⟩| ≤ 6ε ≤ β_*`), instead of W6-PREP's `J`-weighted helper.
* **D6** (`convergence`): the parameter sets are W6-PREP's `w6PiSeq` of the output frequencies
  (`w6Seq_Pi_eq_of_stepReal`); `Π_* = ⋂_ν Π_ν` (`w6PiStarIt`). `ω_*`, `Ω_*` are `limUnder` of the sequences
  (defined for all `ξ`, meaningful on `Π_*`). The iteration `w6Seq` applies the step only when the stage
  hypotheses hold (`W6State.next` is the identity otherwise); along the iteration they always hold
  (`w6Seq_stage_of_stepReal`).

## Blueprint remarks

1. `bpW:w6:iter-lemma`, step `il-div`: the Dirichlet-weighted Melnikov conditions at stage `ν+1` cannot be taken
   from W5's `stepTheorem` (iv), which concludes with P96-K's bracket (weaker); they follow directly from the
   frequency increments and the stage-`ν` conditions (`w6_mel_perturb`), with the same arithmetic
   (`div_arith`). No change of statement.
2. `bpW:w6:prep-step` (ii), (iii): see D2, D3 (W5 interface, not a blueprint error).
3. No wrong statement found.

## Checks

* Gate build (one module per call, import order):
  `/root/code/KAM-inp/.drafts/W/w_build.sh /root/code/KAM-inp-wpr KAM.Wave.Iteration.{Bridge,Stage,IterLemma,Sequence,ConvFreq,PrepMel,PrepStep,WaveInst,FreqInst}`:
  every module `Build completed successfully` (last: `FreqInst` 3476 jobs); no error, no warning in the new files.
  STEP 0: `KAM.Wave.Iteration.{Sequences,…,Applicable}` and `KAM.Wave.Assembly.{Ext,Unique,Winding,Consts,ShellGeom,
  ShellData,Patch,NuInj,UpstreamW6}` all `Build completed successfully` (`UpstreamW6` 3451 jobs).
* `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpr`: **exit 0**; tail
  `check_lean_modules: PASS (3888 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`,
  `ABI HASHES OK (177 frozen declarations of KAM; …)`.
* `python3 /mnt/HC_Volume_106379410/orchestrator-tools/main_shortname_check.py /root/code/KAM-inp-wpr` on the nine
  new modules and `Assembly.ShellGeom`: `short-name check OK (no reused public short name)`, exit 0.
* `#print axioms` (scratch file via `w_lean.sh`): `W6Stage.w6IterLemma`, `W6Stage.next_stage_of_stepReal`,
  `w6_homMelnikov_of_mel`, `w6Seq_stage_of_stepReal`, `w6ConvFreq_of_stepReal`, `w6ConvParams_of_stepReal`,
  `w6ConvBorel_of_stepReal`, `w6_uniform_limit`, `W6PrepHyp.stepHyp`, `W6PrepHyp.w6size`, `W6PrepHyp.freq0`, `W6PrepHyp.shift_Omega`, `W6PrepHyp.phiP_bounds`, `w6_homMelnikovMod_of_prep`,
  `W6PrepHyp.w6Applicable_of_stepRealMod`, `W6PrepHyp.w6WaveFamily_of_stepReal`,
  `W6PrepHyp.w6Exclusion_of_stepReal`, `W6PrepHyp.w6FinalFreq_of_stepReal`, `w6IsFreqPair_of_bounds_half`, `w8Pi_subset_shellInner`,
  `shellInner_subset_w8Pi_of_lt`: all `[propext, Classical.choice, Quot.sound]`.

## Design signals

None: every module elaborates at default heartbeats in seconds under the 4 GB cap.
