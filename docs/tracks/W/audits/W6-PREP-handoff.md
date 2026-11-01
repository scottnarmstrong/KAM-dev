# W6-PREP handoff (in progress)

Package W6-PREP (blueprint `blueprint-W/parts/w6-iteration.tex`, `bpW:w6`), worktree `/root/code/KAM-inp-wpl`,
branch `inp-wpn`. Off the frontier: source-faithful infrastructure used by several nodes; the dependency graph is
still being built. Modules under `KAM/Wave/Iteration/`, namespace `KAM.Wave`.

## Labels and declarations (so far)

| label | status | module | declarations |
|---|---|---|---|
| `sequences` | done | `Sequences` | `w6Tau`, `w6T`, `w6CF`, `w6C0`, `w6C2`, `w6Gamma0`, `W6SeqData` (+ `Valid`), `sigma`, `s`, `alpha`, `M`, `lam`, `eps`, `eta`, `r`, `q`, `dom`, `K0`, `K`, `Kprev`, `sInf`; `s_antitone`, `s_tendsto`, `sInf_le_s`, `sigma_le_min`, `lam_ge`, `one_le_K0`, `two_pow_le_K`, `eps_succ_eq_kappa` |
| `iter-lemma` | W5-free part only | `IterArith` | `w6Iter_q_bounds` (`q_ν ≤ γ₀2^{-ν}`, `q_{ν+1} ≤ q_ν/4`), `eta_le`, `eps_le_small` (W5 smallness), `eps_succ_le`, `lam_succ_le`, `lip_growth_le`, `M_growth_le`, `one_add_mul_one_add_rpow_le`, `div_arith`, `stepMF_eq`, `transf_arith` |
| `k0` | done in the inductive form | `K0` | `w6K0_of_increments` |
| `constants` | done | `Constants` | `w6S`, `w6SigmaP`, `w6S0`, `w6Sigma0`, `w6Tn`, `w6CFn`, `w6C0n`, `w6C2n`, `w6M`, `w6M0`, `w6Gamma1`, `w6Gamma`, `w6Theta`; signs and bounds `w6Gamma_pos`, `w6Gamma1_pos`, `w6Gamma_le_*`, `w6Gamma1_le_*`, `w6Theta_le`, `w6six_pi_gamma_le`, `w6eight_pi_gamma1_le`, `w6twentytwo_gamma_le`; prep-step arithmetic `w6prep_data_arith` (step `p-data`), `w6prep_size_arith` (step `p-size`) |
| `applicable` | arithmetic only | `Constants` | `w6applicable_arith` |
| `freq-lip` | constants clause only | `Constants` | `w6freqLip_consts` (`ε_ω, ε₁, ε₂ ∈ [0,α]`, `θ ∈ [0,θ₀]`) |
| W8 D1 | done | `Assembly/UpstreamW6` | `w8Upstream m hm : W8UpstreamConsts` (`γ`, `γ₁`, `c_F = stepCF 24`, `c^♮_F = stepCFn 24`), `w8SigmaP_eq_w6`, `w8Sigma0_eq_w6`, `w8M_eq_w6` |
| `convergence` (i) | done (generic in the frequencies) | `Params` | `w6Removed`, `w6PiSeq`, `w6PiStar`, `w6Convergence_params` (`Π_{-1}∖Π_* = ⋃ R^ν_{kl}`), `w6Zone_subset`, `w6PiSeq_measurableSet` (Borel), `w6PiSeq_antitone` |
| `exclusion` | done (generic family, D2-style) | `Params` | `w6_exclusion`, `w6_exclusion_seq` (levels `α_ν` with `α₀ = α̌`, thresholds `K_ν`) |
| `convergence` (ii)–(iv) | W5-free arithmetic only | `ConvArith` | `freq_sum_le`, `freq_lip_sum_le` (step `c-freq`), `ePhi`, `ePhi_eq`, `cauchy_sum_le`, `cauchy_tail_le`, `two_two_MF_eq` (step `c-cauchy`), `w6prod_le_two` (step `c-op`), `sum_inv_pow_Ico_le` |
| `convergence` (ii) | divisor limit (generic) | `Limits` | `w6_divisor_limit`, `tendsto_w6ZoneFun` |
| `final-freq` | conditional helper only | `Limits` | `w6FinalFreq_of_limits` (hypotheses: an admissible family, convergence of `ω_ν` on `S`, stage-wise `l = 0` conditions) |
| `freq-lip` | conditional helper (steps `fl-size`, `fl-lip`) | `FreqLip` | `w6IsFreqPair_of_bounds` (hypotheses: prep-step (ii) shift bounds and convergence (ii) drift bounds), `w6_lipcoef_omega`, `w6_lipcoef_Omega`, `w6AdmissibleFamilyOfPairs` |
| `wave-iteration` | W5-free data | `WaveData` | `w6QP`, `w6EtaP`, `w6EpsFlat`, `w6MFP`, `w6WaveSeq` (`s₀ = 7/64`, `r₀ = η_P r`, `α₀ = α̌`, `M₀ = 2M`, `ε₀`), `w6Etor`; `w6WaveSeq_valid`, `w6WaveSeq_small` (applicable, first clause), `w6EpsFlat_pos` |
| `prep-step` | arithmetic only (steps `p-data`, `p-step`, `p-size`, (v)) | `WaveData` | `w6QP_le`, `w6EtaP_le`, `w6prep_small` (W5 smallness, modified case), `w6SigmaP_le_min`, `w6prep_lam_le`, `w6prep_lip_growth`, `w6EpsFlat_eq`, `w6EpsFlat_le` (`ε^♭_0 ≤ γ₁α̌`), `w6lam0_le_lam`, `alpha_rpow_identity`, `w6C0n_ge` (`c^♮_0 ≥ 8`) |
| `to-w8` ("Starting size") | done | `WaveData` | `w6EpsFlat_div`, `w6MFP_eq`, `w6MFP_le`, `w6WaveSeq_ePhi`, `w6Etor_sharp_le` |
| `strong` | linear-algebra core only | `Strong` | `w6Strong_core` |
| `applicable` (`k = 0` clause) | conditional helper | `Applicable` | `w6applicable_k0_of_shift` (hypothesis: the prep-step (ii) shift bound `J|Ω̂_{P,J}| ≤ 3ε`) |
| `freq-lip` step `fl-borel` | done | `Params` | `w6PiMinus_measurableSet` |
