# Handoff W1-CUBIC (branch inp-wph)

Modules (all `KAM/Wave/Cubic/`, namespace `KAM.Wave`, 17 files, 2929 lines, each file < 310 lines; no heartbeat or
recursion overrides, no `sorry`, no axiom). Built on the landed W0-ANALYSIS (`KAM/Wave/Normal/Analysis/*`) and
W1-SEQ/W1-ALGEBRA/W1-ANALYTIC; `inp` merged (already up to date at start). Statements are over `[RCLike K]`
(covers `K = ℝ, ℂ`) wherever the blueprint says `𝕂 ∈ {ℝ, ℂ}`.

Import graph: SelectionCore → SelectionOneSided → TriSeq → TriLp → TriML → TriProps → CubicMap → {CubicDeriv,
FrozenForm → GradIdentity → GradLp → HamHamiltonian; FrozenForm → HamField → HamHamiltonian};
SelectionCore → SelectionTwoMaj → SelectionTwoSided → SelectionTwoFinal; SelectionOneSided → ReconComplex.

## Labels proved -> Lean declarations

### `bpW:w1:selection`
- (a) one-sided: `waveSel_oneSided` (a ≥ 0, p ≥ 1/2, M ≥ 0; hypothesis `‖c i j k l‖ ≤ M * (i*j*k*l)^(-1/2) *
  waveSelCount l (i,j,k)`; conclusions: absolute convergence of every triple sum, `IsEll a (p+1) (waveSelSum c q q' q'')`,
  `ellTsumNorm a (p+1) T ≤ 2 M K_s² ∏ ellTsumNorm a p ·`, `K_s = waveAlgConst (p+1/2)`). Helpers: `waveSel_norm_step`,
  `waveTripleConv_weighted`, `waveEvenAbs_weighted_eq` (SelectionCore). Defs `waveSelCount`, `waveSelSum`.
- (b) two-sided: `waveSel_twoSided` (hypothesis for nonzero indices only; `waveSelCountZ`; `T_c(·)_0 = 0` via
  `waveSelTwo`; constant `64 M K_s²`, exactly as in the blueprint). Helpers `waveTwoMaj`, `waveTwoMaj_weighted`
  (`‖x̃‖_{a,s} ≤ 2‖w‖_{a,p}`), `waveSelSumZ_pointwise` (reindexing `(ℤ∖0)³ ≃ {±}³ × ℕ+³`, `waveSignZEmb`, reusing the
  landed `wave_selection_sum_le`).
- trilinearity / symmetry of `T_c` (generic `c`, one-sided): `waveSelSum_smul_left/_mid/_right`,
  `waveSelSum_add_left/_mid/_right` (with the absolute-convergence summability hypotheses), `waveSelSum_swap_left_mid`,
  `waveSelSum_swap_mid_right`.

### `bpW:w1:trilinear` (and the complex clause of `bpW:w0n:cubic-bound`)
- coefficients `waveTriCoef` (= `g_{ijkl}(λ_iλ_jλ_kλ_l)^{-1/2}`), selection bound `waveTriCoef_bound` (`M = 1/(2π)`),
  sums `waveTriSeq`; exact bound over any `RCLike K`: `waveTri_oneSided` (`‖T‖_{a,p+1} ≤ C_* ∏‖·‖_{a,p}`,
  `C_* = waveCubicConst p = K_{p+1/2}²/π`). Link to the real W0 map: `waveTrilinear_eq_waveTriSeq`.
- (i) `waveTriML` (`ContinuousMultilinearMap K (fun _ : Fin 3 => lp _ 2) (lp _ 2)`), `waveTriML_norm_le` (≤ C_*),
  `coeffW_waveTriML` (defining property), `waveTriML_unique` (uniqueness), symmetry `waveTriML_swap_left_mid`,
  `_mid_right`, `_left_right`, and all permutations `waveTriML_perm` (CubicDeriv). Lp-level: `waveTriAux*`, `waveTriCoords*`.
- (ii) real structure: `waveTriML_complexify` (𝒯_ℂ(ιy,…) = ι 𝒯_ℝ(y,…)), `waveTriML_conj`.
- (iii) compatibility: `waveTriML_embed` (with `embedCLM`).
- (iv) frozen identification: `cubicGrad_eq_triML_div` (`cubicGrad y l = 𝒯^{1,1}_ℝ(y,y,y)_l / ω_{1,2}(l)`),
  general `waveCubic_coeffW_eq_coeffW_triML` (`𝒢(κ_{a,p} y) = κ_{a,p+1} 𝒯^{a,p}_ℝ(y,y,y)`, `a > 0`).

### `bpW:w1:cubic-analytic`
- `waveCubicNL` (= 𝒩), (i) `waveCubicNL_analyticOnNhd` (K-analytic on all of ℓ²_K), `waveCubicNL_norm_le`;
  (ii) `waveCubicNL_hasFDerivAt` / `waveCubicNL_fderiv` (`D𝒩(y)h = 3𝒯(y,y,h)`), `norm_fderiv_waveCubicNL_le`
  (`≤ 3C_*‖y‖²`), `waveCubicNL_second_apply` / `waveCubicNL_second_norm_le` (`D²𝒩(y)(h,k) = 6𝒯(y,k,h)`, norm
  `≤ 6C_*‖y‖‖h‖‖k‖`, in the directional form `fderiv (fun y' => fderiv 𝒩 y' h) y k`), `waveCubicNL_third_apply`
  (`iteratedFDeriv K 3 𝒩 y = 6 • 𝒯`); (iii) `waveCubicNL_sub_le`; (iv) `waveGw` (= 𝒢^w), `waveGw_apply`
  (`𝒢^w(y)_l = ω_{1,2}(l)·cubicGrad y l`), `waveGw_norm_le` (`C_m = waveCubicHeadlineConst`), `waveGw_analyticOnNhd`,
  weighted coordinates `coeffW_one_two_waveGw`, `waveGw_weighted_one_one`, `waveGw_weighted_one_zero`.

### `bpW:w1:gradient-identity`
- (i) `waveG_hasSum_pairing` (`G(q) = ¼ Σ_l q_l 𝒢(q)_l` abs. conv.), `waveG_coeffW_eq_inner`
  (`G(κ_{a,p}y) = ¼ ⟨D_ρ 𝒩(y), y⟩_{ℓ²}`, `ρ_l = 1/(ω_{a,p+1}ω_{a,p})`).
- (ii) `waveG_coeffW_analyticOnNhd`, `waveG_coeffW_hasFDerivAt` (`DG^w(y) = ⟨D_ρ𝒩(y), ·⟩`),
  `waveG_coeffW_fderiv_apply` (`DG^w(y)h = Σ_l 𝒢(q)_l (κ_{a,p}h)_l = ⟨𝒢(q), κ_{a,p}h⟩₀`).
- (iii) frozen form: `waveG_frozen_fderiv_apply` (`DG^w(y)h = Σ_j cubicGrad y j · coeff h j`),
  `waveGradW_one_one_apply` (`∇G^w(y)_j = 𝒢^w(y)_j/(ω_{1,1}(j)ω_{1,2}(j))`).

### `bpW:w1:hamfield`
- (i) `waveXLam` (+ `coeffW_waveXLam_fst/_snd`, `norm_waveXLam_le` ≤ √(1+m), `not_exists_bounded_waveXLam`).
- (ii) `waveXG` (K-analytic `waveXG_analyticOnNhd`, `waveXG_norm_le`, Lipschitz `waveXG_sub_le`, complex extension
  `waveXG_complexify`). (iii) `waveXH` (`waveXH_analyticOnNhd`, coordinates `coeffW_waveXH_fst/_snd`).
- (iv) Hamiltonian structure: `waveLamQuad`, `waveHw`, `waveHw_analyticOnNhd`, `waveHw_hasFDerivAt`,
  `waveHw_fderiv_p` (`DH(0,e_j) = λ_j p_j`), `waveHw_fderiv_q` (`DH(e_j,0) = λ_j q_j + 𝒢(q)_j`), `e_j = ω_{a,p}(j)δ_j`.
- (v) frozen form: `waveXw` (`X^w(y,y') = (Dy', -Dy - S²𝒢^w(y))`), `waveXw_analyticOnNhd`,
  `coeffW_one_zero_waveXw_fst/_snd` (coordinates `ω_{1,0}(j)(λ_j coeff y' j, -λ_j coeff y j - cubicGrad y j)`).

### `bpW:w1:coordinatewise` — X^w specialization closed
- `frozen_invariance_iff_waveXw`: for `Kmap` differentiable at θ, the coordinatewise form of frozen conclusion (4) holds
  iff `(ι̂ (DK(θ)ν).1, ι̂ (DK(θ)ν).2) = X^w(K θ)`; proved by `KAM.Wave.frozen_invariance_iff` with `v := X^w(K θ)`.

### `bpW:w0n:recon-bounded`, complex-carrier clause (scope ruling)
- `waveEllK_summable_pow_mul`, `waveEllK_tsum_pow_mul_le` (`Σ ‖c_j‖ j^k ≤ M_{a,p,k}‖c‖_{a,p}`), `waveSineSeriesK`,
  `waveSineSeriesK_norm_le` (`≤ √(2/π) M ‖c‖`), `waveSineSeriesK_add/_smul`, `waveSineSeriesK_tendstoUniformly`,
  `hasDerivAt_waveSineSeriesK`, `contDiff_waveSineSeriesK`, `iteratedDeriv_waveSineSeriesK`,
  `waveSineSeriesK_zero_apply`, `waveSineSeriesK_pi`, `integral_waveSineSeriesK_mul_sineMode` (all over `RCLike K`).

## Labels / parts NOT done (honest list)
1. `gradient-identity` (i): the symmetric continuous 4-linear form `𝒬` is not packaged (neither its symmetry nor the bound
   `|𝒬| ≤ C_*∏‖q_i‖`). What is proved is the identity `G = ¼ ⟨𝒢(q), q⟩₀ = ¼ ⟨D_ρ𝒩(y), y⟩` and the analyticity/derivative
   of `G` (via the `ℓ²` pairing, not through `𝒬`). Symmetry of `𝒬` needs a Fubini over `ℕ+⁴` that I did not write.
   (iii) remark that `𝒢(q)` is not the Riesz gradient for the `ℓ^{a,p}` inner product is not stated separately (the `ℓ²`
   gradient formula is).
2. `selection`: trilinearity/symmetry of the TWO-sided `T_c` is not stated (one-sided: done).
3. `cubic-analytic` (ii): `D²𝒩` is stated in directional form (`fderiv (fun y' => fderiv 𝒩 y' h) y k`), not as a bundled
   `fderiv (fderiv 𝒩)`.
4. `hamfield` is stated in the weighted `ℓ²` coordinates of the realization table (maps `ℓ² × ℓ² → ℓ² × ℓ²`), with
   `E_{a,p}` identified through `coeffW`; `bpW:w1:hamfield` (i) "not bounded `E_{a,p} → E_{a,p}`" is the landed
   `not_exists_bounded_lam_pow` re-exported for the multiplier `λ_j` (`not_exists_bounded_waveXLam`).
5. complex `recon-bounded`: boundedness into `C^k` is stated as the sup bound for every derivative order plus linearity
   (as in the W0-ANALYSIS real version; no bundled `C^k` norm space). The "in particular" sentence (`U_m`, `V_m`,
   `q ↦ U_m(λq)` for every `p`) is not restated over `ℂ`; its ingredients are `lamMul`/`norm_lamMul_*` (landed W1-SEQ)
   and the declarations above.
6. Duplication note: the real `wave_trilinear_bound` (W0-ANALYSIS) was not refactored onto `waveSel_oneSided`; the generic
   statement re-proves the weighted norm chain once (reusing `wave_selection_sum_le`, `w0a_convAlgebra_nonneg`, `waveConv`
   algebra), and `waveTrilinear_eq_waveTriSeq` ties the two maps together. A later cleanup could derive the real bound from
   `waveTri_oneSided` and delete `CubicBound`'s second half.

## Checks
- Gate: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wph` with all 17 `KAM.Wave.Cubic.*`
  modules -> tail `Build completed successfully (3307 jobs).`
- `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wph`: exit 0; tail `check_lean_modules: PASS (1726 Lean files, 0
  comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (158 frozen declarations)`.
- `main_shortname_check.py` on all Cubic modules: `short-name check OK (no reused public short name)`.
- `KAM/Root/Wave.lean` regenerated with `scripts/gen_root_imports.py` and committed (no hand edits).
- `#print axioms` of 37 main declarations (`waveSel_oneSided`, `waveSel_twoSided`, `waveTri_oneSided`, `waveTriML_norm_le`,
  `waveTriML_unique`, `waveTriML_complexify`, `waveTriML_conj`, `waveTriML_embed`, `waveTriML_perm`, `cubicGrad_eq_triML_div`,
  `waveCubic_coeffW_eq_coeffW_triML`, `waveCubicNL_analyticOnNhd`, `waveCubicNL_hasFDerivAt`, `waveCubicNL_sub_le`,
  `waveCubicNL_second_apply`, `waveCubicNL_second_norm_le`, `waveCubicNL_third_apply`, `waveGw_norm_le`,
  `waveGw_analyticOnNhd`, `frozen_invariance_iff_waveXw`, `waveXw_analyticOnNhd`, `waveG_coeffW_eq_inner`,
  `waveG_coeffW_analyticOnNhd`, `waveG_coeffW_hasFDerivAt`, `waveG_frozen_fderiv_apply`, `waveXG_analyticOnNhd`,
  `waveXG_complexify`, `waveXH_analyticOnNhd`, `waveHw_analyticOnNhd`, `waveHw_fderiv_p`, `waveHw_fderiv_q`,
  `waveEllK_tsum_pow_mul_le`, `waveSineSeriesK_norm_le`, `contDiff_waveSineSeriesK`,
  `integral_waveSineSeriesK_mul_sineMode`, `waveSelSum_swap_left_mid`, `waveSelSum_add_left`): all report exactly
  `[propext, Classical.choice, Quot.sound]`.

## Suspected errata / deviations
- No blueprint defect found. Constants match the blueprint exactly (`2MK_s²`, `64MK_s²`, `C_* = K_{p+1/2}²/π`).
- Deviation (strengthening / form): the selection hypothesis is stated for the literal `(ijkl)^(-1/2)` (real power) and the
  count `waveSelCount`; for `K = ℝ` the cubic coefficient is cast through `RCLike.ofReal`. The two-sided hypothesis is only
  required for nonzero indices (the sum excludes zero indices, as in the blueprint).
- `waveCubicConst p` (landed, `K_{p+1/2}²/π`) equals `2 · (1/(2π)) · K_{p+1/2}²`, the instance of the selection constant.

## Design signals
- None: every proof elaborates at default heartbeats; the largest file is `SelectionOneSided.lean` (309 lines).
- `lp.single` terms need an explicit `(E := fun _ : ℕ+ => ℝ)` when no expected type is available (`GradLp`).
- `ext`/`convert` on `ContinuousLinearMap`s out of a product or `lp` type loses the intended shape; use
  `apply ContinuousLinearMap.ext; intro h` and `HasFDerivAt.congr_fderiv` (see `CubicMap`, `HamHamiltonian`).

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is infrastructure for W2, W3 and W8 (blueprint w1-sequences.tex `bpW:w1:cubic`, plus the complex clauses
of `bpW:w0n:recon-bounded` and `bpW:w0n:cubic-bound` by the scope ruling in W0-ANALYSIS-handoff.md). It has no
provider and no seal, so skip audit item 1.
1. Exact constants and carriers: selection (a)/(b) with 2M K_s² and 64M K_s²; the trilinear bound C_* = K_{p+1/2}²/π
   over RCLike K, with real structure and compatibility; the frozen identification `cubicGrad_eq_triML_div`, which
   must be exactly the frozen cubicGrad.
2. `frozen_invariance_iff_waveXw`: it closes the PARTIAL X^w specialization of `bpW:w1:coordinatewise`. Is it the
   blueprint's statement, under exactly the differentiability hypothesis, and with nothing conclusion-shaped?
3. `hamfield` (v): the coordinates of X^w; and (iv), the Hamiltonian structure.
4. The complex recon-bounded clause: does it close the W0-ANALYSIS audit F1 gap for that node?
5. Definitions on their whole carrier (waveSelSum, waveTriSeq, waveTriML, waveCubicNL, waveGw, waveXw).
6. Hygiene. This is a SLIM worktree, so lint only via w_lint.sh. Run the kernel replay of the 17 modules. Regenerated
   roots are authorized. One lean process at a time.

## Round 2 (response to audit 1)

New modules: `SelectionTwoAlg`, `QPair`, `QSymm` (all `KAM/Wave/Cubic/`, each < 250 lines). `KAM/Wave/Cubic/CubicDeriv.lean`
docstring fixed (N5).

- **F1 (gradient-identity (i))** closed.
  - `wavePair a p u y = Σ_l (κ_{a,p+1}u)_l (κ_{a,p}y)_l` (the unweighted pairing `⟨·,·⟩₀`), with `wavePair_norm_le`
    and `wavePairCLM` (continuous bilinear, norm ≤ 1).
  - `waveQuartForm : ContinuousMultilinearMap K (fun _ : Fin 4 => lp _ 2) K`, `𝒬 = uncurryRight (pairing ∘ 𝒯)`.
  - Defining identity `waveQuartForm_apply`: `𝒬(y₁,y₂,y₃,y₄) = Σ_l T(κy₁,κy₂,κy₃)_l (κy₄)_l = ⟨T(q₁,q₂,q₃),q₄⟩₀`, `q_i = κ_{a,p}y_i`.
  - Bound `waveQuartForm_norm_le` (`‖𝒬‖ ≤ C_*`) and `norm_waveQuartForm_le` (`‖𝒬 v‖ ≤ C_* ∏‖v i‖`).
  - Full four-slot symmetry `waveQuartForm_perm` (every `σ : Perm (Fin 4)`), via `waveQuartForm_swap34`
    (absolute convergence of the quadruple series `waveTri_quad_summable`, using `waveTri_oneSided` for the moduli;
    `waveTri_pairing_eq_quad`, `waveTri_pairing_swap`, coefficient symmetry `waveTriCoef_comm34`) plus the first-three-slot
    symmetry of `𝒯` and generation of `Perm (Fin 4)` by adjacent swaps (`mclosure_swap_castSucc_succ`).
- **F2 (selection, two-sided algebra)** closed: `waveSelSumZ_smul_left/_mid/_right`, `waveSelSumZ_add_left/_mid/_right`
  (summability of the guarded terms `waveSelTermZ` as hypothesis, supplied for `l ≠ 0` by `waveSel_twoSided`),
  `waveSelSumZ_swap_left_mid/_mid_right` (hypothesis: `c` symmetric in the first two / middle indices), and the same for
  `waveSelTwo` (`waveSelTwo_smul_*`, `_add_*`, `_swap_left_mid`, `_mid_right`, `_left_right`).
- Notes: N1 (second derivative only in directional form), N2, N3, N4 are unchanged and deliberately left (API distinctions
  recorded). N5 fixed.
- Checks: gate build of all 20 `KAM.Wave.Cubic.*` modules -> `Build completed successfully (3310 jobs).`;
  `w_lint.sh` exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (158 frozen declarations)`);
  short-name check OK; `#print axioms` of `waveQuartForm_perm`, `waveQuartForm_apply`, `waveQuartForm_norm_le`,
  `norm_waveQuartForm_le`, `waveTri_pairing_swap`, `waveSelSumZ_add_left`, `waveSelSumZ_swap_left_mid`,
  `waveSelTwo_swap_left_right`, `waveSelTwo_smul_left`: only `propext`, `Classical.choice`, `Quot.sound`. No `sorry`.
- Remaining item 1 of "NOT done" (gradient-identity (iii) Riesz-gradient remark for the `ℓ^{a,p}` inner product) is still
  not stated separately; the `ℓ²`/frozen gradient formulas are.
