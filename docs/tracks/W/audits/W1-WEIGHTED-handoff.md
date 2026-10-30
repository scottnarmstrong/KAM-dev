# Handoff W1-WEIGHTED (blueprint-W/parts/w1-sequences.tex lines 28-285), branch inp-wpa

Files (all new, all under KAM/Wave/Seq/, namespace KAM.Wave, <= 245 lines each; no heartbeat options):
Transport, Multiplier, Embed, Coordinatewise, Diag, Flow, Linfty, Tails (.lean). Root parts
KAM.lean / KAM/Root/Wave.lean regenerated with scripts/gen_root_imports.py (committed).

## Proved, label -> Lean declarations
- bpW:w1:transport: `coeffW` (kappa_{a,p}), `IsEll`, `ellNormSq`, `ellNorm`, `tauLp` (tau_{a,p}), `ellWeight_pos`,
  `coeffW_one_one` (coeffW 1 1 = coeff; real sequences).
- bpW:w1:space (i): `tauLp_coeffW`, `coeffW_tauLp`, `coeffW_injective`, `coeffW_add/smul/neg/sub`, `coeffWLinear`,
  `norm_tauLp_sq`, `ellNorm_coeffW` (norm preserved), `inner_tauLp` (transported inner product). (ii) `norm_coeffW_le`,
  `coeffWCLM` (= omega^-1 ev_j). (iii) `truncLp`, `tendsto_norm_sub_truncLp`. (iv) `coeffW_one_one`,
  `norm_prod_eq_max_ellNorm` (frozen WaveSpace norm = max of the (1,1) norms of coeff y, coeff y').
- bpW:w1:multiplier: `diagCLM`, `norm_diagCLM_le(')`, `norm_le_norm_diagCLM`, `norm_le_norm_of_apply_eq`,
  `not_exists_diag_of_unbounded`, `diag_representative`.
- bpW:w1:embed: `embedRatio`, `embedRatio_le_one`, `embedRatio_le_of_lt` ((sigma/(e(a-a')))^sigma), `embedCLM`,
  `norm_embedCLM_le`, `ellNorm_coeffW_le_of_le` (i), `ellNorm_coeffW_le_of_lt` (ii), `coeffW_embedCLM`,
  `embedCLM_injective`, `embedCLM_comp` (iii); general `isEll_coeffW_of_ratio_le`.
- bpW:w1:coordinatewise: `hasDerivAt_coeffW`, `hasDerivAt_coordinates_iff` ((a) <-> (b)), `frozen_invariance_iff`
  (clause (4) of frozen nlw2 <-> iota-hat (DK nu) = v, see deviations).
- bpW:w1:diag: (i) `lamRatio`, `lamMul`, `lamMul_represents`, `norm_lamMul_le_of_nonneg/neg`, `norm_lamMul_eq`
  (= (1+m)^(r/2), r >= 0), `lamMul_comp_neg` (inverse); (ii) `not_exists_bounded_lam_pow`;
  (iii) `rotCLM`, `norm_rotCLM`, `rotCLM_add`, `rotCLM_zero`, `continuous_rotCLM_apply`;
  (iv) `flowCLM`, `norm_sq_flowCLM`, `norm_flowCLM_apply_le` (sqrt 2), `flowCLM_add`, `flowCLM_zero`,
  `hasDerivAt_flow_fst/snd`, `coeffW_flow_fst/snd`, `hasDerivAt_coeffW_flow_fst/snd`.
- bpW:w1:linfty: `IsLinfty`, `tauInfty`, `norm_tauInfty_le_iff`, `isLinfty_of_bound`, `IsLinftyLipschitz`,
  `isLinftyLipschitz_iff`.
- bpW:w1:tails: `waveB`, `waveOmega`, `waveOmegaTilde`, `tildeOmegaSeq`, `tail_bound`, `tail_lipschitz`, `tail_gap`,
  `isLinfty_tildeOmegaSeq`, `norm_tildeOmegaSeq_le`, `isLinftyLipschitz_tildeOmegaSeq`.

## Not done
- bpW:w1:space separability (stepW:w1:sep; blueprint says it is not consumed).
- bpW:w1:diag (iv) last sentence ("in complex coordinates L_t is R_t"): needs the z = (q+ip)/sqrt2 coordinates
  of Def bpW:w0:z, not in this package.
- The Hilbert-space *type* structure on l^{a,p} is not introduced (blueprint: no new normed type); it is expressed by
  the transport lemmas (norm/inner/linearity) above.
- Tails: Omega-tilde bound "Assumption B of P96-K holds with d=1, delta=-1" is prose only; the quantitative bounds are proved.

## Deviations / notes
- Order: Multiplier + Embed were built before Coordinatewise, since the latter's statement uses iota-hat (embedCLM).
- `frozen_invariance_iff`: the field X^w of bpW:w1:hamfield (v) is not in this package, so v = (v1, v2) is a
  hypothesis-free *parameter* characterized by its coefficients (hv1: coeffW 1 0 v.1 = lam*coeff p, hv2: coeffW 1 0 v.2 =
  -lam*coeff q - cubicGrad). This is a defining property of the representative of X^w (not a conclusion-shaped premise),
  but the consumer must supply v with these properties (existence needs the l^{1,2} cubic bound).
- `IsLinftyLipschitz` is stated through `tauInfty` (lp infinity) as in the blueprint; `isLinftyLipschitz_iff` is the pointwise form.
- Tails use `tildeOmegaSeq` (entries j = 1,2 set to zero), as the blueprint's Lean note prescribes; pointwise statements hold for all j >= 1.
- `ellWeight_pos` is a new KAM.Wave name that other packages might also define (potential clash at landing).
- Generic lemma names are prefixed (`lam_pnat_pos`, `pnat_le_lam`, `lam_le_sqrt_mul`, ...) to avoid collisions.

## Checks
- Gate: `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpa KAM.Wave.Seq.Transport
  KAM.Wave.Seq.Multiplier KAM.Wave.Seq.Embed KAM.Wave.Seq.Coordinatewise KAM.Wave.Seq.Diag KAM.Wave.Seq.Flow
  KAM.Wave.Seq.Linfty KAM.Wave.Seq.Tails` -> "Build completed successfully (2799 jobs)", no sorry/warnings.
- `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpa` -> exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK,
  ABI HASHES OK).
- `#print axioms` (checked via a scratch file, removed) of ellNorm_coeffW, inner_tauLp, tendsto_norm_sub_truncLp,
  norm_prod_eq_max_ellNorm, norm_diagCLM_le, not_exists_diag_of_unbounded, embedRatio_le_of_lt, ellNorm_coeffW_le_of_lt,
  embedCLM_comp, hasDerivAt_coordinates_iff, frozen_invariance_iff, lamMul_represents, norm_lamMul_eq,
  not_exists_bounded_lam_pow, continuous_rotCLM_apply, norm_flowCLM_apply_le, hasDerivAt_coeffW_flow_snd,
  isLinftyLipschitz_iff, tail_gap, isLinftyLipschitz_tildeOmegaSeq: all exactly [propext, Classical.choice, Quot.sound].

## Blueprint defects / errata
- None found that block the Lean statements. Minor: bpW:w1:tails states bounds "for j>=3" but they hold for all j>=1
  (the proof does not use j>=3); the sup form needs the zero-padding convention (as noted in the source remark).
- Mathlib names: all names in (W1-E1) used here exist; note `Finset.Iic`/`LocallyFiniteOrder` is NOT available on PNat
  (truncations use `Finset.image Nat.succPNat (Finset.range N)`).

## Design signals
None; every file elaborates in a few seconds at default heartbeats. Module system note: Mathlib derivative lemmas
(`HasDerivAt.smul_const`, ...) need a non-public `import Mathlib.Analysis.Calculus.Deriv.Mul`.

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure used by several nodes. It has no provider and no
seal, so skip audit item 1 and the seal-body probe.
1. Statement fidelity against blueprint-W/parts/w1-sequences.tex lines 28-285 (`bpW:w1:transport`, `space`,
   `multiplier`, `embed`, `coordinatewise`, `diag`, `linfty`, `tails`).
2. PRIORITY: `frozen_invariance_iff`. Is the parameter `v` with its characterizing hypotheses `hv1`, `hv2` a
   legitimate representative, or is it conclusion-shaped? Does the statement faithfully give the equivalence of frozen
   nlw2 clause (4) with `DK(θ)ν = X^w(Kθ)`, as `bpW:w1:coordinatewise` claims, under exactly its differentiability
   hypothesis?
3. Definitions on their whole carrier: `coeffW`, `IsEll`, `ellNorm`, `tauLp`, `diagCLM` (any junk branch),
   `lamMul`, `flowCLM`, `tildeOmegaSeq` (zero padding at j = 1, 2).
4. The not-done items: are they really unconsumed, or needed by W2/W3?
5. Hygiene. This is a SLIM worktree, so run lint only as `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpa`.
   Run the kernel replay of the 8 modules. `git diff inp...HEAD -- KAM/Frozen manifest README.md` must be empty.
