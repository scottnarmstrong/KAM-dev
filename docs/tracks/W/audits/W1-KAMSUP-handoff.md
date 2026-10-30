# Handoff: W1-KAMSUP (branch `inp-wpg`, worktree `/root/code/KAM-inp-wpg`)

Package: blueprint-W `parts/w1-sequences.tex`, subsection `bpW:w1:kam` ("Support for the KAM step").
Hard rules respected: no `set_option maxHeartbeats`/other budget overrides; every file well under 1500 lines
(largest 330 lines); all files are Lean modules in namespace `KAM.Wave`; no `sorry`/`axiom`/`admit`/`unsafe`/`opaque`.
No dependency on `KAM/Wave/Analytic`, `KAM/Wave/Algebra`, frozen theorems or providers. Reused: track K
(`KAM/Strip/*`, `KAM/Fourier/*`) and `KAM/Wave/Seq` (Multiplier, Embed, Transport).

## Files (all under `KAM/Wave/KamSupport/`) and labels

| File | Blueprint label | Lean declarations |
|---|---|---|
| `LatticeCount.lean` | `bpW:w1:lattice` (ii) | `kamL1`, `kamLattice_ncard_fiber_le` (`≤ 2ⁿ C(m+n-1,n-1)`), `kamLattice_ncard_fiber_le_pow` (`≤ 2ⁿ(m+1)^(n-1)`), `kamLattice_card_filter_le(_pow)` (finset forms), `kamChoose_add_le_pow` |
| `Lattice.lean` | `bpW:w1:lattice` (i),(iii),(iv) | `kamLattice_hasSum_exp` (i: `∑ e^{-2πσ|k|₁} = coth(πσ)ⁿ`), `kamLatticeConst` (`S_{n,c}(σ)`), `kamLattice_tsum_pow_exp_le` (iii, with summability), `kamDivisor_le`, `kamLattice_tsum_divisor_le` (iv, `A_k ≤ (1+|k|)^τ`), `kamLattice_BSigma_le` (iv, `B_σ²`) |
| `FourierBanach.lean` | `bpW:w1:fourier-banach` (i)–(iv) | `kamFourierBanach_coeff_le` (i), `kamFourierBanach_sum_le` (ii, `coth(πσ)ⁿ`), `kamFourierBanach_weighted_sum_le` (ii, `M·S_{n,c}(σ)`), `kamFourierBanach_summation` (iii), `kamFourierBanach_coeff_sub`, `kamFourierBanach_coeff_sub_le` (iv). Mostly track K's Banach-valued `KAM.decay_boundary_radius`, `summation_forward_vec`, `summableWeighted_torusCoeffW` (already for any complex Banach space `W`) glued to the lattice constant |
| `SchurTest.lean`, `HilbertMatrix.lean` | `bpW:w1:schur` (i)–(iv) | `KamSchurBound`, `kamSchurCLM`, `norm_kamSchurCLM_le` (Schur test, new); `kamEntry`, `kamEntry_sum_sq_row_le/col_le`, `kamHilbertKernel_sum_sq_le` (`≤ π²/3`), `kamHilbertCLM`, `kamHilbertCLM_hasSum`, `norm_kamHilbertCLM_le` (i), `norm_kamEntry_diag_le`, `kamEntryDiagCLM`, `norm_kamEntryDiagCLM_le` (ii), `KamDominated`, `kamSchurBound_of_dominated`, `exists_clm_of_dominated` (iii: operator with `(Tv)_i = ∑_j F_ij v_j`, `‖T‖ ≤ c(1+π/√3)‖A‖ ≤ 3c‖A‖`), `KamDominated.weighted` (iv) |
| `FourierShift.lean` | `bpW:w1:fourier-shift` | `kamFourier_shift` (arbitrary `η`, `F`-valued, only holomorphic+periodic on `T_s`; no boundedness assumed), `kamCharacter_neg_imag`, `kamTorusAverage_clm` |
| `FourierBessel.lean`, `FourierL2.lean` | `bpW:w1:fourier-l2` (i)–(iii) | `kamBessel` (Bessel for Hilbert-valued continuous maps, finite `K`), `kamFourierL2_orthant_le`, `kamFourierL2_finite_le_of_lt`, `kamFourierL2_sum_le` (i: `∑‖û_k‖²e^{4πs|k|₁} ≤ 2ⁿM²`, summable), `kamFourierL2_summation` (ii), `kamFourierL2_eq_fourierSum` (iii) |
| `KamSpace.lean` | `bpW:w1:kam-space`, `kam-conventions`, `kam-domain` | `KamPhase`, `kamNorm`, `kamDomain`, `kamEmbed`, `kamOpNorm`, `kamOpNorm_apply_le`, `kamOpNorm_le`; `kamDomain_isOpen`, `kamDomain_convex`, `kamDomain_mono`, `kamDomain_add_mem` (margin), `kamNorm_embed_le` (`p̄ ≤ p`), `kamNorm_le_of_le_radius` (`r' ≤ r`); conventions: `kam_conj_relabel`, `kam_wave_norm_sum_ge/le` (sum vs. max norm of `WaveSpace`, factor ≤ 2), `kam_strip_period_conversion` |

`KAM/Root/Wave.lean` was regenerated with `python3 scripts/gen_root_imports.py` (the only root change); `KAM.lean` is untouched
(its "out of date" note in the lint is the landing-time regeneration).

## Labels NOT done
None of the package labels is skipped. Deviations from the literal blueprint text (statements are faithful; proof routes/forms differ):

1. `fourier-shift`: proved through track K's `KAM.torusAverage_imag_shift` (derivative-in-the-shift-size argument, scalar, bounded)
   plus duality (`SeparatingDual`) and `KAM.periodic_bounded`, not through the blueprint's coordinatewise rectangle steps
   `fshift-one/iter/end` and `ext-rect`. The statement is exactly the blueprint's (arbitrary `η`, `F` Banach, `u` only holomorphic and periodic).
2. `fourier-l2` (i): Parseval (`stepW:w1:parseval`) replaced by Bessel's inequality (`kamBessel`), which is all the bound `≤ M²` needs.
   (iii) is proved on all of `T_s` (stronger than `T_{s'}`, `s'<s`) from track K's `eq_fourierSumVec_torusCoeffW`.
3. `kam-space`: the points of `ℓ^{a,p}` are represented in weighted coordinates (`ℓ²`), so `kamNorm`/`kamDomain` do not mention `a,p`;
   the inclusion between weights is `kamEmbed` (`embedCLM`). `|L|_{r,s}` is `kamOpNorm`, defined as the infimum of admissible constants
   (not `ContinuousLinearMap.opNorm`: `kamNorm` is not a Mathlib norm); `kamOpNorm_apply_le` shows it is itself admissible for `0 < s`.
4. `schur`: an operator is characterised by its matrix through the absolutely convergent row sums (`HasSum`); (iv) is the weight-invariance
   of the domination hypothesis (`KamDominated.weighted`, any positive `α_i/β_j`), the representative operator itself being covered by (iii).
5. `kam-domain`: hypothesis `2σ < s` is carried but unused (named `_hσs`); the proof needs only `σ ≤ 1`.
6. `lattice` (iii): `S_{n,c}` is stated for `n ≥ 1` with real power (`(·)^0 = 1`) as in the blueprint; (iv)'s `B_σ²` is the inequality with the factor `2ⁿ` outside the sum.

## Checks
- Gate build (last run): `/mnt/HC_Volume_106379410/orchestrator-tools/inp_lake_build.sh /root/code/KAM-inp-wpg KAM.Wave.KamSupport.LatticeCount KAM.Wave.KamSupport.Lattice KAM.Wave.KamSupport.FourierBanach KAM.Wave.KamSupport.SchurTest KAM.Wave.KamSupport.HilbertMatrix KAM.Wave.KamSupport.FourierShift KAM.Wave.KamSupport.FourierBessel KAM.Wave.KamSupport.FourierL2 KAM.Wave.KamSupport.KamSpace`
  tail: `✔ [3244/3244] Built KAM.Wave.KamSupport.FourierL2` / `Build completed successfully (3244 jobs).` (0 warnings in the log).
- `w_lint.sh`: see the end of this file (first run flagged only >100-column lines, all fixed).
- `#print axioms` (every main declaration listed in the table, e.g. `kamLattice_tsum_pow_exp_le`, `kamFourierBanach_weighted_sum_le`,
  `kamFourier_shift`, `kamFourierL2_sum_le`, `norm_kamHilbertCLM_le`, `exists_clm_of_dominated`, `kamDomain_add_mem`, `kamOpNorm_apply_le`):
  all `[propext, Classical.choice, Quot.sound]`.

## Blueprint defects
None found. All stated constants hold as written (`π/√3 < 2` so `c(1+π/√3) ≤ 3c`; the `S_{n,c}` bound; `coth(πσ)ⁿ`; Bessel gives `2ⁿM²`).
Minor: `bpW:w1:lattice` (iii) as stated needs `n ≥ 1` (so that `b = c+n-1 ≥ 0` and `(m+1)^{n-1}` counts), which the lemma's `n ≥ 1` already says.

## Design signals
None: no proof needed more than default heartbeats; no module over 330 lines. The ABI/lint stage is slow only because the machine is loaded.
Track-K reuse note for W4: `KAM.torusCoeffW` is `W`-valued for any complex normed space `W` (the Banach step needed no new analysis).

## Lint result
`/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpg`: exit 0. Tail:
```
check_lean_modules: PASS (1659 Lean files, 0 comparator configurations)
FROZEN-ANCHOR GUARD OK
ABI HASHES OK (158 frozen declarations)
EXIT=0
```

## AUDIT FOCUS (sub-orchestrator kam-d4)

This package is off the frontier: source-faithful infrastructure for W4 (blueprint w1-sequences.tex `bpW:w1:kam`).
It has no provider and no seal, so skip audit item 1.
1. PRIORITY: `fourier-banach` (i)–(iv) and `lattice`. These replace the false P96-K p. 127 operator square-sum bound
   (erratum E-W-Pos96K-1), and W4 consumes their exact constants (coth(πσ)ⁿ, S_{n,c}(σ)). Check them against the blueprint.
2. Deviations 1–6 above: proof-route changes (fourier-shift via track K plus duality; fourier-l2 via Bessel), the
   kam-space representation in weighted coordinates, `kamOpNorm` as an infimum of admissible constants (is it a
   faithful |L|_{r,s}?), and the unused `_hσs`.
3. Definitions on their whole carrier: `kamNorm`, `kamDomain`, `kamOpNorm`, `kamSchurCLM`, `KamPhase`.
4. Hygiene. This is a SLIM worktree, so run lint only via `/root/code/KAM-inp/.drafts/W/w_lint.sh /root/code/KAM-inp-wpg`.
   Run the kernel replay of the 9 modules. Regenerated roots are authorized. The machine is short on memory: one
   lean process at a time, LEAN_NUM_THREADS=1.

## Round 2 (after audit 1)

**F1 (kamOpNorm/kamNorm carrier).** `KamSpace.lean`: the raw `sInf` on arbitrary linear maps is gone.
New `KamOpAdmissible r s L C` (`0 ≤ C ∧ ∀ W, kamNorm r (L W) ≤ C * kamNorm s W`) and the source carrier
`KamBoundedMap r s` (a linear map together with `0 < r`, `0 < s` and an admissible bound). `kamOpNorm` is defined
only on `KamBoundedMap r s`; `kamOpNorm_isLeast` proves it is admissible and below every admissible constant
(`kamOpNorm_apply_le`, `kamOpNorm_nonneg`, `kamOpNorm_le` updated: no loose `C` arguments in `_apply_le`).
`kamNorm` stays a plain formula; it is a norm only for `0 < r` (`kamNorm_eq_zero`, `kamNorm_nonneg` carry that
hypothesis; documented in the module docstring). No consumers outside `KamSpace.lean`.

**F2 (Schur (iii) constant).** `kamSchurBound_of_dominated` and `exists_clm_of_dominated` no longer assume `0 ≤ c`.
Caveat (blueprint defect, tacit `c ≥ 0`): for `c < 0` and `A ≠ 0`, the matrix `F = 0` satisfies the domination
hypotheses while the literal conclusion `‖T‖ ≤ c(1+π/√3)‖A‖` would be negative, hence false. The premise-free
statements therefore use `max c 0` (identical to the blueprint's constants when `c ≥ 0`); the exact-constant form
for `c ≥ 0` is `kamSchurBound_of_dominated_nonneg` / `exists_clm_of_dominated_nonneg`. Helper `KamDominated.mono_const`.
Also fixed the stale name in the `HilbertMatrix` docstring (N5). N4: largest module is `HilbertMatrix.lean` (~420 lines).
`KamSchurBound.bound_nonneg/bound_mono` names kept.

Checks: gate build of `KAM.Wave.KamSupport.HilbertMatrix KAM.Wave.KamSupport.KamSpace`: `Build completed successfully (3160 jobs).`
Lint: see below.
Lint (round 2): `w_lint.sh` exit 0 (check_lean_modules PASS, FROZEN-ANCHOR GUARD OK, ABI HASHES OK).
