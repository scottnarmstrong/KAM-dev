# W3-FLOW handoff (group 3: the Lie-series flow) — STATUS: COMPLETE

Date: 2026-10-31. Branch `inp-wpk`, worktree `/root/code/KAM-inp-wpk`. Labels: `bpW:w3:lie-coeff`,
`bpW:w3:leibniz`, `bpW:w3:flow`, `bpW:w3:symplectic`. All items of the three theorems are
proved (see "Proved" and "Second pass" / "Third pass"); `READY-W3-G3` is touched.

## Approach
The theory is proved for an abstract symmetric continuous trilinear `T : E³ → E` on a complex
Banach space (`LieSeq`–`LieMain`), with `φ_k = lieSeq T w k` defined by the Cauchy recursion
`(k+1) φ_{k+1} = Σ_{a+b+c=k} T(φ_a, φ_b, φ_c)` and `Γ_t = lieGamma = Σ t^k φ_k`. The majorant
`m_k` (`(k+1)m_{k+1} = Σ m_a m_b m_c`, `0 ≤ m_k ≤ 2^k`) gives `‖φ_k‖ ≤ m_k C^k ‖w‖^{2k+1}` and
`‖Dφ_k‖ ≤ (2k+1) m_k C^k ‖w‖^{2k}`. `LieApp`/`LieBirk` specialise to `T = ι ∘ S` (`birkT`,
`S = birkS = 4∇𝔉`, `ι = birkEmbed`, `C = birkCF = C_F`, `C_F > 0` by `birkCF_pos`).

## Files (all `KAM/Wave/Birkhoff/`, 25 new `Lie*` modules, each < 1500 lines, lines ≤ 100 columns)
`LieNumeric` (m_k), `LieSeq` (φ_k, bound), `LieDeriv` (Dφ_k, bound), `LieLeibniz` (Leibniz (i),
(iv)), `LieFlow1` (convergence, estimates in the `𝔚`-norm), `LieFlow2` (joint Fréchet
differentiability), `LieFlow3` (partials, transport equation), `LieReal` (reality, `leibniz` (iii)),
`LieFlow4` (triple Cauchy product, flow equation), `LieInv` (`Γ_{-t}Γ_t = id`), `LieCauchy`
(general trilinear Cauchy product), `LieVar` (variational equation), `LieNeumann` (Neumann
inverse), `LieSympl` (symplecticity, abstract), `LieApp` (`T = ι∘S`), `LieMain` (invertibility of
`DΓ`, gradient transport, abstract), `LieBirk` (the statements for `X_F` on `𝔚`).

## Proved (labels → declarations)
- lie-coeff / leibniz: `birkLieM_le_pow`, `lieSeq`, `norm_lieSeq_le`, `lieDer`, `norm_lieDer_le`,
  `lieDer_apply_field` (Leibniz (i): `Dφ_k(w) X(w) = (k+1) φ_{k+1}(w)`), `lieDer_succ_sym` (iv),
  `lieSeq_rho` (iii), symmetry from `birkT_perm`.
- flow (i) (C¹ part): `hasFDerivAt_lieGamma` (joint, `|t|<2`, `‖w‖<ρ₀=(40C_F)^{-1/2}`),
  `hasDerivAt_lieGamma_t`, `hasFDerivAt_lieGamma_w`.
- flow (ii): `birkGamma_flow` (`∂_tΓ = X_F(Γ)`, via `hasSum_lieCauchy`), `birkGamma_transport`
  (`∂_tΓ = DΓ X_F`), `lieGamma_zero` (`Γ_0 = id`).
- flow (iii), in the `𝔚`-norm: `norm_birkGamma_le` (`≤ 10/9‖w‖`), `norm_birkGamma_sub_le`
  (`‖Γ-w‖ ≤ 3|t|C_F‖w‖³`), `norm_birkGammaD_sub_le` (`‖DΓ-I‖ ≤ 10|t|C_F‖w‖²`),
  `birkGammaD_invertible` (two-sided inverse on `𝔚`, `‖B‖ ≤ 2`, `‖B-I‖ ≤ 20|t|C_F‖w‖²`).
- flow (iv) `birkGamma_rho`; (v) `birkGammaD_var` (`∂_t DΓ v = 3S(…)`, as `3T(DΓ v, Γ, Γ)`);
  (vi) `birkGamma_neg_birkGamma` (`Γ_{-t}Γ_t = id` for `|t|<2`, `160 C_F‖w‖²<1`, which contains
  `|t|≤1`, `‖w‖<ρ₁`).
- symplectic: `birkGammaD_symplectic` (`Ω(DΓξ, DΓη) = Ω(ξ,η)`, from the skewness of `DX_F`,
  i.e. `birkT_omega_symm` from `birkS_pairing` and the symmetry of `𝔉`), and the abstract gradient
  transport `lie_gradient_transport` (`Y = B X` given `Ω(Y,v) = DP(Aφ v)`, `A = DΓ`, `AB = 1`,
  `Ω` nondegenerate and `A` symplectic).

## Added in the second pass (modules `LiePlusNum`, `LiePlus`, `LiePlusInv`, `LieBirkPlus`)
- flow (iii), `𝔚⁺`-norm: `birkGamma_sub_plus` (`Γ_t w - w = ι ψ`, `‖ψ‖₊ ≤ 3|t|C_F‖w‖³`),
  `birkGammaD_sub_plus` (`DΓ_t - I = ι ∘ Ξ`, `‖Ξ‖_{𝔚→𝔚⁺} ≤ 10|t|C_F‖w‖²`), `birkGammaD_inverse_plus`
  (`DΓ_t` maps `𝔚⁺` into itself, inverses on `𝔚` and `𝔚⁺` of norm ≤ 2 compatible with `ι`,
  `DΓ⁻¹ - I = ι ∘ Ξ'`, `‖Ξ'‖_{𝔚→𝔚⁺} ≤ 20|t|C_F‖w‖²`); the hypothesis `2|t|C_F‖w‖² ≤ 1/10`
  is implied by `|t| < 2`, `‖w‖ < ρ₀` (`birk_q_le`). Abstract versions: `exists_lieGamma_sub`,
  `exists_lieGammaD_sub`, `lie_plus_inverse` (two spaces `E`, `F`, `ι : F → E`).
- flow (vi): `birkGamma_image_subset` (`Γ_1(B_ρ) ⊂ B_{10ρ/9}`), `birkGamma_image_superset`
  (`Γ_1(B_ρ) ⊃ B_{9ρ/10}`), `birkGamma_injOn`, for `160 C_F ρ² ≤ 1` (`ρ = ρ₁`).
- symplectic: `birk_gradient_transport` (chain rule `D(P∘Γ_t)(w) v = DP(Γ_t w)(DΓ_t v)`,
  `= Ω(B X, v)`, and `B X` is the unique such vector; `𝔚⁺`-valuedness of `B X` for `X ∈ 𝔚⁺` is
  `ι ∘ BF = B ∘ ι` in `birkGammaD_inverse_plus`).

## Third pass: analyticity (modules `LieMulti`, `LieAnalytic`, `LieAnalyticPlus`, `LieBirkAnalytic`)
- `lieBlock` (`MultilinearMap.compMultilinearMap` along `(Σ j, Fin (2x_j+1)) ≃ Fin n`),
  `lieMulti` (`Φ_k : E^{2k+1} → E`, `Φ_0 = id`, `(k+1)Φ_{k+1} = Σ_{a+b+c=k} T(Φ_a,Φ_b,Φ_c)`,
  defined by recursion with `attach`), `lieMulti_const` (`Φ_k(w,…,w) = φ_k(w)`),
  `norm_lieMulti_le` (`‖Φ_k‖ ≤ m_k C^k ≤ (2C)^k`).
  (The Cauchy-form recursion is used rather than the blueprint's slot-insertion form; `φ_k` and
  `Φ_k` agree on the diagonal, and `lieDer_apply_field` is the blueprint's `φ_{k+1} = L φ_k/(k+1)`.)
- `lieSeries`, `lieGamma_hasFPowerSeriesOnBall` (the series `Σ t^k Φ_k` represents `Γ_t` on
  `‖w‖ < ρ` when `2|t|Cρ² ≤ 1/10`), `analyticAt_lieGamma`; concrete:
  `birkGamma_analyticOnNhd` (`Γ_t` analytic on `‖w‖ < ρ₀`, `|t| < 2`).
- `𝔚⁺` coefficients: `lieMultiF` (`Φ^F_k`, `‖Φ^F_k‖ ≤ m_{k+1}C^{k+1}`), `lieSeriesF`,
  `liePsiSum`, `liePsiSum_hasFPowerSeriesOnBall`, `analyticAt_liePsiSum`, `map_liePsiSum`;
  concrete: `birkGamma_sub_analytic` (`Γ_t - id` analytic `B_{ρ₀} → 𝔚⁺`: an analytic `ψ` with
  `ι ψ(w) = Γ_t(w) - w` and `‖ψ(w)‖₊ ≤ 3|t|C_F‖w‖³`).
- leibniz (ii) `𝔚⁺`-valued coefficients: `norm_lieMultiF_le`.

## Not done
Nothing of `bpW:w3:lie-coeff`, `bpW:w3:leibniz`, `bpW:w3:flow`, `bpW:w3:symplectic` is left open.
The `Γ_t - id` analyticity statement is for the `𝔚⁺`-valued `ψ` with `ι ψ = Γ_t - id` (unique by
injectivity of `birkEmbed`), as in the blueprint's "analytic `B_{ρ₀} → 𝔚⁺`".

## Checks
- Builds: every `KAM.Wave.Birkhoff.*` module of `KAM/Root/Wave.lean` (the 8 modules of the second
  and third pass each built by `w_build.sh`; earlier ones rebuilt after the F1 commit) via
  `w_build.sh` (one module per call, in import order): `Build completed successfully`
  (the script's own rc is 1 even on success; judged from the text).
- `w_lint.sh /root/code/KAM-inp-wpk`: exit 0 (`check_lean_modules: PASS (3608 Lean files, ...)`,
  `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK`); all `Lie*.lean` lines ≤ 100 columns.
- `main_shortname_check.py` on all 25 `Lie*` modules: `short-name check OK`.
- `#print axioms` of 46 main declarations (27 of the first pass and 19 of the second and third,
  e.g. `birkGamma_flow`,
  `birkGamma_transport`, `birkGammaD_var`, `birkGamma_neg_birkGamma`, `birkGammaD_symplectic`,
  `birkGammaD_invertible`, `lie_gradient_transport`, `norm_lieDer_le`, `birkGammaD_inverse_plus`,
  `birk_gradient_transport`, `birkGamma_analyticOnNhd`, `birkGamma_sub_analytic`): all exactly
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `axiom`, `maxHeartbeats` or other option overrides in any new file; `KAM/Root/Wave.lean`
  regenerated with `scripts/gen_root_imports.py` (no hand edit).

## Uncertainties, errata, deviations
- Domain used throughout: `|t| < 2`, `40 C_F ‖w‖² < 1` (this is `‖w‖ < ρ₀`); the estimates use
  `r = 2|t|C_F‖w‖² ≤ 1/10`, which holds on this domain since `4·C_F‖w‖² < 1/10`.
- The variational equation is stated for `T = ι∘S` (the blueprint's `DX_F(y)ξ = 3S(y,y,ξ)` read in
  `𝔚` through `ι`).
- `waveCubicConst_pos` (new, `LieApp`): `C_* > 0` for `p ≥ 1/2`, needed for `C_F > 0`.
- Suspected errata: none found.
