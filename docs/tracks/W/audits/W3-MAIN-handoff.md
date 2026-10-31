# W3-MAIN handoff (group 4) — STATUS: COMPLETE (all main results proved; the three former open items closed in Round 2)

Branch `inp-wpk`, worktree `/root/code/KAM-inp-wpk`. Labels: `bpW:w3:main`, `bpW:w3:Yseries`,
`bpW:w3:real-restrict`, `bpW:w3:gamma-real`, `bpW:w3:transport-tori`,
`bpW:w3:transport-tori-weak`. `READY-W3-G4` is **not** touched (see "Not done").
Notation: `ι = birkEmbed a (p+1) p` (𝔚⁺ ⊂ 𝔚; a map into 𝔚⁺ is a `BirkSpace` point read at weight
`p+1`), `C_* = waveCubicConst p`, `C_F = birkCF m p`, `B_{ρ₁} = {w | 160 C_F ‖w‖² < 1}`,
`Γ = birkGamma … 1`, `E = BirkReal = ℓ²_ℝ × ℓ²_ℝ` (weighted coordinates), `𝒵|_E = birkZR`,
`Π = birkPi` (`Re 𝒵⁻¹`).

## Files (`KAM/Wave/Birkhoff/`, 23 new modules, each < 1500 lines, lines ≤ 100 columns)
`MainQuart`, `MainK`, `MainK1`, `BlockMap`, `YSeriesNum`, `YSeries`, `YSeries2`, `YSeries3`,
`YSeries4`, `MainK2a`–`MainK2f`, `MainK3`, `MainConj`, `MainReal`, `MainGamma`, `MainGammaSympl`,
`MainTori`, `MainWeak`, `MainRealK`.

## Proved
- **main (i)**: `K = H∘Γ − Λ − Ḡ − G^{nor}` (`birkK`, `birkK_eq : K = K₁+K₂`);
  `norm_birkK1_le`, `norm_birkK2_le` (`≤ 5C_*C_F‖w‖⁶` each; mean value inequality
  `norm_sub_le_quart`, `∂_tΛ(Γ_t w) = Z'(Γ_t w)` = `hasDerivAt_birkLambda_gamma`),
  `norm_birkK_le` (`|K| ≤ 10C_*C_F‖w‖⁶`), `birkK_analyticOnNhd`, `birkK_rho` (real).
- **main (ii)**: `birkK_isClassA : K ∈ 𝒜(B_{ρ₁})` with field `birkXK = X_{K₁}+X_{K₂}`:
  `birkK_field` (`DK = Ω(X_K, ·)`), `birkXK_analyticAt`, `norm_birkXK_le` (`‖X_K‖₊ ≤ 66C_*C_F‖w‖⁵`),
  reality (`IsBirkClassA.field_rho`). `X_{K₁} = DΓ⁻¹X_G(Γ) − X_G` (`birkXK1`, `birkK1_field`,
  `norm_birkXK1_le ≤ 44…`, `birkXK1_analyticAt`; `birkPsi`, `birkXi`, `birkAF`, `birkBF`,
  `birkInvData`). `X_{K₂}` (`birkXK2 = Σ_{n≥1} V_n(w,…,w)/(n+1)`): `birkK2_field`,
  `norm_birkXK2_le ≤ 22C_*C_F‖w‖⁵`, `birkXK2_analyticAt`.
- **Yseries**: the explicit coefficients `V_n : 𝔚^{2n+3} → 𝔚⁺` (`lieV`, triangular recursion
  `V_n = Nsum_n − Σ_{j<n}(2j+3)Ψ^F_j(ιV_{n−1−j},·)`, `slotMap`, `symmMulti`, `blockMap`),
  `norm_lieV_le` (`‖V_n‖ρ^{2n} ≤ 4‖N‖(10·2Cρ²)^n`), `lieV_identity`
  (`DΓ_t(ι V_t) = ι N(Γ_t)`, `V_t = Σ t^n V_n`), `hasFPowerSeriesOnBall_lieV`/`analyticAt_lieV`
  (the power series, radius `ρ` with `2C_Fρ² ≤ 1/80`, i.e. `ρ = ρ₁`). Deviation from the
  blueprint's route: `Y_j` are defined by the triangular recursion for `DΓ_tV = X_{Z'}(Γ_t)` rather
  than by composing the Neumann series; the series for `∫₀¹Y dt` is `Σ V_n/(n+1)` (`n ≥ 1`), and
  `DK₂ = Ω(X_{K₂}, ·)` is obtained by differentiating `s ↦ DΛ(Γ_s w)(DΓ_s u)` (derivative of the
  homological identity `birk_DLam_homological_diff`) instead of a parameter integral.
- **main (iv)**: `birk_conjugacy`: for `y ∈ 𝔚⁺`, `ι y ∈ B_{ρ₁}`: `Γ(ιy) = ι z`
  (`z = y + ψ(ιy)`) and `DΓ(ιy)[X_Λ(y)+X_Ḡ+X_{G^{nor}}+X_K] = X_Λ(z)+X_G(Γ(ιy))`.
  (main (iii) is the landed quartic results: `birkQuart_isClassA`, `norm_birkQuartX_le`, the
  `G^{nor}` bound in `QuartNormal`.)
- **real-restrict**: `real_restrict`, `real_restrict_fun` (`MainReal`); applied to `K`, `X_K`
  (`birkK_real`, `birkXK_real` in `MainRealK`: real analytic on `{320C_F‖x‖² < 1}`).
- **gamma-real** on `{x ∈ E | 320 C_F ‖x‖² < 1}` (`‖x‖ < r₁ = ρ₁/√2`): `birkGammaR`,
  `birkGammaR_analyticOnNhd` (real analytic), `birkGammaR_sub` (`𝒵Γ^ℝx = 𝒵x + ι𝒵ψ`,
  `‖ψ‖ ≤ 6√2C_F‖x‖³`, `‖Γ^ℝ x‖ ≤ (10/9)√2‖x‖`), `birkGammaR_inv`
  (`ΠΓ_{−1}𝒵Γ^ℝ = id`), `birkGammaR_injOn`, `birkGammaR_surj` (`⊃ B_{r₁/2}`),
  `birkGammaR_hasFDerivAt`, `birkGammaR_symplectic` (`Σ dq∧dp`, `birkOmegaR`).
- **transport-tori**: `birk_transport_tori` (directional form along `θ + tν`).
- **transport-tori-weak**: `birk_transport_tori_weak`: the weak equation in `𝔚_{a,p−1}` forces
  `Ψ(θ) ∈ 𝔚⁺` (`birkXLamInv`, `birkEmbed_birkXLamInv`) and then the transport conclusion.
  Deviation: the bound proved is `‖Ψ‖₊ ≤ ‖DΨν‖ + 2C_*‖Ψ‖³ + C'_K‖Ψ‖⁵` (constant `2C_*`, from the
  two quartic bounds separately, not `C_*` from the disjoint-support coefficient `c̄ + c^{nor}`).

## Round 2: the three former open items (all closed)
New modules `MainRealTori`, `MainRealWeak`, `MainFrozenForm`, `MainRealId` (each < 300 lines).
1. **Frozen clause (4) form.** `birk_transport_tori_frozen` (and `_weak_frozen`): at `(a,p) = (1,1)`, for
   real `Ψ` (`ϱΨ = Ψ`), `Kmap θ = birkTransportQP Ψ θ = Π Γ ι Ψ θ` satisfies
   `(ι̂ (D Kmap(θ) ν).1, ι̂ (D Kmap(θ) ν).2) = waveXw m hm (Kmap θ)` (via
   `frozen_invariance_iff_waveXw`; extra hypothesis only differentiability of `ιΨ`/`Ψ` at `θ`, the
   blueprint's "differentiable as a map into 𝔚"). Coordinatewise: `birk_transport_tori_frozen_coord`,
   `birk_transport_tori_weak_frozen_coord` (`coeff`, `lam`, `cubicGrad`).
2. **Real identities** (`MainRealId`): `birkK_real_fderiv`/`birkK_real_gradient`:
   `D K^ℝ(x) h = ω_ℝ(Π ι X_K(𝒵x), h) = Σ_j [(X_K^ℝ)^q_j h^p_j - (X_K^ℝ)^p_j h^q_j]`, i.e.
   `X_K^ℝ = (∂_p K^ℝ, -∂_q K^ℝ)`. `birkHamBar_birkZR`: `Ḡ(𝒵x) = birkGbarR x = ½⟨AI,I⟩ + ⟨BI,Z⟩`,
   `I_j = (q_j²+p_j²)/2` (`birkActionR`), from `birkQuartP_bar`; `birkLambda_birkZR`; `birkH_gammaR`:
   `(Λ+G)(𝒵 Γ^ℝ x) = Λ(𝒵x) + Ḡ(𝒵x) + G^{nor}(𝒵x) + K(𝒵x)`.
3. **Real transport in `(Q,P)` form** (`MainRealTori`, `MainRealWeak`): `birk_transport_tori_real`
   (`a > 0`): `𝒵(Q,P) = Γ∘ιΨ` and `D_ν Q_j = λ_j P_j`, `D_ν P_j = -λ_j Q_j - waveCubic(Q)_j`
   (`coeffW a p` coefficients; `waveCubic = 𝒢` of W0, `waveCubic_coeffW_eq_waveTriSeq`);
   `birk_transport_tori_weak_real`: same for `Ψ` in the weak equation (also gives `Ψ(θ) ∈ 𝔚⁺` with the
   bound). `T = 𝒢q` uses `a > 0` as in the blueprint.
- Axioms of all of the above: `[propext, Classical.choice, Quot.sound]`.
- Merged `inp` first. The W3-FLOW audit fixes (F1–F3, commit `840a38c7`) were done before these items;
  they refactor `LieFlow2` (majorant lemma), and the W3-MAIN modules were rebuilt against it.

## Checks
- Builds: every new module via `w_build.sh` (one module per call, import order):
  `Build completed successfully`. Merged `inp` (clean; only a doc file changed).
- `w_lint.sh /root/code/KAM-inp-wpk`: exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD
  OK`, `ABI HASHES OK`). `main_shortname_check.py` on the new modules: `short-name check OK`.
- `#print axioms` of the 25 main declarations (e.g. `birkK_isClassA`, `norm_birkK_le`,
  `norm_birkXK_le`, `birk_conjugacy`, `birkK_field`, `birkK2_field`, `lieV_identity`,
  `analyticAt_lieV`, `real_restrict`, `birkGammaR_*`, `birk_transport_tori`,
  `birk_transport_tori_weak`, `birkEmbed_birkXLamInv`): all exactly
  `[propext, Classical.choice, Quot.sound]`.
- No `sorry`, `axiom`, `maxHeartbeats` or other option override in any new file;
  `KAM/Root/Wave.lean` regenerated with `scripts/gen_root_imports.py`.
