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
  (Audit-1 F1, fixed in W3-MAIN-FIX: the bound is now `‖Ψ‖₊ ≤ ‖DΨν‖ + C_*‖Ψ‖³ + C'_K‖Ψ‖⁵`, via the
  single disjoint-support coefficient `c̄ + c^{nor}`; see AUDIT FOCUS below.)

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

## W3-MAIN-FIX (repair of `W3-MAIN-audit-1.md`: F1, F2, F3, N1, hygiene)

Branch `inp-w3main`, worktree `/root/code/KAM-inp-wpka`. Commits: `0176cd0a` (F1), `bdde1482`
(hygiene), `b0f0e487` (F2), `235c5422` (F3), `f7ba7091` (N1), plus this handoff commit.
New modules (`KAM/Wave/Birkhoff/`): `MainQuartSum` (116 lines), `MainYInt` (264), `MainYSeries` (409),
`MainBall` (295), `MainBallReal` (401), `MainGammaRSeries` (128). Changed: `MainWeak`,
`MainRealWeak` (F1), `LieFlow2` (hygiene), all `Main*` modules (F3 rename), `KAM/Root/Wave.lean`
(regenerated by `scripts/gen_root_imports.py`). No statement was weakened and no premise added.

### AUDIT FOCUS

Notation: `ι = birkEmbed a (p+1) p _`, `C_* = waveCubicConst p`, `C_F = birkCF m p`,
`B_{ρ₀} = birkBall0 m p = {40 C_F‖w‖² < 1}`, `B_{ρ₁} = birkBall1 m p = {160 C_F‖w‖² < 1}`,
`ρ₁ = birkRho1 m p = 1/(2√(40 C_F))` (`birkBall1_eq_ball : birkBall1 m p = Metric.ball 0 ρ₁`),
`B^E_{r₁} = birkRealBall1 m p = {320 C_F‖x‖² < 1}`, `r₁ = birkRealRho1 m p = ρ₁/√2`
(`birkRealBall1_eq_ball`). Values in `𝔚⁺` are `BirkSpace` points read at weight `p+1`.

**F1 (combined quartic estimate, blueprint 837–855).** `MainQuartSum.lean`:
- `birkGradML_add` (:37), `birkQuartX_add` (:52): `∇𝔓` and `X_P` are additive in the coefficient
  (`c₃ = c₁ + c₂` pointwise ⇒ `X_{P₃} = X_{P₁} + X_{P₂}`).
- `birkBarNorSet = birkBarSet ∪ birkNormalSet`, `birkCoefBarNor = 𝔤·1_{birkBarNorSet}` (:61, :64),
  `birkCoefBarNor_isCoef` (:66), `birkBarSet_disjoint_birkNormalSet` (:73),
  `birkCoefBarNor_eq : birkCoefBarNor x = birkCoefBar x + birkCoefNor x` (:80).
- `birkHamBarX_add_birkHamNorX (w) : X_Ḡ w + X_{G^{nor}} w = birkQuartX … birkCoefBarNor_isCoef w` (:98).
- `norm_birkHamBarX_add_birkHamNorX_le (w) : ‖X_Ḡ(w) + X_{G^{nor}}(w)‖ ≤ C_* * ‖w‖^3` (:107).
- Consumed in `norm_birkRestFieldExt_le` (`MainWeak.lean:102`): `‖birkRestFieldExt w‖ ≤ C_*‖w‖³ +
  66 C_* C_F ‖w‖⁵`; hence `birk_transport_tori_weak` (`MainBallReal.lean:319`) and
  `birk_transport_tori_weak_real` (`MainBallReal.lean:336`) now conclude
  `‖y‖ ≤ ‖D θ‖ + waveCubicConst p * ‖Ψ θ‖ ^ 3 + 66 * waveCubicConst p * birkCF m p * ‖Ψ θ‖ ^ 5`
  (no factor `2`). Public restricted form: `norm_birkRestField_le` (`MainBallReal.lean:311`).

**F2 (`bpW:w3:Yseries`, blueprint 613–630).** `MainYInt.lean`, `MainYSeries.lean`:
- `birkGammaDPlus (t : Set.Ioo (-2) 2) (w : birkBall0 m p)` (`MainYInt:170`): `DΓ_t(w)` on `𝔚⁺`,
  characterized by `birkGammaDPlus_embed : ι ∘ birkGammaDPlus t w = birkGammaD t w ∘ ι` (:185);
  `birkGammaDPlusInv t w = Ring.inverse (birkGammaDPlus t w)` (:176) is a two-sided inverse
  (`birkGammaDPlus_mul_inv` :195, `birkGammaDPlusInv_mul` :199; `isUnit_birkGammaDPlus` :190),
  `‖·‖ ≤ 2` (:204), `birkGammaD t w (ι (inv f)) = ι f` (:217).
- The integrand (`MainYInt:233`):
  `birkY (t : Set.Icc 0 1) (w : birkBall1 m p) = birkGammaDPlusInv ⟨t,_⟩ ⟨w,_⟩ (X_{Z'}(Γ_t w)) - X_{Z'}(w)`
  with `X_{Z'} = birkHamZX`, i.e. literally `Y(t,w) = DΓ_t(w)⁻¹ X_{Z'}(Γ_t w) - X_{Z'}(w)`.
  `birkY_eq_tsum` (:240): `birkY t w = Σ' n, t^n • V_n(w,…,w) - V_0(w,…,w)`.
- Coefficients (`MainYSeries:45`): `birkYj j : ContinuousMultilinearMap ℂ (Fin (2j+3) → 𝔚) 𝔚⁺`,
  `birkYj 0 = 0` (:56), `birkYj j = birkVn j` for `j ≠ 0` (:59).
- `summable_norm_birkYj` (:132) and `tsum_norm_birkYj_le` (:139):
  `∑' j, ‖birkYj j‖ * ρ₁ ^ (2j+3) ≤ 4 * waveCubicConst p * ρ₁ ^ 3`.
- `birkY_hasSum (t) (w)` (:180): `HasSum (fun j => (t:ℝ)^j • birkYj j (fun _ => w)) (birkY t w)`,
  absolutely: `summable_norm_birkY_terms` (:172).
- `birkYInt (w : birkBall1 m p) = ∫ t in (0:ℝ)..1, Set.IccExtend zero_le_one (birkY · w) t` (:198),
  the Bochner interval integral of the integrand on `[0,1]`;
  `birkYInt_hasSum` (:202): `HasSum (fun j => (1/((j:ℝ)+1)) • birkYj j (fun _ => w)) (birkYInt w)`;
  `birkYInt_eq_tsum` (:232).
- Formal series (`:50`) `birkYSeries`: `birkYSeries_odd (j) : birkYSeries (2j+3) = (1/((j:ℂ)+1)) • birkYj j`
  (:253), `birkYSeries_eq_zero (n) (hn : ∀ j, n ≠ 2j+3) : birkYSeries n = 0` (:273).
  `hasFPowerSeriesOnBall_birkYInt (f) (hf : ∀ w : birkBall1 m p, f w = birkYInt w) :
  HasFPowerSeriesOnBall f birkYSeries 0 (ENNReal.ofReal ρ₁)` (:283);
  `analyticOnNhd_birkYInt (f) (hf) : AnalyticOnNhd ℂ f (birkBall1 m p)` (:314).
- Reality (:399) `birkYInt_rho (w) : birkYInt ⟨ϱ w, _⟩ = ϱ (birkYInt w)`.
- Link to the remainder: `birkYInt_eq_birkXK2 (w) : birkYInt w = birkXK2 w` (`MainBall:222`).
- Route deviation (statements unaffected): `Y_j` are the pullback coefficients `V_j` of the
  triangular recursion (W3-MAIN), not the Neumann-composite majorant series; the identity with the
  literal integrand is proved through the `𝔚⁺`-inverse. The sum bound is proved from
  `‖V_j‖ρ₁^{2j} ≤ 4C_*(1/8)^j` (actually `≤ (4/7)C_*ρ₁³`). Reality is obtained from
  `birkYInt = X_{K₂}` and `K₂ ∈ 𝒜(B_{ρ₁})` (`birkK2Ext_isClassA`, `MainYSeries:378`, field reality),
  not by commuting `ϱ` with the integral.

**F3 (restricted public carriers).** All flagged objects are now defined only on their domain via
`Set.domRestrict` of an internal totalized helper; helpers are renamed `…Ext` (theorems about
them `…Ext_…` or `…_aux`) and documented as internal:
- `MainBall.lean`: `birkPsi`, `birkXi`, `birkAF`, `birkBF : birkBall0 m p → …` (:90–:101);
  `birkK1`, `birkK2`, `birkK : birkBall1 m p → ℂ` (:105–:111); `birkXK1`, `birkXK2`,
  `birkXK : birkBall1 m p → BirkSpace` (:114–:121).
- `MainBallReal.lean`: `birkGammaR : birkRealBall1 m p → BirkReal` (:46),
  `birkRestField : birkBall1 m p → BirkSpace` (:50),
  `birkTransportQP (Ψ) (hΨ : ∀ θ, ι (Ψ θ) ∈ birkBall1 m p) (θ)` (:55).
- Analytic / Fréchet statements of maps on a set are stated for every extension:
  `IsBirkExtension f g := ∀ x : U, g x = f x` (`MainBall:35`); `IsBirkClassAOn U P X` (:56): every
  extension of `(P, X)` is in `𝒜(U)`; `IsBirkClassA.congr` (:65).
- Restated main theorems (same names as before, now about the restricted objects; `w : birkBall1 m p`
  unless noted): `birkInvData` (`w : birkBall0`, :150), `birkPsi_embed` (:132), `birkXi_embed` (:137),
  `birkK_eq` (:173), `norm_birkK1_le`/`norm_birkK2_le` (`≤ 5C_*C_F‖w‖⁶`, :177/:182),
  `norm_birkK_le` (`≤ 10C_*C_F‖w‖⁶`, :187), `birkK_rho`, `birkK2_rho` (:192/:198),
  `norm_birkXK1_le` (44), `norm_birkXK2_le` (22), `norm_birkXK_le` (66) (:204–:214),
  `birkK_analyticOnNhd (g) (hg)` (:230), `birkK1_field`/`birkK2_field`/`birkK_field (g) (hg) (w) (v) :
  fderiv ℂ g w v = birkOmegaPlus … (birkX… w) v` (:236–:250), `birkXK1/XK2/XK_analyticOnNhd` (:257–:269),
  `birkK_isClassA : IsBirkClassAOn a p ha _ (birkBall1 m p) birkK birkXK` (:275), `birkK2_isClassA`
  (:280), `birkXK_rho` (:286); `MainBallReal`: `birkGammaR_analyticOnNhd` (:67), `birkGammaR_sub`
  (:76), `birkGammaR_inv` (:84), `birkGammaR_injective` (:89, replaces `birkGammaR_injOn`),
  `birkGammaR_surj (y) (hy : 1280 C_F‖y‖² < 1) : ∃ x : birkRealBall1 m p, birkGammaR x = y` (:93),
  `birkGammaR_hasFDerivAt` (:99), `birkGammaR_symplectic` (:107), `birkH_gammaR` (:116),
  `birkK_real` (:131), `birkXK_real` (:145), `birkK_real_fderiv` (:158), `birkK_real_gradient` (:172),
  `birk_conjugacy` (:197), `birk_transport_tori` (:214), `birk_transport_tori_real` (:236),
  `birk_transport_tori_frozen_coord` (:262), `birk_transport_tori_frozen` (:283),
  `birk_transport_tori_weak` (:319), `birk_transport_tori_weak_real` (:336),
  `birk_transport_tori_weak_frozen_coord` (:364), `birk_transport_tori_weak_frozen` (:382).
  In the transport theorems the field `X_K` is applied as `birkXK ⟨ι (Ψ θ), hΨ θ⟩` and the weak
  right-hand side as `birkRestField ⟨Ψ θ, hΨ θ⟩` (so `hΨ` is the membership hypothesis it was).
- The new F2 objects are restricted from the start (`birkGammaDPlus`, `birkGammaDPlusInv` on
  `(-2,2) × B_{ρ₀}`, `birkY` on `[0,1] × B_{ρ₁}`, `birkYInt` on `B_{ρ₁}`).

**N1 (`bpW:w3:gamma-real` (i), blueprint 784–786).** `MainGammaRSeries.lean`:
`birkGammaRSeries = Π.compFormalMultilinearSeries (((lieSeries T 1).restrictScalars ℝ)
.compContinuousLinearMap 𝒵)` (:32); `birkGammaRSeries_odd (k) (v) : birkGammaRSeries (2k+1) v =
birkPi (lieMulti T k (fun i => birkZR (v i)))` (:46, `Φ_k = lieMulti T k`);
`birkGammaRSeries_even (k) : birkGammaRSeries (2k) = 0` (:63);
`hasFPowerSeriesOnBall_birkGammaR (g) (hg : IsBirkExtension birkGammaR g) :
HasFPowerSeriesOnBall g birkGammaRSeries 0 (ENNReal.ofReal r₁)` (:94).

**Hygiene.** `LieFlow2.lean:178` `ring` → `ring_nf`; also removed two unused `simp` arguments and
two unused section instances (`omit [CompleteSpace E] in`); the file now elaborates warning-free.

Checks: every touched module built with `w_build.sh` (`Build completed successfully`, last runs
3418/3419 jobs for `MainBallReal`/`MainGammaRSeries`; the full `Main*` chain rebuilt after the F3
rename); `w_lint.sh /root/code/KAM-inp-wpka` exit 0 (`check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD
OK`, `ABI HASHES OK`); `#print axioms` of 58 new/restated main declarations (all listed above):
each exactly `[propext, Classical.choice, Quot.sound]`. No `sorry`/`axiom`/option override.

### Not done

- `Π` (= `Re 𝒵⁻¹`) is used for `𝒵⁻¹` in the real series terms; the separate statement that each
  term `Φ_k(𝒵v₁,…,𝒵v_{2k+1})` is real for distinct real arguments (so that `Π` may be replaced by
  `𝒵⁻¹` termwise) is not exported (only the diagonal reality `birkGamma_rho` exists).
- The blueprint's reality step for `∫Y dt` (commuting `ϱ` with the integral) is not formalized as such;
  `birkYInt_rho` is proved via `birkYInt = X_{K₂}` and `K₂ ∈ 𝒜(B_{ρ₁})`.
- The internal `…Ext` helpers are public (distinctly named and documented internal), not `private`,
  because they are consumed across modules (`MainK` … `MainRealWeak`).
- `READY-W3-G4` untouched. No blueprint statement was found false.
