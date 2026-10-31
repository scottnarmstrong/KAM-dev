# Handoff W3-SETTING (branch inp-wpk)

Package: first lemma group of `blueprint-W/parts/w3-birkhoff.tex` (setting of the analytic Birkhoff normal form).
19 modules `KAM/Wave/Birkhoff/*.lean`, namespace `KAM.Wave`, each < 400 lines (3.9k lines total); no heartbeat or
recursion overrides, no `sorry`/axiom. Built on landed `KAM/Wave/{Seq,Algebra,Analytic,Normal,Cubic,...}`.
Import order: Space, Coords, Omega, HamClass, Forms, Lambda, Reindex, Majorant, Fold, QuartGrad, QuartML, QuartSum,
QuartForm, QuartMain, QuartIdent, QuartNormal, QuartPaired, QuartBar, QuartBarAlg.

Conventions. `BirkIdx = Bool × ℕ+` (sign, |l|), `BirkSpace = lp (BirkIdx → ℂ) 2` is 𝔚 in *weighted coordinates*
(`birkCoord a r y l = y_l/ω_{a,r}(|l|)`); a map into 𝔚⁺ is a map into `BirkSpace` read at weight `p+1`
(embedding `birkEmbed a r r' : 𝔚_{a,r} → 𝔚_{a,r'}`, norm ≤ 1). Results are parametric in `a ≥ 0`, `p ≥ 1/2`.

## Labels -> declarations
- `bpW:w3:space`: `BirkIdx`, `BirkSpace`, `birkCoord`, `birkEmbed`(`_injective`, `norm_birkEmbed_le`, `birkCoord_birkEmbed`),
  `birkRho` (conj-linear isometric involution, `birkCoord_birkRho`), `lpDiagCLM` (+ unboundedness lemma).
- `bpW:w3:coords`: `birkZ`, `birkZinv`, `birkZEquiv`, `norm_le_norm_birkZ`, `norm_birkZ_le`, `norm_birkZinv_le`,
  `birkCoord_birkZ_true/false` (any weight), `birkCoord_mul_birkZ`, `birkRho_birkZ_real`, `exists_birkZ_of_birkRho_eq`,
  `birkReal`, `birkReal_injective`.
- `bpW:w3:omega`: `birkOmega`, `norm_birkOmega_le`, `birkOmega_antisymm`, `birkOmega_unit_neg`,
  `birkOmega_nondegenerate`, `birkOmega_birkRho`, `birkOmega_birkZ` (and `_real`).
- `bpW:w3:hamfield-def`: `IsBirkHamField`, `IsBirkClassA` (open ϱ-invariant U, real, `AnalyticOnNhd ℂ` P and X into 𝔚⁺),
  `BirkClassA`, `birkField_eq` (uniqueness), `birkField_coord`, `IsBirkClassA.field_rho` (X∘ϱ=ϱ∘X).
- `bpW:w3:forms`: `IsBirkSmoothing`, `birkDiag`, `birkDiagField`, `birkDiag_field`, `norm_birkDiag_le`,
  `norm_birkDiagField_le`, `norm_birkDiagField_sub_le`, `birkDiag_analyticOnNhd`, `birkDiagField_analyticOnNhd`,
  `birkDiag_isClassA`.
- `bpW:w3:Lambda`: `birkLamBil`, `birkLambda`, `norm_birkLambda_le`, `birkLambda_analyticOnNhd`, `birkLambda_birkZ`,
  `fderiv_birkLambda_apply`, `birkXLam`, `norm_birkXLam_le`, `birkLambda_field`, `not_exists_birkXLam_bounded`.
- `bpW:w3:majorant`: `birkMajorant`, `birkMajorant_eq` (displayed formula), `birkMajorant_bound` (constant `waveCubicConst p`).
- `bpW:w3:quartic`: `IsBirkQuartCoef`, `birkGradML` (∇𝔓, `norm_birkGradML_le` = C_*/4), `birkQuartForm`, `birkQuartForm_perm`,
  `birkQuartForm_rho`, `birkQuart_isSmoothing`, `birkQuart_isClassA`, `norm_birkQuartP_le` (C_*/4 ‖w‖⁴),
  `norm_birkQuartX_le` (C_* ‖w‖³), `norm_birkQuartX_sub_le`, `isBirkQuartCoef_on` (coefficient 𝔤·1_S for the sets
  (ℤ∖0)⁴, 𝒯, 𝒯∩paired, 𝒯ᶜ: `birkCoefAll/Tan/Bar/Nor`), gradient formula `birkCoord_birkGradML`, pairing `birkQuartSum_eq_omega`.
- `bpW:w3:quartic-ident`: `birkQuartP_birkZ` (G(𝒵x)=¼Σg q̂⁴, all a≥0), `birkQuartP_birkZ_real` (= landed `waveG`, a>0),
  `birkZinv_birkQuartX_birkZ` (𝒵⁻¹X_G(𝒵x) = landed `waveXG`, i.e. (0,−T(q,q,q))), `birkQuartP_normal`,
  `birkQuartX_normal`, `birkQuartX_tangential`, `norm_birkQuartP_normal_le`, `norm_birkQuartX_normal_le`,
  `birkPaired_iff_divisor` (𝔤_x≠0: δ_x=0 ⇔ paired, via landed `quartic_nonresonance`),
  `birkQuartP_all_eq_tan_add_nor`, and `birkQuartP_bar`: for every w ∈ 𝔚 (complex),
  Ḡ(w)=½Σ_{i,i'}A_{ii'}I_iI_{i'}+Σ_{j≥3,i}B_{ji}I_iI_j with landed `actionA` and `birkActionB` (`birkActionB_eq`: = landed `actionB`).
  The counting (6 sign patterns, 24/6 orderings) is `birkV_sum_eq_six`, `birkV_s0_eq`, `tsum_tan_split`.

## Not done / notes
- `bpW:w3:real-restrict` (not in this package's list) is not proved.
- `bpW:w3:Lambda`: the formula Λ(𝒵x)=½Σλ_j(q_j²+p_j²) is proved for all complex x (hence real x); bound is exactly √(1+m)‖w‖².
- The "holomorphic ⇐ analytic" sentence of hamfield-def is not restated (Mathlib: analytic ⇒ differentiable).
- For a=0 the G(q) identification is the series form `birkQuartP_birkZ`; `waveG` form needs a>0 (landed hypothesis).
- No blueprint defect found; the factor `T` in the last claim of quartic-ident is not needed for the nonresonance equivalence.

## Checks
- Gate: `w_build.sh /root/code/KAM-inp-wpk <19 modules in import order>` -> tail `Build completed successfully (3324 jobs).`
- `w_lint.sh /root/code/KAM-inp-wpk`: exit 0; tail `check_lean_modules: PASS (3576 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 frozen declarations of KAM; ...)`. It also prints an informational list of Lean lines over 100 columns (some in my files, 101-108 wide; not a failure, to be wrapped in a cleanup).
- `main_shortname_check.py` on all modules: `short-name check OK (no reused public short name)`.
- `#print axioms` of 95 main declarations: all exactly `[propext, Classical.choice, Quot.sound]`.
- `KAM/Root/Wave.lean` regenerated with `scripts/gen_root_imports.py` (no hand edit).
