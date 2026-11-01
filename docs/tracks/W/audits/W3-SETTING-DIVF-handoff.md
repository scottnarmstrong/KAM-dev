# Combined audit handoff: W3-SETTING + W3-DIVISOR-F (commit 47fa21b9, detached audit worktree)

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
- `w_lint.sh /root/code/KAM-inp-wpk`: exit 1 at 32c9b184 because of over-100-column lines (fixed in the following commit: exit 0); tail `check_lean_modules: PASS (3576 Lean files, 0 comparator configurations)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 frozen declarations of KAM; ...)`. It also prints an informational list of Lean lines over 100 columns (some in my files, 101-108 wide; not a failure, to be wrapped in a cleanup).
- `main_shortname_check.py` on all modules: `short-name check OK (no reused public short name)`.
- `#print axioms` of 95 main declarations: all exactly `[propext, Classical.choice, Quot.sound]`.
- `KAM/Root/Wave.lean` regenerated with `scripts/gen_root_imports.py` (no hand edit).

# Handoff W3-DIVISOR-F (branch inp-wpk; group 2 of blueprint-W part W3)

Labels: `bpW:w3:divisor`, `bpW:w3:Fdef`, `bpW:w3:F`, `bpW:w3:homological`. Modules (all `KAM/Wave/Birkhoff/`, namespace `KAM.Wave`,
each < 330 lines; no heartbeat/recursion overrides, no `sorry`/axiom), built on W3-SETTING (commit 32c9b184) and landed
`KAM/Wave/Normal`, `KAM/Wave/Cubic`. Import order: DivisorReal, DivisorCore, Divisor, FCoef, FForm, HomSum, Homological.

## Labels -> declarations
- `bpW:w3:divisor`
  - DivisorReal: `birkL` (`= √(k²+m)`, `lam_eq_birkL`), exact second difference without calculus
    `birkL_second_diff` (`L(k)+L(k+2)-2L(k+1) ≥ m/L(k+2)³`, from `(p+r-2q)(p+r+2q)(pr+q²-1)=8m`), `birkDelta_mono`,
    `birkDelta_ge` (`Δ(a) ≥ a/L(a)`), `birkL_add_ge`, `birkL_incr_mono`, `birkL_incr_sub`.
  - DivisorCore (sorted `1 ≤ a ≤ b ≤ c ≤ d`, `β = m/(27 L(a)³)`): `birkDiv_C0` (no minus), `birkDiv_C1` (one minus, needs
    `d ≤ a+b+c`; Step s1), `birkDiv_C3` (outer pairs), `birkDiv_C2`, `birkDiv_C1i` (inner pair, `d+a=b+c`, uses
    `birkL_second_diff` and `(a+2)² ≤ 9a²`), `birkDiv_C1ii` (inner pair, `d=a+b+c`).
  - Divisor: `birk_divisor_sorted` (all 16 sign patterns, the subcase i=j<k=l is covered by `birkDiv_C3`/`C2` with
    `¬paired ⇒ ¬(all equal)`), `birk_divisor_bound` (statement: `x` with `∃ ε, Σ ε_t|x_t| = 0`, not paired, `n=|x_{t₀}|`
    minimal: `m/(27(n²+m)^{3/2}) ≤ |δ_x|`), `birkDeltaStar m = m/(27(4+m)^{3/2})`, `birk_divisor_bound_tan`
    (`x∈𝒯`, `𝔤_x≠0`, not paired ⇒ `δ_* ≤ |δ_x|`; selection rule from landed `quarticSel_of_quarticCoeff_ne_zero`).
- `bpW:w3:Fdef`, `bpW:w3:F`: FCoef: `birkFx` (`f_x = 𝔤_x/δ_x` on `𝒯∖paired`), `birkFcoef = iδ_*f_x`, `birkFx_perm`,
  `birkFx_neg`, `abs_birkFx_le`, `birkFcoef_isCoef`. FForm: `birkFform = δ_*⁻¹𝔓_c`, `birkFgrad`, `birkS = 4∇𝔉`,
  `birkCF m p = C_*/δ_*`, `birkF_isSmoothing` (constant `C_*/(4δ_*)`), `norm_birkS_le` (`‖S‖₊ ≤ C_F ∏‖w^t‖`),
  `birkS_pairing` (`Ω(S(w¹,w²,w³),v)=4𝔉(w¹,w²,w³,v)`), `birkS_perm` (symmetry), `birkS_rho` (reality), `birkF_real`,
  `norm_birkF_le` (`|F(w)| ≤ (C_F/4)‖w‖⁴`), `birkXF_eq` (`X_F(w)=S(w,w,w)`), `birkF_isClassA` (F ∈ 𝒜(𝔚), `X_F` analytic into 𝔚⁺),
  `IsBirkSmoothing.birkScale`.
- `bpW:w3:homological`: HomSum `summable_birkLamQuartTerm` (absolute convergence of `Σ_x λ_{|x₄|} c_x w_x`);
  Homological `birk_delta_mul_fx` (`δ_xf_x = -(c̄_x - c^{tan}_x)`), `birk_euler` (symmetrization),
  `birk_DLam_XF` (`DΛ(w)X_F(w) = -(1/4)Σλ'_{x₄}f_xw_x`), **`birk_homological`**: for every `w ∈ 𝔚`,
  `DΛ(w)·ι X_F(w) = Ḡ(w) - G^{tan}(w)` (`ι: 𝔚⁺ ⊂ 𝔚`), and `birk_homological'`: `G + DΛ·X_F = Ḡ + G^{nor}`.

## Notes / deviations
- The divisor lemma is stated with the minimum attained at `t₀` (no sorting in the statement); the sorting is internal
  (`Tuple.sort`). The selection rule is taken as `∃ε` (all 16 patterns handled), as in the blueprint.
- The calculus steps of the blueprint proof (`f''` integrals) are replaced by the exact algebraic second-difference
  identity; the constants (`27`, `δ_*`) are the blueprint's.
- No blueprint defect found.

## Checks
- Gate: `w_build.sh /root/code/KAM-inp-wpk KAM.Wave.Birkhoff.{DivisorReal,DivisorCore,Divisor,FCoef,FForm,HomSum,Homological}`
  -> `Build completed successfully (3331 jobs).`
- `#print axioms` of 27 main declarations (list in `/tmp` script; includes `birk_divisor_bound`, `birk_divisor_bound_tan`,
  `birkF_isSmoothing`, `birkS_perm`, `birkS_rho`, `birkF_isClassA`, `birk_euler`, `birk_homological`, `birk_homological'`):
  all exactly `[propext, Classical.choice, Quot.sound]`.
- `main_shortname_check.py` on all 26 Birkhoff modules: `short-name check OK`. (`IsBirkSmoothing.smul` was renamed `birkScale` after a reuse hit.)
- `w_lint.sh /root/code/KAM-inp-wpk`: exit 0 (tail `check_lean_modules: PASS (3583 Lean files ...)`, `FROZEN-ANCHOR GUARD OK`, `ABI HASHES OK (177 ...)`), no over-100-column lines.
- Correction to the W3-SETTING handoff: its recorded `w_lint.sh exit 0` was wrong at commit 32c9b184 (the width check made it exit 1); all Birkhoff files were re-wrapped to <= 100 columns in this round and the whole 26-module chain rebuilt (`Build completed successfully (3331 jobs)`); axioms of the 95 W3-SETTING and 27 new declarations re-checked: all exactly `[propext, Classical.choice, Quot.sound]`.

## AUDIT FOCUS (sub-orchestrator kam-d4)

Two packages, together the first two lemma groups of blueprint W3 (w3-birkhoff.tex). They are on the critical path to
nlw2 (W5 and W8 consume them). No provider and no seal, so skip audit item 1. Compare with inp:
`git diff inp...HEAD -- KAM/Wave/Birkhoff`.
1. Statement fidelity per label against the CURRENT inp blueprint W3. In particular:
   - `quartic-ident`: Ḡ with the corrected A, B, through the landed nonresonance;
   - `divisor`: the constant m/(27(n²+m)^{3/2}) for all 16 sign patterns, including the subcase i=j<k=l, and δ_*;
   - `F`: S into 𝔚⁺ with C_F, reality, symmetry;
   - `homological`: DΛ(w)·X_F(w) = Ḡ(w) − G^tan(w) on ALL of 𝔚.
2. The weighted-coordinate model (BirkSpace = lp over Bool × ℕ+), `birkEmbed`, `birkZ`, and the class `IsBirkClassA`
   (analytic P and X into 𝔚⁺). Are they faithful realizations of the blueprint's 𝔚, 𝒵 and 𝒜(U)?
3. Definitions on their whole carrier, with no junk values relied on.
4. Hygiene. This is a slim worktree; lint only via w_lint.sh; replay the 26 modules (capped). Regenerated roots are
   authorized.
