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
