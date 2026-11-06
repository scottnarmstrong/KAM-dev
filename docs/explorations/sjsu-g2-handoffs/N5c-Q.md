# N5c-Q handoff (T2-CONF): the SJSU initial box lies in the tube domain

Worker g2-n5c (session kam-sjsu-g2-70), 6 November 2026. Status: **complete** for the agreed scope. Every
ball hypothesis of N5b's `tubeChart_confinement` that does not depend on the observables is proved for SJSU.
The observable-dependent ones (`hFu`, `hFφ`, `hfd`, `hfper`, `hc`) have generic lemmas, and their numeric
side (`hLF`) is proved against explicit ceilings. There is no `sorry`, `axiom` or `set_option`, every file
is ≤ 1500 lines, and the axioms are only `propext`, `Classical.choice` and `Quot.sound`.

## Interface (agreed with g2-n5b, ruled by kam-g2 at 16:27 UTC)

- **Target.** `KAM.EffectiveStability.Tube.tubeChart_confinement` (`Tube/Check/TubeChart.lean`, N5b), with
  `V = sjsuV` (N5a, real matrix), `B = sjsuB` (N5a), `z = sjsuZStar`, `r = 10⁻⁶`, `ρ = κδ = 2·10⁻⁶`,
  `δ = 10⁻⁶`.
- **Ownership.** N5b owns the observables `sjsuObs j` (tmEval with `g_i = TP.eval`, from F-v1 via N7's
  literal format); N7 supplies the coefficient norms. I supply the generic partial-derivative and
  periodicity lemmas and the SJSU numbers.
- **`hc`.** No separate enclosure: `γ_j := ε_j + μ_j` (`abs_obs_sub_le_of_face`). N5b's face condition is
  `δ + ε_j + γ_j < ρ`. Phase 1's `sup|E_S| ≈ 0.423δ` gives `0.85δ + 10⁻⁹ < δ`, so it fits.

## Files

| file | lines | content |
|---|---:|---|
| `KAM/EffectiveStability/Tube/Initial/Point.lean` (core) | 285 | `hasFDerivAt_tubeCenter`, `abs_fderiv_tubeCenter_le` (β); `zMode`, `exp_tubeChart_angle` (chart angles = angles of `ζ_a = z_a conj z_2`); `unitOK`, `norm_div_norm_sub_le`; `pointZeta`, `pointCenter`, `pointMu`, **`abs_tubeU_le_of_point`**; `abs_obs_sub_le_of_face` |
| `KAM/EffectiveStability/Tube/Initial/Partials.lean` (core) | 156 | `tmEvalPair`; `hasFDerivAt_tmEvalPair`, `differentiable_tmEvalPair`, `fderiv_tmEvalPair_u/φ`, **`abs_fderiv_tmEvalPair_u_le`, `abs_fderiv_tmEvalPair_φ_le`**; periodicity `trig_add_int_mul_two_pi`, `kdot_add_two_pi`, `evalK_add_two_pi`, `TP.eval_add_two_pi`, `tmEvalPair_add_two_pi` |
| `KAM/EffectiveStability/SJSU/Initial/Data.lean` (generated) | 90 | `sjsuZStar` (statement decimals), `sjsuEtaQ`, `sjsuXiQ`, `sjsuQStar`, `sjsuPStar` (`w* = V′ᵀz*` exact), `sjsuNv`, `sjsuA`, `sjsua`, `sjsuBeta`, `sjsuMu`, `sjsuEps`, `sjsuPt₁/₂`, `sjsuFuMax`, `sjsuFphiMax` |
| `KAM/EffectiveStability/SJSU/Initial/Main.lean` | 172 | the SJSU theorems below and their kernel checks |

Generator and mirror (scratch): `.drafts/g2/scratch/N5c-Q/` contains `qgen.py` (exact numbers, circle
points, checks; writes `qdata.json`), `flip.py` (Fu/Fφ estimates from F-v1; writes `fbounds.json`) and
`gen_init.py` (writes `Data.lean` and checks `hLF` exactly). Run `python3 qgen.py && python3 flip.py &&
python3 gen_init.py`.

## Main statements (SJSU, namespace `KAM.EffectiveStability.SJSU`)

```lean
theorem sjsu_hN (j : Fin 3) : ∑ k, |sjsuV k j| ≤ (sjsuNv : ℝ)
theorem sjsu_hAb : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
    |(rotMap sjsuVᵀ y).1 j| + |(rotMap sjsuVᵀ y).2 j| ≤ (sjsuA j : ℝ)
theorem sjsu_ha (j : Fin 3) : 0 < (sjsua j : ℝ)
theorem sjsu_hab : ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), ∀ j,
    (sjsua j : ℝ) ≤ modeSq sjsuV y j
theorem sjsu_hβ (φ : Fin 2 → ℝ) (b : Fin 2) (l : Fin 3) :
    |fderiv ℝ sjsuB φ (Pi.single b 1) l| ≤ (sjsuBeta l : ℝ)
theorem sjsu_hμ (j : Fin 3) : |tubeU sjsuV sjsuB sjsuZStar j| ≤ (sjsuMu : ℝ)
theorem sjsu_hμρ (j : Fin 3) :
    (sjsuMu : ℝ) + chartLip (sjsuNv : ℝ) (fun j => (sjsuA j : ℝ)) (fun j => (sjsua j : ℝ))
      (fun l => (sjsuBeta l : ℝ)) (Pi.single j 1) 0 * (1 / 10 ^ 6) < 2 / 10 ^ 6
theorem sjsu_hLF (j : Fin 3) :
    chartLip (sjsuNv : ℝ) (fun j => (sjsuA j : ℝ)) (fun j => (sjsua j : ℝ))
      (fun l => (sjsuBeta l : ℝ)) (fun l => (sjsuFuMax j l : ℝ)) (fun b => (sjsuFphiMax j b : ℝ)) *
      (1 / 10 ^ 6) ≤ 1 / 10 ^ 6 / 2
theorem sjsu_ball_subset_modesPos :
    ∀ y ∈ Metric.closedBall sjsuZStar (1 / 10 ^ 6), y ∈ modesPos sjsuV
theorem sjsuV_eq_eccV (i j : Fin 3) : sjsuV i j = (sjsuEccV i j : ℝ)
```

The values are `N_V = 1.4972`, `A = (0.03573, 0.050515, 0.010693)`, `a = (6.3818e-4, 1.3371e-3,
5.7227e-5)`, `β = (2.652e-5, 2.887e-5, 3.794e-6)`, `μ = 10⁻⁹`. The ceilings are
`FuMax = [[1.2, 0.03, 0.035], [0.16, 1.1, 0.065], [0.03, 0.002, 1.15]]` and
`FphiMax = [[5e-7, 4e-7], [4e-7, 6e-7], [1e-7, 2e-7]]`.

These cover the brief's three targets:
1. **All modes nonzero on Q:** `sjsu_ball_subset_modesPos`.
2. **`|u_l| < 2·10⁻⁶` on Q:** `sjsu_hμ` and `sjsu_hμρ`, through N5b's mean-value step `hub` inside
   `tubeChart_confinement`. On Q, `|u| ≤ 9.7·10⁻⁸`.
3. **`|F_j − F_j(z*)| ≤ δ/2` on Q:** `sjsu_hLF` (with N5b's `hFb`), once N7's norms meet the ceilings. The
   value is `chartLip·r ≤ 1.19·10⁻⁷` against `5·10⁻⁷`.

N7 supplies the literal `c̃_j` and its face bound; `abs_obs_sub_le_of_face` then supplies
`γ_j = ε_j + sjsuMu` (package audit 1, N2).

## Generic statements (namespace `KAM.EffectiveStability.Tube`)

```lean
theorem abs_tubeU_le_of_point {d : EccData} (hg : globalOK d = true)
    {V : Matrix (Fin 3) (Fin 3) ℝ} {x} (hx : x ∈ modesPos V) {q p : Fin 3 → ℚ}
    (hq : ∀ j, (rotMap Vᵀ x).1 j = q j) (hp : ∀ j, (rotMap Vᵀ x).2 j = p j)
    {s₁ s₂ : Bool} {t₁ t₂ ε₁ ε₂ : ℚ}
    (h₁ : unitOK (pointZeta q p 0) (circPt s₁ t₁) ε₁ = true)
    (h₂ : unitOK (pointZeta q p 1) (circPt s₂ t₂) ε₂ = true) (k : Fin 3) :
    |tubeU V (fun φ k => tubeCenter d.modes d.Ibar k φ) x k| ≤
      (pointMu d q p s₁ s₂ t₁ t₂ ε₁ ε₂ k : ℝ)
theorem abs_obs_sub_le_of_face … (j : Fin 3)
    (hface : ∀ u φ, (∀ l, |u l| ≤ ρ) → |f (u, φ) - ct - u j| ≤ ε)
    (hμ : ∀ l, |tubeU V B z l| ≤ μ l) (hμρ : ∀ l, μ l ≤ ρ) : |f (tubeChart V B z) - ct| ≤ ε + μ j
theorem abs_fderiv_tmEvalPair_u_le (s) (μ) (hg : ∀ i ∈ s, Differentiable ℝ (g i))
    (hG : ∀ i ∈ s, ∀ φ, |g i φ| ≤ G i) (hu : ∀ l, |u l| ≤ ρ) (φ) (l : Fin 3) :
    |fderiv ℝ (tmEvalPair s μ g) (u, φ) (Pi.single l 1, 0)| ≤
      ∑ i ∈ s, (μ i l : ℝ) * ρ ^ mdeg (μ i - Pi.single l 1) * G i
theorem abs_fderiv_tmEvalPair_φ_le (s) (μ) (hg) {b : Fin 2}
    (hG' : ∀ i ∈ s, ∀ φ, |fderiv ℝ (g i) φ (Pi.single b 1)| ≤ G' i) (hu) (φ) :
    |fderiv ℝ (tmEvalPair s μ g) (u, φ) (0, Pi.single b 1)| ≤ ∑ i ∈ s, ρ ^ mdeg (μ i) * G' i
theorem tmEvalPair_add_two_pi (s) (μ)
    (hg : ∀ i ∈ s, ∀ φ (m : Fin 2 → ℤ), g i (φ + fun a => 2 * Real.pi * m a) = g i φ) :
    ∀ u φ (m : Fin 2 → ℤ), tmEvalPair s μ g (u, φ + fun a => 2 * Real.pi * m a) = tmEvalPair s μ g (u, φ)
```

## Approach

- **Ball.** N5b's `modeBounds_of_mem_closedBall` turns the exact centre `w* = V′ᵀz*` into `A`, `a`. The
  rational inequalities are checked by `decide +kernel` in `ℚ` and cast to `ℝ`.
- **β.** `B = tubeCenter` (N6's centre, which N5a's `sjsuB` is by definition). Its derivative is
  `Σ_m m_l σ_m sin(m·φ) m_b`, bounded by N6's Lipschitz sums `lipSum`. Those are bounded by `L₁`, `L₂`
  through N6's kernel-checked `sjsuEcc_globalOK`.
- **`u(z*)`.** The chart angles at `x` satisfy `e^{iφ_a} = ζ_a/|ζ_a|`, with `ζ_a = z_a conj z_2` and
  `z_j = p_j − i q_j` (from N2's `polarInv`, `arg`). For SJSU, `ζ_a` is an exact Gaussian rational. The
  rational circle points `circPt s t` (N6), with `t` dyadic of 40 bits, are within `ε = 10⁻⁹` of
  `ζ/|ζ|`, by the test `c²|ζ|² ≤ Re(ζ conj P)²` with `c = 1 − ε²/2`. From there N6's chain applies: the
  Lipschitz step, the fixed-point rounding step, and the Gaussian-integer evaluation `bSumZ`. It gives
  `|u_k(z*)| ≤ |I_k − B̃_k(P)| + εL₁ + εL₂ + τ_k ≈ 1.2·10⁻¹² ≤ 10⁻⁹`. The float value is
  `u(z*) ≈ (2.1, 1.3, −1.6)·10⁻¹⁹`; the slack is the fixed-point truncation of σ (τ ≈ 10⁻¹²).
- **Partials.** These are product and chain rules on the pair space, plus N3's `fderiv_umon` and
  `abs_umon_le`.

## Checks

- **Builds** (`.drafts/g2/g2lake build`): `KAM.EffectiveStability.SJSU.Initial.Main`,
  `KAM.EffectiveStability.SJSU.Ecc.Main` and `KAM.EffectiveStability.Tube.Initial.Partials` give "Build
  completed successfully (2975 jobs)" with no warnings in my files. That run also rebuilt and re-checked
  all of N6: Data 45 s, TreePM 39 s, TreeMM 47 s, TreeMP 58 s, TreePP 75 s. `Initial.Main` takes 2.8 s, its
  kernel checks included: the point enclosure is one `bSumZ` evaluation.
- **`#print axioms`** (`.drafts/g2/scratch/N5c-Q/Axioms.lean`): `sjsu_hN`, `sjsu_hAb`, `sjsu_ha`,
  `sjsu_hab`, `sjsu_hβ`, `sjsu_hμ`, `sjsu_hμρ`, `sjsu_hLF`, `sjsu_ball_subset_modesPos`, `sjsuV_eq_eccV`,
  `abs_tubeU_le_of_point`, `abs_obs_sub_le_of_face`, `abs_fderiv_tmEvalPair_u_le`,
  `abs_fderiv_tmEvalPair_φ_le`, `differentiable_tmEvalPair`, `tmEvalPair_add_two_pi`,
  `TP.eval_add_two_pi` and `sjsu_tube_ecc` all show `[propext, Classical.choice, Quot.sound]`.
- **Line lengths:** none over 100 in my files (`awk 'length > 100'`).
- **Lint:** `.drafts/g2/lint_noabi.sh`; result in the section "Lint result". `abi_hashes` was skipped, per
  the rule.

## Changes to my committed N6 (kam-g2 informed)

- `KAM.EffectiveStability.SJSU.sjsuB` in `SJSU/Ecc/Main.lean` is renamed to **`sjsuEccCenter`** (ruling of
  16:27). It clashed with N5a's `sjsuB` in `SJSU/Ham/Center.lean`. The two are the same function up to
  argument order: N5a's `sjsuB φ k` is literally `tubeCenter sjsuEccModes sjsuEccIbar k φ`, so no equality
  lemma is needed (`rfl`).
- `KAM.EffectiveStability.Tube.pairSum/treeSum/treeSum_eq/pairSum_sum` in `Tube/Ecc/Defs.lean` and
  `Center.lean` are renamed to **`pairSumQ/treeSumQ/treeSumQ_eq/pairSumQ_sum`**. N3's `Trig/Poly.lean`
  defines ℤ versions with the same names, so importing N3 and N6 together failed. A scan of `Tube/` and
  `SJSU/` finds no other duplicate full names. The N6 handoff still says `treeSum`; read `treeSumQ`.

## Design signals

None at default heartbeats. The `treeSum` clash between packages is noted above.

## Uncertainties

- `hLF` uses my ceilings. N7's norms must meet them for the pruned F (≥ 5 % headroom over the full F-v1
  values). The ceilings are generous for `Fφ` and for the off-diagonal `Fu`. If a norm comes out above a
  ceiling, the generator changes one number and the margin in `hLF` (a factor ≥ 4.2) absorbs it.
- The face condition `δ + 2ε_j + μ < ρ` depends on N7's face bound `ε_j`: phase 1 gives 0.42δ, with
  margin 0.15δ.

## Deviations from the brief

- **No direct enclosure of `F_j(z*)`.** Targets 2 and 3 are proved through N5b's checker with the
  hypotheses supplied here, and `c̃_j`, `γ_j` come from the face bound instead of a direct enclosure. This
  was agreed with g2-n5b and accepted by kam-g2.
- **`f_j`-dependent bounds are reduced to coefficient norms.** The bounds that depend on `f_j` reduce to
  N7's coefficient norms through the generic lemmas, because `f_j` is defined by N5b/N7 (kam-g2's ruling).

No suspected errata in pinned sources.

## Lint result

`.drafts/g2/lint_noabi.sh` (16:43–16:53 UTC; **`abi_hashes` skipped**) exited 1, with none of the
causes in my files:
- **Lines over 100 characters:** none in my files. The 32 hits are in other workers' directories.
- **`KAM.lean is out of date (KAM/Root/EffectiveStability.lean)`:** the generated roots are kam-g2's step
  (rule 10). `Tube/Initial/*` belong in `KAM`; `SJSU/Initial/*` belong in `KAMSJSU`.
- **The frozen-anchor guard crashed:** `FileNotFoundError: KAM/EffectiveStability/SJSU/Ham/Hw/D3P0.lean`.
  N5a's directory was being regenerated during the run, so this is not about my files.
- **Passed:** `check_lean_modules: PASS (18407 Lean files)` and the unit tests (29 + 8) `OK`.

**Stability.** g2-n5b's `SJSU/Confinement/Statement.lean` (`sjsu_secular_confinement_of_obs`) now uses my
names as they are (`sjsu_hN`, `sjsu_hAb`, `sjsu_ha`, `sjsu_hab`, `sjsu_hβ`, `sjsu_hμ`, `sjsu_hμρ`,
`sjsu_hLF`, `sjsuV_eq_eccV`, `sjsuZStar`, `sjsuMu`, `sjsuFuMax`, `sjsuFphiMax`,
`abs_obs_sub_le_of_face`) and builds; it also picked up `treeSumQ_eq`. Do not rename these without
telling g2-n5b. The face margin left for N7 is `10⁻⁶ + ε_j + (ε_j + sjsuMu) < 2·10⁻⁶`.
