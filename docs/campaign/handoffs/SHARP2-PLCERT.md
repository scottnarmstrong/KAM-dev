# SHARP2-PLCERT: a closed theorem at PlasmaLean's frequency and strip

Branch `sharp-plcert`, from `sharp-v2` at 13e06ff9. Opus 5.5.

## Result

`KAM.Sharp2.Examples.plasmaLean_torus`: certified threshold **e\* = 1.93·10⁻¹⁷ = 10^(−16.71)**, exact
rational `193/10^19`. This is above the design's float value 10^(−17.27) by 0.56 orders, and 33.9 times
PlasmaLean's tolerance 5.7·10⁻¹⁹ (10^(−18.24)). There is no float in the proof and no numerical
hypothesis.

Classical variant `plasmaLean_classical`: threshold `4.85·10⁻⁶ γ⁴ δ₀⁴`, which is **10^(−18.67)** at
γ = 0.1374 and **10^(−19.88)** at γ = 0.0687 (design: −20.01 at γ = 0.0687). The classical variant
alone does not reach PlasmaLean's tolerance at any admissible γ: the frequency certificate is what
gives the 1.96 orders.

The comparison with PlasmaLean is not like for like. See "Uncertainties".

## The theorem

```lean
theorem plasmaLean_torus {𝔅 : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    {h : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {e : ℝ}
    (hO : CALike 𝔅 h K omegaStar)
    (hE : ∀ θ ∈ complexStrip 2 (1 / 50), ‖invarianceError h K omegaStar θ‖ ≤ e)
    (he : e ≤ 193 / 10 ^ 19) :
    ∃ Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ),
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError h Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ 𝔅) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - K θ‖ ≤ 22226503 * e
```

with `omegaStar = ![iota, 1]`, `iota = (75 + √5)/562`. `CALike` is a structure of explicit object
bounds and nothing else (`KAM/Sharp2/Examples/PlasmaLean/Core.lean`):

| field | content |
|---|---|
| `isOpen`, `transl`, `holo`, `periodic`, `real` | the standing structure of `h` on `𝔅` |
| `bounds` | `‖Dh‖, ‖X_h‖, ‖DX_h‖, ‖D²X_h‖ ≤ 3` on `𝔅` (M = 3.0) |
| `torus_holo`, `primary`, `torus_real` | `K` holomorphic, primary, real on the strip ρ = 1/50 |
| `ball` | `ball (K θ) (1/160) ⊆ 𝔅` |
| `deriv_le` | `‖DK‖ ≤ 31/10` (σ_K 3.1) |
| `gram` | Gram matrix invertible, row sums of the inverse ≤ 2 (σ_B 2.0) |
| `twist_unit`, `twist_le` | `⟨T⟩` invertible, row sums of the inverse ≤ 50/11 (twist ≥ 0.22) |
| `torsion_le` | `‖T‖ ≤ 496/25` (19.84) on `T_{ρ-δ₀}` |

The transposes are not hypotheses: `‖Lᵀ‖ ≤ 12.4`, `‖N‖ ≤ 6.2`, `‖Nᵀ‖ ≤ 24.8` are derived by
`frame_bounds` (the conservative defaults).

## Data of the run

ρ = 1/50, ρ∞ = 1/50000, δ₀ = 333/100000, μ = 1/160, M₁ = M₂ = 3, τ = 1, γ = γ̄ = 687/5000 = 0.1374.
The infimum of |k|₁|k·ω\*| is ι = 0.13743…, attained at k = (1, 0), so γ = 0.1374 is essentially
sharp; the design's 0.0687 is PlasmaLean's convention.

| | frequency | classical |
|---|---|---|
| prefix length | 3 | 5 |
| X⋆ | 441/10⁶ (true edge 4.415·10⁻⁴) | 485/10⁸ (edge 4.859·10⁻⁶) |
| caps sB, sT | 2.0002, 6.1 | 2.0003, 4.8 |
| sLt, sN, sNt | 12.4001, 6.2002, 24.8005 | same |
| t, ϑ | 19.88, 19/100 | 19.86, 3/100 |
| c(δ_s) | .01524, .01512, .01508 | .08184, .08161, .08150, .08144, .08141 |
| c̄(r_s) | .01778, .01612, .01540 | .08411, .08276, .08207, .08173, .08156 |
| c_tail | .08144 at δ₃ | .08139 at δ₅ |

Prefix length: with the frequency constants the threshold is flat past 3 (−16.75 at both 3 and 4 in
a coarser model), so `δ₃` and `r₃` were not certified. The gain over the design's −17.27 comes from
tight cap budgets (0.01–0.03% on `sB`, `sLt`, `sN`, `sNt` against the design's 5%), not from the
frequency constants. `c_tail` is the classical constant at the actual entry bite δ_kp (audit F2, F3).

## Files

- `KAM/Sharp2/Examples/PlasmaLean.lean` (290): the two closed theorems, the two runs, certificates.
- `KAM/Sharp2/Examples/PlasmaLean/Core.lean`: `CALike`, `CAVar`, `cALike_core` (`g1_branch_A` at the
  data, with the derived frame bounds).
- `KAM/Sharp2/Examples/PlasmaLean/Bites.lean`: the six small-divisor certificates.
- `KAM/Sharp2/Examples/PlasmaLean/Balanced.lean`: the balanced checker, soundness,
  `sdConst_two_of_sdSum`.
- `KAM/Sharp2/Examples/PlasmaLean/Frequency.lean`: `iota`, `omegaStar`, the Diophantine pair, the box.
- `KAM/Sharp2/Examples/PlasmaLean/ClassicalConst.lean`: `cohConstC_two_one_le`, a rational test for
  `c♮(2, 1, δ) = √((π²/6 - 1)(1 + 8πδ/e²))/π²`.
- `KAM/Sharp2/Examples/MirrorQ.lean`: the rational mirror of route A at τ = 1, with `NumQ.ok_sound`
  into `routeAOk`.
- `KAM.lean`: regenerated.

## Kernel cost

Measured with `lake env lean -Dprofiler=true`, one niced process. `balCheck` is the side test, `balBound`
the rational sum; `l` is the cut-off `N = 2^l`.

| bite b | l | bound B of S(ω\*, b) | `balCheck` | `balBound` | c |
|---|---:|---:|---:|---:|---:|
| δ₀ = .00333 | 9 | 10938 | 7.0 s | 9.6 s | .01524 |
| δ₁ = .001665 | 10 | 43107 | 13.9 s | 13.5 s | .01512 |
| δ₂ = .0008325 | 11 | 171512 | 15.6 s | 26.8 s | .01508 |
| r₀ = .02 | 6 | 413.02 | 0.38 s | 0.62 s | .01778 |
| r₁ = .01001 | 7 | 1355.3 | 0.79 s | 1.26 s | .01612 |
| r₂ = .005015 | 8 | 4928 | 1.69 s | 2.2 s | .01540 |

Total 93 s of kernel time; `Bites.lean` builds in 82 s. The remaining `decide +kernel` calls
(`iotaData_check`, `freqVar_ok`, `freqVar_close`, `classicalVar_ok`, `classicalVar_close`) are each
under 1 s (`PlasmaLean.lean` builds in 3.4 s in total).

C2's `SdsData.fiberBound` is a linear `Finset.sum`. In exact ℚ the cost is fine, but the kernel fails
somewhere between N = 764 and N = 1529 with a misleading "failed to reduce" (the claim was true: the
value was 171609 against a bound of 180000, and `#eval` confirmed it). I attribute this to recursion
depth; I did not confirm it directly. `Balanced.lean` proves that the same sum, computed by bisection
at `N = 2^l`, equals `fiberBound`; this reaches N = 2048 with no recursion override. C2's definitions
are unchanged.

## Checks

- `nice -n 5 lake build KAM.Sharp2.Examples.PlasmaLean`: `Build completed successfully (3383 jobs).`
- `#print axioms` on `plasmaLean_torus`, `plasmaLean_classical`, `freqVar_cert`,
  `isDiophantine_omegaStar`, `NumQ.ok_sound`: `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: exit 1 from the known causes only: overlong lines in sibling
  `KAM/Sharp2/{Data,Geometry,ModConstants*}.lean`, `KAM.lean` over 1500 lines, and the ABI scratch
  probe. `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`. No file of this package has a line over
  100 characters; the largest has 385 lines.
- No `set_option` of any kind, no `sorry`, no frozen file touched.

## Deviations from the brief

1. The certificates use `sdConst_of_sdSum` on Ω = {ω\*}, not `sdConst_freq`/`NumA.cert_freq` on the
   ray. C2's fibered bound is a bound of the whole sum, tail included, not of `sdFinite`, so it enters
   one step lower. The fixed-frequency theorem does not need the ray.
2. Prefix length 3 instead of the design's 5, and tuned budgets instead of the design's 5%; both for
   the reasons above.
3. γ = 0.1374 instead of 0.0687. This is the certified value for ω\*.
4. e\* is above the brief's "as close to 10⁻¹⁷·²⁷ as the certified constants allow".

## Uncertainties

- **`plasmaLean_torus` is not a theorem about PlasmaLean's field.** It is about canonical Hamiltonian
  flows satisfying `CALike`. PlasmaLean's field has a non-canonical area form and no closed-form
  canonical chart, and the norm set "cA-like" is the design's guess, not a measurement of any object.
- The comparison 1.93·10⁻¹⁷ against 5.7·10⁻¹⁹ compares different quantities: a sup norm of `E` on a
  2n-dimensional phase space here, a weighted ℓ¹ coefficient norm there.
- Non-vacuity of `CALike` is not formalised. An informal witness with e = 0 is
  `h(θ, I) = ω*·I + (a/2)|I|²`, `a ∈ [0.22, 3]`, `K(θ) = (θ, 0)` on a small neighbourhood.
- The fiber bound loses 8.7% in S at r₀ and 2% at δ₀ against the true sum; the effect on e\* is about
  0.02 orders. A direct sum at r₀ would recover it.

## Suspected errata

None in pinned sources. In-repo note: the kernel failure of `SdsData.fiberBound` above, which is a
limit of the checker's form and not a defect in its statement.
