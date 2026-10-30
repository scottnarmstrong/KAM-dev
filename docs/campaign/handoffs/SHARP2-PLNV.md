# SHARP2-PLNV: non-vacuity of the PlasmaLean theorem

Branch `sharp-plnv`, from `sharp-v2` at 3930f5fe. Opus 5.5. This handoff covers item 1 of the brief.
Item 2 (L8′) waits for B4B and gets its own handoff, `SHARP2-L8P.md`.

## Result

`CALike` is inhabited, so `plasmaLean_torus` is not vacuous. No field of `CALike` is obstructed: every
field was met by a canonical flow, with room to spare (see the table). The theorem also applies at a
strictly positive error, to a torus that is provably not invariant.

```lean
theorem caLike_nonempty : ∃ (𝔅 : Set PS) (h : PS → ℂ) (K : (Fin 2 → ℂ) → PS),
    CALike 𝔅 h K omegaStar

theorem caLike_plH {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1 / 1000) :
    CALike plB (plH ε) plK omegaStar

theorem plasmaLean_torus_integrable : ∃ Kinf, ... (at ε = 0, e = 0)

theorem norm_invarianceError_plH_le {ε : ℝ} (h0 : 0 ≤ ε) {θ} (hθ : θ ∈ complexStrip 2 (1 / 50)) :
    ‖invarianceError (plH ε) plK omegaStar θ‖ ≤ 26 * ε

theorem invarianceError_plH_ne_zero {ε : ℝ} (hε : ε ≠ 0) :
    invarianceError (plH ε) plK omegaStar (fun _ => 1 / 4) ≠ 0

theorem plasmaLean_torus_twoWave {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 7 / 10 ^ 19) :
    ∃ Kinf : (Fin 2 → ℂ) → PS,
      DifferentiableOn ℂ Kinf (complexStrip 2 (1 / 50000)) ∧ IsPrimaryOnStrip Kinf (1 / 50000) ∧
      IsRealOnReals Kinf ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), invarianceError (plH ε) Kinf omegaStar θ = 0) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), Metric.ball (Kinf θ) (1 / 320) ⊆ plB) ∧
      (∀ θ ∈ complexStrip 2 (1 / 50000), ‖fderiv ℂ Kinf θ‖ ≤ 31 / 10 + 1 / 320) ∧
      ∀ θ ∈ complexStrip 2 (1 / 50000), ‖Kinf θ - plK θ‖ ≤ 22226503 * (26 * ε)
```

## The witness

- `plH ε (θ, I) = ω*·I + ½ I·I + ε (cos 2πθ₀ + cos 2π(θ₀ + θ₁))`, so `a = 1` in the brief's notation.
- `plK θ = (θ, 0)`.
- `plB = complexStrip 2 (1/30) ×ˢ Metric.ball 0 (1/10)`.

At ε = 0 this is the brief's example. The term in ε goes beyond what was asked: it gives the e > 0
instance a Hamiltonian that is not in action-angle form, rather than merely a shifted torus. The two
waves have independent phases, so this is the classical two-wave Hamiltonian.

| `CALike` field | required | value on the witness |
|---|---|---|
| `bounds` (`‖Dh‖`, `‖X_h‖`, `‖DX_h‖`, `‖D²X_h‖`) | ≤ 3 | ≤ 2.2 + 39ε, 1.1, 1 + 240ε, 2600ε |
| `deriv_le` | ≤ 3.1 | ≤ 1 |
| `gram` | row sums ≤ 2 | Gram = 1, row sums 1 |
| `twist_le` | row sums ≤ 50/11 | ⟨T⟩ = 1, row sums 1 |
| `torsion_le` | ≤ 19.84 | T = 1 |
| `ball` | radius 1/160 | margin to `plB`: 1/30 − 1/50 − 1/160 |
| invariance error | ≤ 1.93·10⁻¹⁷ | ≤ 26ε, nonzero for ε ≠ 0 |

T = 1 holds for every ε, because the potential does not touch `DX_h` on the normal directions
`(0, e_j)`.

## Files

- `KAM/Sharp2/Examples/PlasmaLean/Witness.lean`: `plH`, `plX`, `plDX`, `plD2X` with their
  `HasFDerivAt` proofs, the sup-norm bounds `plH_bounds`, `norm_cos_le_two`, `norm_sin_le_two`.
- `KAM/Sharp2/Examples/PlasmaLean/NonVacuous.lean`: `plK`, the Gram matrix, normal frame, torsion and
  average, `caLike_plH`, the theorems above.
- `KAM.lean`: regenerated.

## Checks

- `nice -n 5 lake build KAM.Sharp2.Examples.PlasmaLean.NonVacuous`:
  `Build completed successfully (3386 jobs).`
- `#print axioms` (`.drafts` probe) on `caLike_nonempty`, `caLike_plH`,
  `plasmaLean_torus_integrable`, `plasmaLean_torus_twoWave`, `invarianceError_plH_ne_zero`:
  `[propext, Classical.choice, Quot.sound]`.
- `sh scripts/lint_sources.sh`: exit 1 from the known causes only (overlong lines in sibling
  `KAM/Sharp2/{Data,Geometry,ModConstants*}.lean`, `KAM.lean` over 1500 lines, ABI scratch probe). No
  line of `KAM/Sharp2/Examples`. `check_lean_modules: PASS`, `FROZEN-ANCHOR GUARD OK`.
- No warning from either new file, no `set_option`, no `sorry`, no frozen file touched. Both files are
  under 800 lines.

## Uncertainties

- The witness shows the hypotheses can be met. It says nothing about PlasmaLean's field.
- The bound ‖E‖ ≤ 26ε is crude: it uses ‖sin‖ ≤ 2, where cosh(2π·2/50) ≈ 1.03 holds on the strip. The
  largest ε covered, 7·10⁻¹⁹, could be nearly doubled. This does not matter for non-vacuity.
- That the two-wave Hamiltonian is non-integrable is the standard picture, not something proved here.
  What is proved is that `plK` is not invariant for ε ≠ 0 and that a true torus of frequency ω\* lies
  within 22226503·26ε, with ε of order 10⁻¹⁸, so this is purely a small-perturbation statement.
- `plasmaLean_torus_integrable` is a type-level check that the theorem applies; at e = 0 its content
  is trivial.

## Suspected errata

None.
