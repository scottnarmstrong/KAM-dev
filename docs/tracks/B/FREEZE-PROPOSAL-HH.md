# Track B: freeze proposal HH (D73), exact text of `henonHeiles_confinement`

Owner approval (D73, 2026-11-03, relayed by root-b8): the `henonHeiles_confinement` text exactly as in
`brief-B3-CERT.md` step 4 (sent to the owner 10:0x UTC). Namespace `KAM.EffectiveStability` (the approved text fixes
no namespace; root-b8 confirmed). The docstring below is commentary added at freeze time; the statement from
`theorem` to the final `12 / 10 ^ 10` is byte-identical to the approved text.

Anchor `KAM/Frozen/EffectiveStability/HenonHeilesConfinement.lean` (application library `KAMHenonHeiles`, as the SO
`lunar_spin_confinement` precedent D49/D50), provider `KAM/Provider/EffectiveStability/HenonHeilesConfinement.lean`,
implementation `KAM.EffectiveStability.HenonHeiles.henonHeiles_confinement_proof` (B3-CERT).

## Exact text

```lean
/-- **Hénon–Heiles confinement** (track B, plan §4 "A first instance with literal acceptance
criteria"; CL20 Appendix B model `H = I₁ - (√2/2) I₂ + q₁² q₂ - q₂³/3`, `q = z.1`, `p = z.2`):
every initial point with both oscillator actions `≤ (1/12500)²` has a Hamiltonian solution on
`(-T₁, T₁)` with `T₁ > 10¹⁰`, unique among solutions on intervals through `0`, whose actions stay
`< 101/10¹⁰` and within `12/10¹⁰` of their initial values for `|t| ≤ 10¹⁰`. -/
theorem henonHeiles_confinement (z₀ : (Fin 2 → ℝ) × (Fin 2 → ℝ))
    (hz₀ : ∀ j, KAM.Planetary.oscillatorAction z₀.2 z₀.1 j ≤ (1 / 12500) ^ 2) :
    ∃ T₁ : ℝ, 10 ^ 10 < T₁ ∧ ∃ z : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ), z 0 = z₀ ∧
      (∀ t ∈ Set.Ioo (-T₁) T₁, HasDerivAt z (KAM.hamiltonianVectorField
        (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
          (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
            + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (z t)) t) ∧
      (∀ (I : Set ℝ) (y : ℝ → (Fin 2 → ℝ) × (Fin 2 → ℝ)), I.OrdConnected → (0 : ℝ) ∈ I → y 0 = z₀ →
        (∀ t ∈ I, HasDerivAt y (KAM.hamiltonianVectorField
          (fun w : (Fin 2 → ℝ) × (Fin 2 → ℝ) =>
            (w.1 0 ^ 2 + w.2 0 ^ 2) / 2 - Real.sqrt 2 / 2 * ((w.1 1 ^ 2 + w.2 1 ^ 2) / 2)
              + w.1 0 ^ 2 * w.1 1 - w.1 1 ^ 3 / 3) (y t)) t) →
        ∀ t ∈ I, t ∈ Set.Ioo (-T₁) T₁ → y t = z t) ∧
      ∀ t : ℝ, |t| ≤ 10 ^ 10 → ∀ j,
        KAM.Planetary.oscillatorAction (z t).2 (z t).1 j < 101 / 10 ^ 10 ∧
        |KAM.Planetary.oscillatorAction (z t).2 (z t).1 j -
            KAM.Planetary.oscillatorAction z₀.2 z₀.1 j| ≤ 12 / 10 ^ 10
```

## Provenance of the literals
Plan §4 (model, box `(1/12500)²`, time `10¹⁰`, bounds `101/10¹⁰`, `12/10¹⁰`); certificate E1 report
`docs/tracks/B/b3/out/E1-report.md` (GO); physical box through `oscillatorChain_physical_disc` (OD-B18).
