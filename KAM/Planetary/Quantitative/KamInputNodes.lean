/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Quantitative.Assembly
public import KAM.Planetary.Quantitative.AssemblyK6
public import KAM.Planetary.Quantitative.TheoremNodes

/-! # GAP-P11a-SQ: the Part-11 KAM input (`bpP:p11:kam-input`)

`kam_input` states the quantitative KAM input in the form in which Part 11 uses it
(`N = n + n`, squared convention `ρ = 2`): for a valid datum `𝔡` there are `γ = γ(𝔡) > 0` and
`ε_adm = ε_adm(𝔡) > 0` (the data-only `thresholds`) such that for every `𝔡`-admissible `(h, f)`
(`QuantitativeInput`) with `sup |f| ≤ ε_f ≤ ε_adm` the clauses (K1)–(K4) hold (the fields of
`QuantitativeFamily`, restated in source wording), and, uniformly in the amount `β`, (K5) holds with
`B₀ = μ(μ+1)+2` and (K6) with a displacement power law.  The exponent identity
`p11c_B0 𝔡 = μ(μ+1)+2` is proved for `ρ = 2`, `μ ≥ 1`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

/-- (K5) exponent: for `ρ = 2` and `μ ≥ 1`, `B₀ = μ(μ+1)+2`. -/
theorem kam_input_B0 {N : ℕ} (d : QuantitativeData N) (hd : d.Valid) (hρ : d.rho = 2) :
    p11c_B0 d = (d.mu : ℝ) * (d.mu + 1) + 2 := by
  have hm : (1 : ℝ) ≤ d.mu := by exact_mod_cast hd.1.2.1
  unfold p11c_B0 p11c_G0
  rw [hρ]
  push_cast
  rw [max_eq_right (by nlinarith)]
  ring

/-- `bpP:p11:kam-input`. -/
theorem kam_input {n : ℕ} (d : QuantitativeData (n + n)) (hd : d.Valid) (hρ : d.rho = 2) :
    ∃ γ ε_adm : ℝ, γ = d.gamma ∧ ε_adm = thresholds d ∧ 0 < γ ∧ 0 < ε_adm ∧
    ∃ cDelta : ℝ, 0 < cDelta ∧
    (∀ (h : (Fin (n + n) → ℂ) → ℂ) (f : (Fin (n + n) → ℂ) × (Fin (n + n) → ℂ) → ℂ),
      QuantitativeInput d h f → ∀ ε_f : ℝ, ε_f ≤ ε_adm →
      (∀ z ∈ complexStrip (n + n) d.s ×ˢ actionNbhd d.K (2 * d.vartheta), ‖f z‖ ≤ ε_f) →
      ∃ Q : QuantitativeFamily d (realHamiltonian h f) cDelta ε_f,
        IsCompact Q.good ∧ Q.good ⊆ d.K ∧
        volume d.K ≤ volume Q.good + ENNReal.ofReal d.epsLoss ∧
        volume d.K - ENNReal.ofReal d.epsLoss ≤ volume Q.good ∧
        (∀ b ∈ Q.good, IsLatticeTorus angleShift (realHamiltonian h f)
          (p11c_realDomain d) (Q.freq b) (Q.torus b)) ∧
        (∀ b ∈ Q.good, IsDiophantine γ d.tau (Q.freq b)) ∧
        (∀ b ∈ Q.good, ∀ θ, ‖Q.torus b θ - (θ, b)‖ ≤ p11c_displacement d cDelta ε_f) ∧
        Set.InjOn (fun z : Phase (n + n) => Q.torus z.2 z.1) (unitCube (n + n) ×ˢ Q.good) ∧
        MeasurableSet ((fun z : Phase (n + n) => Q.torus z.2 z.1) '' (unitCube (n + n) ×ˢ Q.good)) ∧
        ENNReal.ofReal ((2 : ℝ) ^ (-(2 * (n + n) : ℤ))) * volume Q.good ≤
          volume ((fun z : Phase (n + n) => Q.torus z.2 z.1) '' (unitCube (n + n) ×ˢ Q.good))) ∧
    p11c_B0 d = (d.mu : ℝ) * (d.mu + 1) + 2 ∧
    (∃ c_star : ℝ, 0 < c_star ∧ ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M),
      c_star * b ^ ((d.mu : ℝ) * (d.mu + 1) + 2) ≤ thresholds { d with beta := b }) ∧
    ∃ (c_D κ_D a_D : ℝ), 0 < c_D ∧ 0 < κ_D ∧ 0 ≤ a_D ∧
      ∀ b ∈ Ioc (0 : ℝ) (min 1 d.M), ∀ ε_f : ℝ, 0 ≤ ε_f → ε_f ≤ thresholds { d with beta := b } →
        p11c_displacement { d with beta := b } cDelta ε_f ≤ c_D * ε_f ^ κ_D * b ^ (-a_D) := by
  have hB0 := kam_input_B0 d hd hρ
  obtain ⟨cDelta, hc, hQ⟩ := weak_kam_quantitative (n + n) d.mu d.tau d.s d.C1
  obtain ⟨cD, hcD, hflat⟩ := displacement_power_flat d hd cDelta hc
  obtain ⟨c, hc0, hbeta⟩ := qb_beta d hd.1
  have hn := qt_order d hd
  have hr : (0 : ℝ) < d.rho := by rw [hρ]; norm_num
  have hG0 : 0 ≤ p11c_G0 d := by unfold p11c_G0; positivity
  obtain ⟨y, hy⟩ : d.K.Nonempty := nonempty_of_measure_ne_zero hn.2.2.1.ne'
  refine ⟨d.gamma, thresholds d, rfl, rfl, hn.1, hn.2.1, cDelta, hc, ?_, hB0,
    ⟨c, hc0, fun b hb => hB0 ▸ hbeta b hb⟩, cD, 1 / 2, p11c_G0 d, hcD, by norm_num, hG0,
    fun b hb eps he _ => hflat b hb eps he⟩
  intro h f hh ε_f hε hf
  have hs : 0 < d.s := hd.1.2.2.2.2.2.2.2.1
  have hε0 : 0 ≤ ε_f := by
    have hmem : (realInclusion (n + n) y, realInclusion (n + n) y) ∈
        complexStrip (n + n) d.s ×ˢ actionNbhd d.K (2 * d.vartheta) :=
      ⟨realInclusion_mem_complexStrip hs _, y, hy, by
        have e : ((realInclusion (n + n) y, realInclusion (n + n) y).2 -
            fun i => (y i : ℂ)) = 0 := by
          funext i; simp [realInclusion]
        rw [e, norm_zero]; linarith [hd.1.2.2.2.2.2.1]⟩
    exact (norm_nonneg _).trans (hf _ hmem)
  obtain ⟨Q⟩ := hQ d hd rfl rfl rfl rfl h f hh ε_f hε0 hε hf
  refine ⟨Q, Q.compact, Q.subset, Q.measure, tsub_le_iff_right.2 Q.measure, Q.lattice, Q.dio,
    Q.displacement, ?_, Q.borel, Q.cell_lower⟩
  rintro ⟨θ, b⟩ ⟨hθ, hb⟩ ⟨θ', b'⟩ ⟨hθ', hb'⟩ heq
  have h1 := Q.lower b hb b' hb' θ θ'
  have heq' : Q.torus b θ = Q.torus b' θ' := heq
  rw [heq', sub_self, norm_zero] at h1
  have hpos : (0 : ℝ) < 1 - (2 : ℝ) ^ (-10 : ℤ) := by norm_num
  have h2 : ‖(θ, b) - (θ', b')‖ ≤ 0 := by
    by_contra hcon
    push Not at hcon
    nlinarith
  have := norm_le_zero_iff.1 h2
  exact sub_eq_zero.1 this

end KAM.Planetary

end
