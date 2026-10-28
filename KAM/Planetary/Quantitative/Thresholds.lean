/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.MaximalStep.Constants

/-!
# Quantitative weak KAM: data, validity, explicit constants and thresholds (P11C-Q1)

The numerical projection `QuantitativeData` of `bpP:p11a:sec-q-thm#data`, its validity predicates,
the explicit cutoff constant, the Fourier-cutoff constant `cN`, `gamma`, `tbar`, `tflat`, `xibar`,
`lambdaFlat` and the data-only `thresholds`, together with `p11c_oldThreshold` (comparison only).
`QuantitativeData.cN_eq_p11C` identifies `cN` with the upstream constant `p11C` of
`fourier_cutoff`.
-/

@[expose] public noncomputable section
open Set Metric Real MeasureTheory Function
open scoped ContDiff Topology
namespace KAM.Planetary
open KAM KAM.Kepler KAM.ODE

/- Quantitative/Thresholds: local numerical projection of sec-q-thm#data.
The cutoff constant below is its explicit source formula, not an arbitrary positive input. -/
structure QuantitativeData (N : ℕ) where
  mu : ℕ
  rho : ℕ
  tau : ℝ
  vartheta : ℝ
  s : ℝ
  beta : ℝ
  M : ℝ
  M0 : ℝ
  C1 : ℝ
  epsLoss : ℝ
  K : Set (Fin N → ℝ)

def QuantitativeData.NumericalValid {N : ℕ} (d : QuantitativeData N) : Prop :=
  1 ≤ N ∧ 1 ≤ d.mu ∧ (d.rho = 1 ∨ d.rho = 2) ∧
  (N : ℝ) * d.mu / d.rho - 1 < d.tau ∧ 0 ≤ d.tau ∧
  0 < d.vartheta ∧ d.vartheta ≤ 1 ∧ 0 < d.s ∧ d.s ≤ 1 ∧
  1 ≤ d.C1 ∧ 0 < d.M0 ∧ 0 < d.beta ∧ d.beta ≤ d.M ∧
  IsCompact d.K ∧ 0 < d.epsLoss ∧ ENNReal.ofReal d.epsLoss < volume d.K

def QuantitativeData.Valid {N : ℕ} (d : QuantitativeData N) : Prop :=
  d.NumericalValid ∧ (N : ℝ) - 1 < d.tau ∧ d.beta ≤ 1

def p11c_bump (mu : ℕ) (x : ℝ) : ℝ := (max 0 (1 - x ^ 2)) ^ (mu + 1)
def p11c_mollifier (mu : ℕ) (x : ℝ) : ℝ :=
  p11c_bump mu x / ∫ y : ℝ, p11c_bump mu y

def p11c_mollifierMass (mu j : ℕ) : ℝ := ∫ x : ℝ, |iteratedDeriv j (p11c_mollifier mu) x|
def p11c_cutoffDerivative (N mu k : ℕ) : ℝ :=
  (N : ℝ) ^ k * sSup {v : ℝ | ∃ a : Fin N → ℕ,
    (∑ i, a i) = k ∧ v = ∏ i, p11c_mollifierMass mu (a i)}
def p11c_cutoffConstant (N mu : ℕ) : ℝ :=
  sqrt N * sSup {v : ℝ | ∃ k ≤ mu, v = (4 : ℝ) ^ k *
    ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * p11c_cutoffDerivative N mu j *
      ((k - j : ℕ) : ℝ) ^ (k - j)}

def QuantitativeData.diameter {N : ℕ} (d : QuantitativeData N) : ℝ := Metric.diam d.K
def QuantitativeData.varpi {N : ℕ} (d : QuantitativeData N) : ℝ :=
  (2 : ℝ) ^ (-(2 * (2 * (d.tau + 1) * (d.mu + 1) + N + 4)))
def QuantitativeData.cN (N : ℕ) : ℝ :=
  2 * (1 + 1 / π) * (3 * N / (exp 1 * π)) ^ (N - 1)
def QuantitativeData.A0 {N : ℕ} (d : QuantitativeData N) : ℝ := log (16 * cN N / d.varpi)
def QuantitativeData.cDio {N : ℕ} (d : QuantitativeData N) : ℝ :=
  2 ^ (N + 2) * d.mu * (sqrt N * d.diameter) ^ (N - 1) * (d.M / d.beta) *
    (1 + (4 + 1 / d.vartheta) * sqrt N * d.diameter) * d.beta ^ (-(1 / (d.mu : ℝ))) *
    (N : ℝ) ^ ((d.rho : ℝ) / (2 * d.mu)) * 2 * 3 ^ (N - 1) *
      (1 + 1 / ((d.rho : ℝ) * (d.tau + 1) / d.mu - N))
def QuantitativeData.gamma {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min ((1 / 2 : ℝ) * (N : ℝ) ^ (-(1 / 2 : ℝ)) * (d.beta / 4) ^ (1 / (d.rho : ℝ)))
    ((d.epsLoss / d.cDio) ^ ((d.mu : ℝ) / d.rho)) / 2

def QuantitativeData.tbar {N : ℕ} (d : QuantitativeData N) : ℝ :=
  1 + 16 / (π * d.s) * (|d.A0| + N * log (32 * N / d.s))
def QuantitativeData.tflat {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (d.vartheta / sqrt N) (d.gamma * d.tbar ^ (-d.tau - 1) / (4 * d.C1))
def QuantitativeData.xibar {N : ℕ} (d : QuantitativeData N) : ℝ :=
  (2 : ℝ) ^ (d.tau + 1) * (1 + 1 / (d.s / 24) + 1 / d.tflat + d.tbar * (d.s / 24))
def QuantitativeData.thetaMax {N : ℕ} (d : QuantitativeData N) : ℝ :=
  if d.rho = 1 then d.beta / 2 else min d.beta (d.beta / (2 ^ (d.mu + 1) * (2 * d.M0 + d.beta)))
def QuantitativeData.lambdaFlat {N : ℕ} (d : QuantitativeData N) : ℝ :=
  min (min (d.tflat / 8)
    (min (d.varpi / 2) ((2 : ℝ) ^ (-10 : ℤ) / d.xibar) *
      (π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * d.tbar ^ d.tau))))
    (d.thetaMax * d.tflat ^ d.mu / (4 * p11c_cutoffConstant N d.mu))
def thresholds {N : ℕ} (d : QuantitativeData N) : ℝ := d.lambdaFlat ^ 2 / (2 * N * d.C1)

/-- Old threshold's numerical projection, for comparison only (adm_params reconciliation). -/
def p11c_oldThreshold {N : ℕ} (d : QuantitativeData N) : ℝ :=
  let T := max 1 (16 / (π * d.s) * (d.A0 + N * log (32 * N / d.s)))
  let t := min (d.vartheta / sqrt N) (d.gamma * T ^ (-d.tau - 1) / (4 * d.C1))
  let X := (2 : ℝ) ^ (d.tau + 1) * (1 + t / (d.s / 24) + (d.s / 24) / t + T * (d.s / 24))
  let l := min (min (d.C1 * t / 8) (min (d.varpi / 2) ((2 : ℝ) ^ (-10 : ℤ) / X) *
    (π * d.gamma * (d.s / 24) ^ (N + 1) / (18 * N * (4 * N + 5) * 2 ^ N * T ^ d.tau))))
    (d.thetaMax * t ^ d.mu / (4 * p11c_cutoffConstant N d.mu))
  l ^ 2 / (2 * N * d.C1)

/-- `cN` is the upstream Fourier-cutoff constant `p11C` (`fourier_cutoff`), by definition. -/
theorem QuantitativeData.cN_eq_p11C (N : ℕ) : QuantitativeData.cN N = p11C N := rfl

end KAM.Planetary
