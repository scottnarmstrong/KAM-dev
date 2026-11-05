/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Measure.Consts

/-!
# W7: resonance zones and admissible frequency families (blueprint `bpW:w7:zones`, `bpW:w7:family`)

`IsFreqPair` is the structure of hypotheses (H1)–(H2) of an admissible family on one parameter
domain `D`; `AdmissibleFamily` is a sequence of such pairs with the common numbers
`ε_ω, ε₁, ε₂, θ` and the thresholds `K_ν ≥ 2^ν`. These are the hypotheses W6 supplies; they are
stated exactly as in the blueprint, not as conclusions.

Maps are total functions that are only constrained on the domain `D_ν`; this is equivalent to
maps on `D_ν`. The normal frequencies `Ω_{ν,j}` are indexed by the normal index `j - 3 : ℕ`, with
the Dirichlet label `normLab`, so the decay `j^{-1}`, `j^{-1/2}` is `normLab⁻¹`, `normLab^{-1/2}`.
-/

@[expose] public noncomputable section

open Real Finsupp

namespace KAM.Wave

variable (m : ℝ) (hm : 0 < m)

/-- The standing data of W7: `Π` Borel in the closed ball of radius `1/2`, `0 < α ≤ α₀`. -/
structure MeasSetup (Pi : Set (Fin 2 → ℝ)) (α : ℝ) : Prop where
  meas : MeasurableSet Pi
  sub : ∀ ξ ∈ Pi, ‖ξ‖ ≤ 1 / 2
  alpha_pos : 0 < α
  alpha_le : α ≤ measAlpha0 m hm

/-- The hypotheses (H1)–(H2) of an admissible family on the domain `D` (blueprint
`bpW:w7:family`): one frequency pair `(ω, Ω)` with the numbers `ε_ω, ε₁, ε₂, θ`. -/
structure IsFreqPair (Pi : Set (Fin 2 → ℝ)) (α : ℝ) (D : Set (Fin 2 → ℝ))
    (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ → ℝ) (εω ε1 ε2 θ : ℝ) : Prop where
  meas : MeasurableSet D
  sub : D ⊆ Pi
  εω_mem : εω ∈ Set.Icc 0 α
  ε1_mem : ε1 ∈ Set.Icc 0 α
  ε2_mem : ε2 ∈ Set.Icc 0 α
  θ_mem : θ ∈ Set.Icc 0 (measTheta0 m hm)
  /-- (H1), sup bound -/
  h1_sup : ∀ ξ ∈ D, ‖ω ξ - omegaTan m hm ξ‖ ≤ εω
  /-- (H1), Lipschitz bound -/
  h1_lip : ∀ ξ ∈ D, ∀ ξ' ∈ D,
    ‖(ω ξ - omegaTan m hm ξ) - (ω ξ' - omegaTan m hm ξ')‖ ≤ θ * ‖ξ - ξ'‖
  /-- (H2), sup bound -/
  h2_sup : ∀ ξ ∈ D, ∀ ν : ℕ,
    |Ω ξ ν - omegaNor m hm ξ ν| ≤ ε1 * (normLab ν)⁻¹ + ε2 * normLab ν ^ (-(1 / 2 : ℝ))
  /-- (H2), Lipschitz bound -/
  h2_lip : ∀ ξ ∈ D, ∀ ξ' ∈ D, ∀ ν : ℕ,
    |(Ω ξ ν - omegaNor m hm ξ ν) - (Ω ξ' ν - omegaNor m hm ξ' ν)| ≤
      θ * normLab ν ^ (-(1 / 2 : ℝ)) * ‖ξ - ξ'‖

/-- An admissible frequency family for `Π` and `α` (blueprint `bpW:w7:family`). -/
structure AdmissibleFamily (Pi : Set (Fin 2 → ℝ)) (α : ℝ) where
  D : ℕ → Set (Fin 2 → ℝ)
  ω : ℕ → (Fin 2 → ℝ) → Fin 2 → ℝ
  Ω : ℕ → (Fin 2 → ℝ) → ℕ → ℝ
  K : ℕ → ℝ
  εω : ℝ
  ε1 : ℝ
  ε2 : ℝ
  θ : ℝ
  pair : ∀ ν, IsFreqPair m hm Pi α (D ν) (ω ν) (Ω ν) εω ε1 ε2 θ
  K_ge : ∀ ν, (2 : ℝ) ^ ν ≤ K ν

/-- `K_{ν-1}` with `K_{-1} = 0`. -/
def AdmissibleFamily.Kprev {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (F : AdmissibleFamily m hm Pi α) :
    ℕ → ℝ
  | 0 => 0
  | n + 1 => F.K n

/-- The resonance zone `R_{kl}(a) = {ξ ∈ D : |⟨k, ω'⟩ + ⟨l, Ω'⟩| < a ⟨l⟩ / A_k}`
(blueprint `bpW:w7:zones` (ii)). -/
def zoneSet (D : Set (Fin 2 → ℝ)) (ω : (Fin 2 → ℝ) → Fin 2 → ℝ) (Ω : (Fin 2 → ℝ) → ℕ → ℝ)
    (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : Set (Fin 2 → ℝ) :=
  {ξ ∈ D | |∑ i, (k i : ℝ) * ω ξ i + linF l (Ω ξ)| < a * japL l / kAk k}

/-- The preparatory zone `S_{kl}` (blueprint `bpW:w7:zones` (i)), at level `a = α̂`. -/
def prepZone (Pi : Set (Fin 2 → ℝ)) (a : ℝ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : Set (Fin 2 → ℝ) :=
  {ξ ∈ Pi | |∑ i, (k i : ℝ) * omegaTan m hm ξ i + linF l (omegaNor m hm ξ)| < a * hatW l / kAk k}

/-- The index set `Z = {(k, l) : l ∈ Λ ∪ {0}, (k, l) ≠ (0, 0)}`. -/
def InZ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) : Prop := (l = 0 ∨ IsLam l) ∧ (k ≠ 0 ∨ l ≠ 0)

/-- `Ξ = ⋃_{(k,l) ∈ Z} S_{kl}` (blueprint `bpW:w7:zones` (i)), at level `α̂ = α^{44/47}`. -/
def prepSet (Pi : Set (Fin 2 → ℝ)) (α : ℝ) : Set (Fin 2 → ℝ) :=
  ⋃ (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l), prepZone m hm Pi (alphaHat α) k l

/-- `ℰ_it = ⋃_ν ⋃_{(k,l) ∈ Z, |k| > K_{ν-1}} R^ν_{kl}`, at level `α̌ = α^{48/47}`. -/
def iterSet {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (F : AdmissibleFamily m hm Pi α) : Set (Fin 2 → ℝ) :=
  ⋃ (ν : ℕ) (k : Fin 2 → ℤ) (l : ℕ →₀ ℤ) (_ : InZ k l ∧ F.Kprev m hm ν < kAbs k),
    zoneSet (F.D ν) (F.ω ν) (F.Ω ν) (alphaCheck α) k l

/-- The excluded set `ℰ = Ξ ∪ ℰ_it` (blueprint `bpW:w7:family`). -/
def exclSet {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (F : AdmissibleFamily m hm Pi α) : Set (Fin 2 → ℝ) :=
  prepSet m hm Pi α ∪ iterSet m hm F

/-- The unperturbed frequency pair `(ω⁰, Ω⁰)` on `Π`, with all `ε`'s and `θ` equal to `0`. -/
theorem isFreqPair_unpert {Pi : Set (Fin 2 → ℝ)} {α : ℝ} (hPi : MeasurableSet Pi) (hα : 0 ≤ α) :
    IsFreqPair m hm Pi α Pi (omegaTan m hm) (omegaNor m hm) 0 0 0 0 where
  meas := hPi
  sub := subset_rfl
  εω_mem := ⟨le_rfl, hα⟩
  ε1_mem := ⟨le_rfl, hα⟩
  ε2_mem := ⟨le_rfl, hα⟩
  θ_mem := ⟨le_rfl, by
    unfold measTheta0
    have := measSigmaX_pos m hm
    have := measLA_pos m hm
    have : 0 < measKstar m hm + 2 := by linarith [measKstar_pos m hm]
    apply mul_nonneg (inv_nonneg.2 (measLA_pos m hm).le)
    exact le_min (by norm_num) (by positivity)⟩
  h1_sup := fun ξ _ => by simp
  h1_lip := fun ξ _ ξ' _ => by simp
  h2_sup := fun ξ _ ν => by simp
  h2_lip := fun ξ _ ξ' _ ν => by simp

end KAM.Wave

end
