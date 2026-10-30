/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.Local
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The scheme of route B

The engine `StageScheme.converge_ratio` (SHARP2-B5R) asks (N1), (N2) for **every** strip `r` and
bite `δ ≤ δ₀`, with constants `C δ` depending on the bite only. The data of route B are
stage-indexed: the stage-0 weight `λ₀` and the frozen bound of `E` serve stage `0` only, and the
average certificate at the full bite `min (r_s) 1` needs the strip `r_s` of the stage. The scheme
therefore carries the stage and a validity flag in its state, `(s, b, K)`:

* `schemeB`: the step from `(s, true, K)` at the matched pair `(r_s, δ_s)` is the modified step
  `modNewton` (SHARP2-B4B); every other pair leaves the torus unchanged and clears the flag;
* `Good`: admissibility of a flagged state: the strip is `r_s`, the weighted error is at most
  `μ̄_s = γ δ_s^{τ+1} X_s` (`X_s = N.xS X_i s`), the frames are bounded by the cap values, the
  drift of the frame part of the torsion against the initial torus is at most the `Tab` cap value,
  and at stage `0` the frozen bound of `E` (option `stage0`); `Junk`: regularity only;
* `stageC`: the engine's constants of a bite, `N.stage s` at `δ_s` (`s < kp`) and the tail record
  elsewhere (`stageC_sched`, `stageC_tail`).

Since the flag survives exactly along the run (`iter_eq`), the engine's admissibility of the
iterates is `Good`, which records their stage, strip and weighted error.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology MeasureTheory

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2 KAM.Sharp2.ModStepB

variable {n : ℕ}

/-- The states of route B: stage, validity flag, torus. -/
abbrev StB (n : ℕ) := ℕ × Bool × ((Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ))

/-- Admissibility of a flagged state at stage `s` (`bp:p2s2:g1`, route B: the state of the scheme
is the torus with the reference data). -/
structure Good (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) (s : ℕ) (r β μ : ℝ) (m : Fin 7 → ℝ)
    (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop where
  r_eq : r = N.r s
  μ_nonneg : 0 ≤ μ
  μ_le : μ ≤ γ * N.δ s ^ (N.τ + 1) * N.xS Xi s
  holo : DifferentiableOn ℂ K (complexStrip n r)
  primary : IsPrimaryOnStrip K r
  real : IsRealOnReals K
  ball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅
  β_pos : 0 < β
  L : ∀ θ ∈ complexStrip n r, ‖tangentMat K θ‖ ≤ m 0
  Lt : ∀ θ ∈ complexStrip n r, ‖(tangentMat K θ)ᵀ‖ ≤ m 1
  G : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ m 2
  Nm : ∀ θ ∈ complexStrip n r, ‖normalMat K θ‖ ≤ m 3
  NmT : ∀ θ ∈ complexStrip n r, ‖(normalMat K θ)ᵀ‖ ≤ m 4
  drift : ‖torsionABAverage h K - torsionABAverage h K0‖ ≤ m 5
  ηL : ∀ θ ∈ complexStrip n r, ‖etaL h K ω θ‖ ≤ (N.inp s).lam * μ
  ηN : ∀ θ ∈ complexStrip n r, ‖etaN h K ω θ‖ ≤ γ * N.δ s ^ N.τ * μ
  E0 : s = 0 → ∀ θ ∈ complexStrip n r, ‖invarianceError h K ω θ‖ ≤ N.ePer0 * μ

/-- Admissibility of an unflagged state: regularity only. -/
def Junk (r μ : ℝ) (K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : Prop :=
  0 ≤ μ ∧ DifferentiableOn ℂ K (complexStrip n r) ∧ IsPrimaryOnStrip K r ∧ IsRealOnReals K

open Classical in
/-- The scheme of route B. -/
def schemeB (N : NumB n) (𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ)))
    (h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ) (ω : Fin n → ℝ) (γ Xi : ℝ)
    (K0 : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)) : StageScheme n 7 (StB n) where
  tor := fun x => x.2.2
  par := fun _ => 0
  Adm := fun r β μ m x => if x.2.1 then Good N 𝔅 h ω γ Xi K0 x.1 r β μ m x.2.2 else Junk r μ x.2.2
  step := fun r δ x => if x.2.1 = true ∧ r = N.r x.1 ∧ δ = N.δ x.1 then
      (x.1 + 1, true, modNewton h x.2.2 ω (r - 2 * δ)) else (x.1 + 1, false, x.2.2)

open Classical in
/-- The stage of a bite: `s` at `δ_s` (`s < kp`), `kp` otherwise. -/
def stageOf (N : NumB n) (δ : ℝ) : ℕ :=
  if hd : ∃ t, t < N.kp ∧ δ = N.δ t then Nat.find hd else N.kp

/-- The engine's constants of a bite. -/
def stageC (N : NumB n) (δ : ℝ) : StageConsts 7 := N.stage (stageOf N δ)

variable {N : NumB n}

theorem stageOf_sched (hN : N.Wf) (s : ℕ) : stageOf N (N.δ s) = min s N.kp := by
  classical
  unfold stageOf
  by_cases hs : s < N.kp
  · have hd : ∃ t, t < N.kp ∧ N.δ s = N.δ t := ⟨s, hs, rfl⟩
    rw [dite_eq_left_of_eq_true (eq_true hd), min_eq_left hs.le]
    have h1 := Nat.find_spec hd
    exact (hN.δ_inj h1.2).symm
  · have hd : ¬ ∃ t, t < N.kp ∧ N.δ s = N.δ t := by
      rintro ⟨t, ht, he⟩
      have := hN.δ_inj he
      omega
    rw [dite_eq_right_of_eq_false (eq_false hd), min_eq_right (not_lt.1 hs)]

theorem stage_min (hN : N.Wf) (s : ℕ) : N.stage (min s N.kp) = N.stage s := by
  by_cases hs : s < N.kp
  · rw [min_eq_left hs.le]
  · have hs' := not_lt.1 hs
    rw [min_eq_right hs']
    simp only [NumB.stage, NumB.Qs, NumB.rate, NumB.wt, hN.inp_tail hs', min_self,
      min_eq_right hs']

/-- `C (δ_s) = N.stage s`. -/
theorem stageC_sched (hN : N.Wf) (s : ℕ) : stageC N (N.δ s) = N.stage s := by
  rw [stageC, stageOf_sched hN, stage_min hN]

/-- Every bite `≤ δ_kp` has the tail constants. -/
theorem stageC_tail (hN : N.Wf) {δ : ℝ} (hδ : δ ≤ N.δ N.kp) : stageC N δ = N.stage N.kp := by
  classical
  unfold stageC stageOf
  have hd : ¬ ∃ t, t < N.kp ∧ δ = N.δ t := by
    rintro ⟨t, ht, rfl⟩
    exact absurd hδ (not_le.2 (hN.δ_strict ht))
  rw [dite_eq_right_of_eq_false (eq_false hd)]

theorem inp_stageOf_ok (hN : N.Wf) (δ : ℝ) : (N.inp (stageOf N δ)).Ok := hN.inp_ok _

/-- (J0): the constants are nonnegative at every bite. -/
theorem stageC_nonneg (hN : N.Wf) (δ : ℝ) :
    0 ≤ (stageC N δ).Q ∧ 0 ≤ (stageC N δ).CDK ∧ 0 ≤ (stageC N δ).Cp ∧
      ∀ i, 0 ≤ (stageC N δ).rate i * (stageC N δ).wt i := by
  have hok := inp_stageOf_ok hN δ
  obtain ⟨hQ, hDK, hBb, hNb, hNbT, hab, -, hnu⟩ := stepConstsB_nonneg hok
  refine ⟨hQ, hDK, hnu, fun i => ?_⟩
  have hw : 0 ≤ N.γb * N.δ (min (stageOf N δ) N.kp) ^ (N.τ + 1) :=
    mul_nonneg hN.γb.le (Real.rpow_nonneg (hN.δ_pos _).le _)
  fin_cases i <;> simp [stageC, NumB.stage, NumB.rate, NumB.wt] <;> positivity

/-- Junk is preserved by the engine's updates. -/
theorem junk_mono {r r' μ' : ℝ} {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} (hr : r' ≤ r)
    (hμ' : 0 ≤ μ') (h : DifferentiableOn ℂ K (complexStrip n r) ∧ IsPrimaryOnStrip K r ∧
      IsRealOnReals K) : Junk r' μ' K := by
  refine ⟨hμ', h.1.mono (Triangular.strip_mono hr), fun θ hθ k => h.2.1 θ ?_ k, h.2.2⟩
  exact Triangular.strip_mono hr hθ

/-! ### Averages of the torsion and of its frame part -/

/-- The frame part `𝒯_ab = B Lᵀ (A Ω₀ - Ω₀ A) L B` is holomorphic where the frames are. -/
theorem diffOn_torsionAB {τ M σK σB σT γ₀ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ₀)
    {r β : ℝ} (hr : 0 < r) (hβ : 0 < β) {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hK : DifferentiableOn ℂ K (complexStrip n r))
    (hball : ∀ θ ∈ complexStrip n r, Metric.ball (K θ) β ⊆ 𝔅)
    (hdK : ∀ θ ∈ complexStrip n r, ‖fderiv ℂ K θ‖ ≤ σK)
    (hG : ∀ θ ∈ complexStrip n r, IsUnit (gramMatrix K θ).det ∧ ‖(gramMatrix K θ)⁻¹‖ ≤ σB) :
    DifferentiableOn ℂ (torsionAB h K) (complexStrip n r) := by
  obtain ⟨⟨hLd, -, -, hAd, -, hBd, -⟩, -⟩ := frame_basic hS hr hβ hK hball hdK hG
  have e : torsionAB h K = fun θ => (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ *
      (linMat h K θ * omegaZeroMatrix n - omegaZeroMatrix n * linMat h K θ) * tangentMat K θ *
        (gramMatrix K θ)⁻¹ := rfl
  rw [e]
  exact ((((hBd.matrix_mul hLd.matrix_transpose).matrix_mul
    ((hAd.matrix_mul (differentiableOn_const _)).sub
      ((differentiableOn_const _).matrix_mul hAd))).matrix_mul hLd).matrix_mul hBd)

/-- An entrywise cube integral is the matrix-valued average. -/
theorem cubeAvg_eq {p q : ℕ} {F : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ} (hF : Continuous F) :
    (Matrix.of fun i j =>
      ∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1), F x i j) = torusAverage F := by
  ext i j
  exact (torusAverage_matrix_apply hF i j).symm

/-- `|⟨F⟩ - ⟨G⟩| ≤ D` for continuous `F`, `G` with `|F - G| ≤ D` on the real torus. -/
theorem norm_torusAverage_sub_le {p q : ℕ} {F G : (Fin n → ℝ) → Matrix (Fin p) (Fin q) ℂ}
    {D : ℝ} (hF : Continuous F) (hG : Continuous G) (hD : ∀ x, ‖F x - G x‖ ≤ D) :
    ‖torusAverage F - torusAverage G‖ ≤ D := by
  have e : torusAverage F - torusAverage G = torusAverage (fun x => F x - G x) := by
    unfold torusAverage
    rw [integral_sub (integrableOn_unitCube_of_continuous hF)
      (integrableOn_unitCube_of_continuous hG)]
  rw [e]
  exact norm_torusAverage_le fun x _ => hD x

/-- `⟨𝒯_ab⟩` is the matrix-valued average. -/
theorem torsionABAverage_eq {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)}
    (hc : Continuous fun x : Fin n → ℝ => torsionAB h K (fun i => (x i : ℂ))) :
    torsionABAverage h K = torusAverage (fun x : Fin n → ℝ => torsionAB h K (fun i => (x i : ℂ))) :=
  cubeAvg_eq hc

/-- `⟨T⟩` is the matrix-valued average. -/
theorem torsionAverage_eq' {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
    {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ}
    (hc : Continuous fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))) :
    torsionAverage h K ω =
      torusAverage (fun x : Fin n → ℝ => torsion h K ω (fun i => (x i : ℂ))) :=
  cubeAvg_eq hc

end KAM.Sharp2.RouteB

end
