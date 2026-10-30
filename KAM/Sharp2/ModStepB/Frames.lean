/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.ModStepB.Comp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# The frames of the new torus and the frame part of the torsion (step `step:p2s2:st-fr`)

On `T_{r-3δ}`, with `X = μ/(γ δ^{κ+1})`:

* `Lb_sub_le`: `|L̄ - L| ≤ n C_ΔK X`, `|(L̄ - L)ᵀ| ≤ 2n C_ΔK X` (Cauchy on `K̄ - K` from
  `T_{r-2δ}`);
* `Gb`: `det Ḡ ≠ 0` and `|B̄ - B| ≤ C_B̄ X` (`Ḡ - G = L̄ᵀ (L̄ - L) + (L̄ - L)ᵀ L`, Neumann with
  ratio `ϑ`);
* `Nb_sub_le`: `|N̄ - N| ≤ C_N̄ X`, `|N̄ᵀ - Nᵀ| ≤ C_N̄ᵀ X` (`N = Ω₀ L B`, `Nᵀ Ω₀ = B Lᵀ`);
* `torsionAB_sub_le`: `|𝒯_ab(K̄) - 𝒯_ab(K)| ≤ C_ab X` (`𝒯_ab = (B Lᵀ)(A Ω₀ - Ω₀ A)(L B)`
  telescoped, `|Δ(A Ω₀ - Ω₀ A)| ≤ c_DTh |K̄ - K|` on the segment `[K, K̄] ⊆ 𝔹_β(K) ⊆ 𝔅`).

The barred factors are bounded by the caps, which admit the increments (`Hyp.room`).
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2

open KAM KAM.Torus KAM.Apost KAM.Sharp

variable {n : ℕ}

namespace ModStepB

/-- The three-factor telescoping. -/
theorem triple_sub_le' {a b c e : Type*} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
    (X X' : Matrix a b ℂ) (Y Y' : Matrix b c ℂ) (Z Z' : Matrix c e ℂ) :
    ‖X' * Y' * Z' - X * Y * Z‖ ≤
      ‖X' - X‖ * ‖Y'‖ * ‖Z'‖ + ‖X‖ * ‖Y' - Y‖ * ‖Z'‖ + ‖X‖ * ‖Y‖ * ‖Z' - Z‖ := by
  have hid : X' * Y' * Z' - X * Y * Z =
      (X' - X) * Y' * Z' + X * (Y' - Y) * Z' + X * Y * (Z' - Z) := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc]
    abel
  have n3 : ∀ {a b c e : Type _} [Fintype a] [Fintype b] [Fintype c] [Fintype e]
      (P : Matrix a b ℂ) (Q : Matrix b c ℂ) (R : Matrix c e ℂ), ‖P * Q * R‖ ≤ ‖P‖ * ‖Q‖ * ‖R‖ :=
    fun P Q R => (Matrix.linfty_opNorm_mul _ _).trans
      (mul_le_mul_of_nonneg_right (Matrix.linfty_opNorm_mul _ _) (norm_nonneg _))
  rw [hid]
  exact (norm_add_le _ _).trans (add_le_add ((norm_add_le _ _).trans
    (add_le_add (n3 _ _ _) (n3 _ _ _))) (n3 _ _ _))

namespace Hyp

variable {p : StepInB} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))} {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ}
  {K : (Fin n → ℂ) → (Fin n → ℂ) × (Fin n → ℂ)} {ω : Fin n → ℝ} {Ω : Set (Fin n → ℝ)}
  {γ β εL εN δ r s c' b cb : ℝ} {m : Fin 5 → ℝ}
  (H : Hyp p 𝔅 h K ω Ω γ β εL εN δ r s c' b cb m)
  {τ M γ₀ : ℝ} (hS : Standing n τ M p.sK p.sB p.sT 𝔅 h ω γ₀)
include H hS

omit hS in
theorem sub32 : complexStrip n (r - 3 * δ) ⊆ complexStrip n (r - 2 * δ) :=
  strip_sub (by linarith [H.δ_pos])

omit hS in
theorem sub3 : complexStrip n (r - 3 * δ) ⊆ complexStrip n r :=
  strip_sub (by linarith [H.δ_pos])

theorem Kb_diffAt : ∀ θ ∈ complexStrip n (r - 2 * δ),
    DifferentiableAt ℂ (modNewton h K ω (r - 2 * δ)) θ := fun _ hθ =>
  (H.Kb_holo hS).differentiableAt ((isOpen_complexStrip n (r - 2 * δ)).mem_nhds hθ)

/-- `|L̄ - L| ≤ n C_ΔK X`, `|(L̄ - L)ᵀ| ≤ 2n C_ΔK X` on `T_{r-3δ}`. -/
theorem Lb_sub_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖tangentMat (modNewton h K ω (r - 2 * δ)) θ - tangentMat K θ‖ ≤
        n * (sCDK p * xX p γ εL εN δ) ∧
      ‖(tangentMat (modNewton h K ω (r - 2 * δ)) θ - tangentMat K θ)ᵀ‖ ≤
        2 * n * (sCDK p * xX p γ εL εN δ) := fun θ hθ => by
  have hd : DifferentiableOn ℂ (fun y => sumVec n (modNewton h K ω (r - 2 * δ) y - K y))
      (complexStrip n (r - 2 * δ)) :=
    (sumVecIso n).differentiable.comp_differentiableOn
      ((H.Kb_holo hS).sub (H.holo.mono (strip_sub (by linarith [H.δ_pos]))))
  have hb : ∀ y ∈ complexStrip n (r - 2 * δ),
      ‖sumVec n (modNewton h K ω (r - 2 * δ) y - K y)‖ ≤
        sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ)) := fun y hy => by
    rw [norm_sumVec]; exact H.Kb_sub_le hS y hy
  have hθ' : θ ∈ complexStrip n (r - 2 * δ - δ) := by
    rw [show r - 2 * δ - δ = r - 3 * δ by ring]; exact hθ
  have hc := (cauchy_strip hd hb H.δ_pos).1
  have he : δ⁻¹ * (sCDK p * (mu p γ εL εN δ / (γ * δ ^ p.κ))) = sCDK p * xX p γ εL εN δ := by
    rw [H.mu_div_gd]; field_simp [H.δ_pos.ne']
  exact tangentMat_sub_le (H.Kb_diffAt hS θ (H.sub32 hθ)) (H.K_diffAt θ (H.sub3 hθ))
    (mul_nonneg (nn_sCDK H.ok) H.X_nonneg) fun j => (hc j θ hθ').trans (le_of_eq he)

theorem Lb_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖tangentMat (modNewton h K ω (r - 2 * δ)) θ‖ ≤ p.sK ∧
      ‖(tangentMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ‖ ≤ p.sLt := fun θ hθ => by
  obtain ⟨h1, h2⟩ := H.Lb_sub_le hS θ hθ
  have hθr := H.sub3 hθ
  obtain ⟨r0, r1, -⟩ := H.room
  rw [← H.pn_real] at h1 h2
  constructor
  · calc _ = ‖tangentMat K θ + (tangentMat (modNewton h K ω (r - 2 * δ)) θ - tangentMat K θ)‖ :=
          by rw [add_sub_cancel]
      _ ≤ m 0 + p.n * (sCDK p * xX p γ εL εN δ) := (norm_add_le _ _).trans
          (add_le_add (H.L θ hθr) h1)
      _ ≤ p.sK := by
          have : (p.n : ℝ) * (sCDK p * xX p γ εL εN δ) =
              p.n * (stepConstsB p).CDK * xX p γ εL εN δ := by
            rw [show (stepConstsB p).CDK = sCDK p from rfl]; ring
          linarith
  · calc _ = ‖(tangentMat K θ)ᵀ +
          (tangentMat (modNewton h K ω (r - 2 * δ)) θ - tangentMat K θ)ᵀ‖ := by
          rw [← Matrix.transpose_add, add_sub_cancel]
      _ ≤ m 1 + 2 * p.n * (sCDK p * xX p γ εL εN δ) := (norm_add_le _ _).trans
          (add_le_add (H.Lt θ hθr) h2)
      _ ≤ p.sLt := by
          have : 2 * (p.n : ℝ) * (sCDK p * xX p γ εL εN δ) =
              2 * p.n * (stepConstsB p).CDK * xX p γ εL εN δ := by
            rw [show (stepConstsB p).CDK = sCDK p from rfl]; ring
          linarith

/-- `det Ḡ ≠ 0` and `|B̄ - B| ≤ C_B̄ X`, `|B̄| ≤ σ_B` on `T_{r-3δ}`. -/
theorem Gb : ∀ θ ∈ complexStrip n (r - 3 * δ),
    IsUnit (gramMatrix (modNewton h K ω (r - 2 * δ)) θ).det ∧
      ‖(gramMatrix (modNewton h K ω (r - 2 * δ)) θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤
        sCBb p * xX p γ εL εN δ ∧
      ‖(gramMatrix (modNewton h K ω (r - 2 * δ)) θ)⁻¹‖ ≤ p.sB := fun θ hθ => by
  have hθr := H.sub3 hθ
  set Kb := modNewton h K ω (r - 2 * δ)
  obtain ⟨h1, h2⟩ := H.Lb_sub_le hS θ hθ
  obtain ⟨-, hLbt⟩ := H.Lb_le hS θ hθ
  have hX := H.X_nonneg
  have hD : ‖gramMatrix Kb θ - gramMatrix K θ‖ ≤ sCG p * sCDK p * xX p γ εL εN δ := by
    rw [gramMatrix_eq_tangentMat_transpose_mul, gramMatrix_eq_tangentMat_transpose_mul]
    refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [← Matrix.transpose_sub]
    calc _ ≤ p.sLt * (n * (sCDK p * xX p γ εL εN δ)) +
          2 * n * (sCDK p * xX p γ εL εN δ) * p.sK :=
          add_le_add (mul_le_mul hLbt h1 (norm_nonneg _) H.ok.caps.2.1.le)
            (mul_le_mul h2 (H.L' θ hθr) (norm_nonneg _)
              (by have := nn_sCDK H.ok; positivity))
      _ = sCG p * sCDK p * xX p γ εL εN δ := by rw [sCG, H.pn_real]; ring
  have hB := H.B' θ hθr
  have hθ1 := H.ok.ratios.2.1
  have hsmall : ‖(gramMatrix K θ)⁻¹‖ * ‖gramMatrix Kb θ - gramMatrix K θ‖ ≤ p.θ :=
    (mul_le_mul hB hD (norm_nonneg _) H.ok.caps.2.2.1.le).trans (by
      have := H.c_G
      calc p.sB * (sCG p * sCDK p * xX p γ εL εN δ) =
          p.sB * sCG p * sCDK p * xX p γ εL εN δ := by ring
        _ ≤ p.θ := this)
  obtain ⟨hu, -, hd⟩ := neumann_ratio ((Matrix.isUnit_iff_isUnit_det _).2 (H.gram θ hθr)) hθ1
    hsmall
  rw [add_sub_cancel] at hu hd
  have hBb : ‖(gramMatrix Kb θ)⁻¹ - (gramMatrix K θ)⁻¹‖ ≤ sCBb p * xX p γ εL εN δ := by
    refine hd.trans ?_
    rw [sCBb]
    have h1t : 0 < 1 - p.θ := by linarith
    rw [div_le_iff₀ h1t]
    calc ‖(gramMatrix K θ)⁻¹‖ ^ 2 * ‖gramMatrix Kb θ - gramMatrix K θ‖ ≤
        p.sB ^ 2 * (sCG p * sCDK p * xX p γ εL εN δ) :=
          mul_le_mul (pow_le_pow_left₀ (norm_nonneg _) hB 2) hD (norm_nonneg _) (sq_nonneg _)
      _ = p.sB ^ 2 * sCG p * sCDK p / (1 - p.θ) * xX p γ εL εN δ * (1 - p.θ) := by
          field_simp
  refine ⟨(Matrix.isUnit_iff_isUnit_det _).1 hu, hBb, ?_⟩
  obtain ⟨-, -, r2, -⟩ := H.room
  calc _ = ‖(gramMatrix K θ)⁻¹ + ((gramMatrix Kb θ)⁻¹ - (gramMatrix K θ)⁻¹)‖ := by
        rw [add_sub_cancel]
    _ ≤ m 2 + sCBb p * xX p γ εL εN δ := (norm_add_le _ _).trans (add_le_add (H.G θ hθr).2 hBb)
    _ ≤ p.sB := r2

/-- `|L̄ B̄ - L B| ≤ C_N̄ X` and `|B̄ L̄ᵀ - B Lᵀ| ≤ C_N̄ᵀ X` on `T_{r-3δ}`. -/
theorem LB_sub_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖tangentMat (modNewton h K ω (r - 2 * δ)) θ * (gramMatrix (modNewton h K ω (r - 2 * δ)) θ)⁻¹ -
        tangentMat K θ * (gramMatrix K θ)⁻¹‖ ≤ sCNb p * xX p γ εL εN δ ∧
      ‖(gramMatrix (modNewton h K ω (r - 2 * δ)) θ)⁻¹ *
          (tangentMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ -
        (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ ≤ sCNbT p * xX p γ εL εN δ := fun θ hθ => by
  have hθr := H.sub3 hθ
  obtain ⟨h1, h2⟩ := H.Lb_sub_le hS θ hθ
  obtain ⟨hLb, -⟩ := H.Lb_le hS θ hθ
  obtain ⟨-, hBb, hBbn⟩ := H.Gb hS θ hθ
  have hX := H.X_nonneg
  have hDK := nn_sCDK H.ok
  constructor
  · refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    calc _ ≤ p.sK * (sCBb p * xX p γ εL εN δ) + n * (sCDK p * xX p γ εL εN δ) * p.sB :=
          add_le_add (mul_le_mul hLb hBb (norm_nonneg _) H.ok.caps.1.le)
            (mul_le_mul h1 (H.B' θ hθr) (norm_nonneg _) (by positivity))
      _ = sCNb p * xX p γ εL εN δ := by rw [sCNb, H.pn_real]; ring
  · refine (norm_mul_sub_mul_le _ _ _ _).trans ?_
    rw [← Matrix.transpose_sub]
    calc _ ≤ p.sB * (2 * n * (sCDK p * xX p γ εL εN δ)) + sCBb p * xX p γ εL εN δ * p.sLt :=
          add_le_add (mul_le_mul hBbn h2 (norm_nonneg _) H.ok.caps.2.2.1.le)
            (mul_le_mul hBb (H.Lt' θ hθr) (norm_nonneg _)
              (by have := nn_sCBb H.ok; positivity))
      _ = sCNbT p * xX p γ εL εN δ := by rw [sCNbT, H.pn_real]; ring

/-- `|N̄ - N| ≤ C_N̄ X`, `|N̄ᵀ - Nᵀ| ≤ C_N̄ᵀ X`, `|N̄| ≤ σ_N`, `|N̄ᵀ| ≤ σ_{Nᵀ}` on `T_{r-3δ}`. -/
theorem Nb_sub_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    (‖normalMat (modNewton h K ω (r - 2 * δ)) θ - normalMat K θ‖ ≤ sCNb p * xX p γ εL εN δ ∧
      ‖(normalMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ - (normalMat K θ)ᵀ‖ ≤
        sCNbT p * xX p γ εL εN δ) ∧
    ‖normalMat (modNewton h K ω (r - 2 * δ)) θ‖ ≤ p.sN ∧
      ‖(normalMat (modNewton h K ω (r - 2 * δ)) θ)ᵀ‖ ≤ p.sNt := fun θ hθ => by
  have hθr := H.sub3 hθ
  obtain ⟨h1, h2⟩ := H.LB_sub_le hS θ hθ
  set Kb := modNewton h K ω (r - 2 * δ)
  have e1 : normalMat Kb θ - normalMat K θ = omegaZeroMatrix n *
      (tangentMat Kb θ * (gramMatrix Kb θ)⁻¹ - tangentMat K θ * (gramMatrix K θ)⁻¹) := by
    simp only [normalMat, Matrix.mul_sub, Matrix.mul_assoc]
  have hN1 : ‖normalMat Kb θ - normalMat K θ‖ ≤ sCNb p * xX p γ εL εN δ := by
    rw [e1, norm_omegaZeroMatrix_mul]; exact h1
  have e2 : ((normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ) * omegaZeroMatrix n =
      (gramMatrix Kb θ)⁻¹ * (tangentMat Kb θ)ᵀ - (gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ := by
    rw [Matrix.sub_mul, TorsionPoly.normalMat_transpose_mul_omega,
      TorsionPoly.normalMat_transpose_mul_omega]
  have hN2 : ‖(normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ‖ ≤ sCNbT p * xX p γ εL εN δ := by
    rw [← norm_mul_omegaZeroMatrix, e2]; exact h2
  obtain ⟨-, -, -, r3, r4⟩ := H.room
  refine ⟨⟨hN1, hN2⟩, ?_, ?_⟩
  · calc _ = ‖normalMat K θ + (normalMat Kb θ - normalMat K θ)‖ := by rw [add_sub_cancel]
      _ ≤ m 3 + sCNb p * xX p γ εL εN δ := (norm_add_le _ _).trans (add_le_add (H.N θ hθr) hN1)
      _ ≤ p.sN := r3
  · calc _ = ‖(normalMat K θ)ᵀ + ((normalMat Kb θ)ᵀ - (normalMat K θ)ᵀ)‖ := by
          rw [add_sub_cancel]
      _ ≤ m 4 + sCNbT p * xX p γ εL εN δ :=
          (norm_add_le _ _).trans (add_le_add (H.Nt θ hθr) hN2)
      _ ≤ p.sNt := r4

/-- `|𝒯_ab(K̄) - 𝒯_ab(K)| ≤ C_ab X` on `T_{r-3δ}`. -/
theorem torsionAB_sub_le : ∀ θ ∈ complexStrip n (r - 3 * δ),
    ‖torsionAB h (modNewton h K ω (r - 2 * δ)) θ - torsionAB h K θ‖ ≤ sCab p * xX p γ εL εN δ :=
  fun θ hθ => by
  have hθr := H.sub3 hθ
  have hθ2 := H.sub32 hθ
  set Kb := modNewton h K ω (r - 2 * δ)
  obtain ⟨h1, h2⟩ := H.LB_sub_le hS θ hθ
  obtain ⟨-, hNb, -⟩ := H.Nb_sub_le hS θ hθ
  rw [TorsionRef.torsionAB_eq_triple, TorsionRef.torsionAB_eq_triple]
  refine (triple_sub_le' _ _ _ _ _ _).trans ?_
  have hKb𝔅 := H.Kb_mem𝔅 hS θ hθ2
  have hK𝔅 := H.K_mem θ hθr
  have hc1 := H.comm _ hKb𝔅
  have hc0 := H.comm _ hK𝔅
  have hseg : segment ℝ (Kb θ) (K θ) ⊆ 𝔅 :=
    ((convex_ball (K θ) β).segment_subset (H.Kb_mem hS θ hθ2)
      (Metric.mem_ball_self H.β_pos)).trans (H.ball θ hθr)
  have hlip := H.lip _ hKb𝔅 _ hK𝔅 hseg
  have hdK : ‖Kb θ - K θ‖ ≤ sCDK p * (p.δ * xX p γ εL εN δ) :=
    (H.Kb_sub_le hS θ hθ2).trans (mul_le_mul_of_nonneg_left H.mu_div_gd_le (nn_sCDK H.ok))
  have hZ' : ‖tangentMat Kb θ * (gramMatrix Kb θ)⁻¹‖ ≤ p.sN := by
    rw [TorsionRef.norm_L_B]; exact hNb
  have hX : ‖(gramMatrix K θ)⁻¹ * (tangentMat K θ)ᵀ‖ ≤ p.sNt := by
    rw [TorsionRef.norm_B_Lt]; exact H.Nt' θ hθr
  have hcTh := H.ok.nonneg.2.2.1
  have hcDTh := H.ok.nonneg.2.2.2.1
  have hXX := H.X_nonneg
  have hsNt := H.ok.caps.2.2.2.2.1.le
  have hsN := H.ok.caps.2.2.2.1.le
  have t1 := mul_le_mul (mul_le_mul h2 hc1 (norm_nonneg _)
    (by have := nn_sCNbT H.ok; positivity)) hZ' (norm_nonneg _)
    (by have := nn_sCNbT H.ok; positivity)
  have t2 := mul_le_mul (mul_le_mul hX (hlip.trans (mul_le_mul_of_nonneg_left hdK hcDTh))
    (norm_nonneg _) hsNt) hZ' (norm_nonneg _)
    (by have := nn_sCDK H.ok; have := H.ok.δ_pos; positivity)
  have t3 := mul_le_mul (mul_le_mul hX hc0 (norm_nonneg _) hsNt) h1 (norm_nonneg _)
    (by positivity)
  refine (add_le_add (add_le_add t1 t2) t3).trans (le_of_eq ?_)
  rw [sCab]
  simp only [H.fix, Bool.false_eq_true, ↓reduceIte]
  rw [sCab0]
  ring

end Hyp

end ModStepB

end KAM.Sharp2

end
