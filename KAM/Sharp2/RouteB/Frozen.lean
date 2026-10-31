/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Sharp2.RouteB.G1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# Route B with the default refined data: the literal frozen body

Lemma `bp:p2s2:defaults` for route B: `g1_v2B_frozen` (verbatim) concludes the literal
`KAM.Sharp.G1Body`. The refined data are derived from the frozen ones:

* `|A Ω₀ - Ω₀ A| ≤ 2|A| ≤ 2M ≤ c_Th` (`norm_hamComm_le`) and, on a segment in `𝔅`,
  `|Δ(A Ω₀ - Ω₀ A)| ≤ 2|ΔA| ≤ 2M |Δz| ≤ c_DTh |Δz|` (`norm_hamComm_sub_le`, mean value inequality
  with `|D²X_h| ≤ M`);
* `|Lᵀ| ≤ 2n(σ_K - μ)`, `|N| ≤ (σ_K - μ)(σ_B - μ)`, `|Nᵀ| ≤ 2n(σ_K - μ)(σ_B - μ)`
  (`KAM.Sharp.frame_bounds`), the values of `defaultInitB`;
* the certificates on the Diophantine set, `hcert` (a statement on the numbers alone).

Unlike route A (`g1_v2A_frozen`), no torsion bound is derived: route B's torsion cap is derived
inside the run (`bp:p2s2:torsion-ref`), so there is no `TorsionOk` premise.
-/

@[expose] public noncomputable section

open scoped Matrix.Norms.Operator
open Matrix Filter Topology

namespace KAM.Sharp2.RouteB

open KAM KAM.Torus KAM.Apost KAM.Sharp KAM.Sharp2

variable {n : ℕ}

/-- `|A Ω₀ - Ω₀ A| ≤ 2 |A|`. -/
theorem norm_hamComm_le {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {z : (Fin n → ℂ) × (Fin n → ℂ)}
    {M : ℝ} (hA : ‖fderiv ℂ (hamiltonianVectorFieldℂ h) z‖ ≤ M) : ‖hamComm h z‖ ≤ 2 * M := by
  unfold hamComm
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul, norm_sqMat]
  linarith

/-- `|Δ(A Ω₀ - Ω₀ A)| ≤ 2 M |Δz|` on a segment in `𝔅`, from `|D²X_h| ≤ M`. -/
theorem norm_hamComm_sub_le {τ M σK σB σT γ : ℝ} {𝔅 : Set ((Fin n → ℂ) × (Fin n → ℂ))}
    {h : (Fin n → ℂ) × (Fin n → ℂ) → ℂ} {ω : Fin n → ℝ} (hS : Standing n τ M σK σB σT 𝔅 h ω γ)
    {z z' : (Fin n → ℂ) × (Fin n → ℂ)} (hz : z ∈ 𝔅) (hz' : z' ∈ 𝔅) (hseg : segment ℝ z z' ⊆ 𝔅) :
    ‖hamComm h z - hamComm h z'‖ ≤ 2 * M * ‖z - z'‖ := by
  have _hz := hz
  have _hz' := hz'
  have hd := differentiableOn_fderiv_ham hS
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le (𝕜 := ℂ)
    (f := fderiv ℂ (hamiltonianVectorFieldℂ h)) (s := segment ℝ z' z)
    (fun x hx => hd.differentiableAt (hS.isOpen.mem_nhds (hseg (segment_symm ℝ z z' ▸ hx))))
    (fun x hx => by
      rw [norm_fderiv_fderiv_eq]
      exact (hS.bounds x (hseg (segment_symm ℝ z z' ▸ hx))).2.2)
    (convex_segment z' z) (left_mem_segment ℝ z' z) (right_mem_segment ℝ z' z)
  have e : hamComm h z - hamComm h z' =
      sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z - fderiv ℂ (hamiltonianVectorFieldℂ h) z') *
          omegaZeroMatrix n -
        omegaZeroMatrix n *
          sqMat (fderiv ℂ (hamiltonianVectorFieldℂ h) z -
            fderiv ℂ (hamiltonianVectorFieldℂ h) z') := by
    rw [PerturbationAux.sqMat_sub]
    unfold hamComm
    simp only [Matrix.sub_mul, Matrix.mul_sub]
    abel
  rw [e]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul_omegaZeroMatrix, norm_omegaZeroMatrix_mul, norm_sqMat]
  linarith

/-- Route B, literal frozen `KAM.Sharp.G1Body` with the default refined data
(`bp:p2s2:defaults`): the commutator data are implied by `|DX_h|, |D²X_h| ≤ M`, and `hcert` is a
statement on the numbers alone (classical constants: `sdConst_classical`,
`sdConst_classical_of_le`). -/
theorem g1_v2B_frozen {n : ℕ} {N : NumB n} (hN : N.Wf) (hfix : N.iso = false)
    (hτ : (n : ℝ) - 1 ≤ N.τ)
    {M σK σB σT μ γbar Xs : ℝ} (hM : 0 < M) (hσK : μ < σK) (hσB : μ < σB) (hσT : 0 < σT)
    (hμ : 0 < μ) (hγbar : γbar = N.γb) (hsK : N.sK = σK - μ / 2) (hsB : σB - μ < N.sB)
    (hM1 : N.M1 = M) (hM2 : N.M2 = M) (hcTh : 2 * M ≤ N.cTh) (hcDTh : 2 * M ≤ N.cDTh)
    (hI : (defaultInitB n σK σB μ).Wf N σT μ) (hfit : N.Fits (defaultInitB n σK σB μ))
    (hOk : routeBOk N (capB N σT μ 0) (initB (defaultInitB n σK σB μ) σK σB μ) (μ / 2) Xs)
    (hXpos : 0 < Xs)
    (hcert : ∀ γ, 0 < γ → γ ≤ γbar → N.Cert γ {ω | IsDiophantine γ N.τ ω}) :
    0 < min (sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf)
        (c1B N (defaultInitB n σK σB μ) Xs) ∧
      0 < max (sharpC2 n N.τ (cohConstR n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
        (c2B N (defaultInitB n σK σB μ) Xs) ∧
      G1Body n N.τ N.ρ N.ρinf M σK σB σT μ γbar
        (min (sharpC1 n N.τ (cohConstR n N.τ) M σK σB σT γbar μ N.τ N.ρ N.ρinf)
          (c1B N (defaultInitB n σK σB μ) Xs))
        (max (sharpC2 n N.τ (cohConstR n N.τ) M σK σB σT γbar N.τ N.ρ N.ρinf)
          (c2B N (defaultInitB n σK σB μ) Xs)) := by
  have hσK0 : 0 < σK := hμ.trans hσK
  have hσB0 : 0 < σB := hμ.trans hσB
  obtain ⟨hC1, hC2, hbody⟩ := g1_v2B hN hfix hτ (defaultInitB n σK σB μ) hM hσK0 hσB0 hσT hμ
    hγbar hsK hsB hI hfit hOk hXpos
  refine ⟨hC1, hC2, ?_⟩
  intro 𝔅 h K ω γ e hopen htransl hholo hper hreal hbd hK hKp hKr hball hDK hG hTu hTb hγ hγγbar
    hdio hE hsm
  have hSv : Standing n N.τ M σK σB σT 𝔅 h ω γ :=
    { toParams := ⟨hN.two_le, hτ, hM, hσK0, hσB0, hσT⟩
      isOpen := hopen
      transl_mem := htransl
      holo := hholo
      periodic := hper
      real := hreal
      bounds := fun z hz => ⟨(hbd z hz).2.1, (hbd z hz).2.2.1, (hbd z hz).2.2.2⟩
      gamma_pos := hγ
      dio := hdio }
  have hK𝔅 : ∀ θ ∈ complexStrip n N.ρ, K θ ∈ 𝔅 := fun θ hθ =>
    hball θ hθ (Metric.mem_ball_self hμ)
  have hGn : ∀ θ ∈ complexStrip n N.ρ, ‖(gramMatrix K θ)⁻¹‖ ≤ σB - μ := fun θ hθ =>
    norm_le_of_rowSum_le hN.two_le (hG θ hθ).2
  have hfb : ∀ θ ∈ complexStrip n N.ρ, _ := fun θ hθ =>
    frame_bounds hSv (hK𝔅 θ hθ) (hDK θ hθ) (hG θ hθ).1 (hGn θ hθ) ω
  have hRef : RefHypB N (defaultInitB n σK σB μ) 𝔅 h K N.ρ :=
    { dX := fun z hz => hM1 ▸ (hbd z hz).2.2.1
      d2X := fun z hz => hM2 ▸ (hbd z hz).2.2.2
      comm := fun z hz => (norm_hamComm_le ((hbd z hz).2.2.1)).trans hcTh
      lip := fun z hz z' hz' hseg => (norm_hamComm_sub_le hSv hz hz' hseg).trans
        (mul_le_mul_of_nonneg_right hcDTh (norm_nonneg _))
      tangentT := fun θ hθ => (hfb θ hθ).2.1
      normal := fun θ hθ => (hfb θ hθ).2.2.1
      normalT := fun θ hθ => (hfb θ hθ).2.2.2.2.1 }
  exact hbody 𝔅 h K ω γ e {ω | IsDiophantine γ N.τ ω} hopen htransl hholo hper hreal hbd hK hKp
    hKr hball hDK hG hTu hTb hRef hdio (hcert γ hγ hγγbar) hγ hγγbar hdio hE hsm



end KAM.Sharp2.RouteB

end
