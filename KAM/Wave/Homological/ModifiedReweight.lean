/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Wave.Homological.ModifiedDivisors
public import KAM.Wave.Homological.Lemma1
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.FieldSimp

/-!
# Reading a Taylor Hamiltonian at a smaller gradient weight (`bpW:w5:w4-modified`, step `m-other`)

Off-frontier, source-faithful infrastructure (W5-MODIFIED, blueprint `bpW:w5:w4-modified`); the
dependency graph is still being built.

For `p₊ ≤ p+1` the inclusion `ℓ^N_{a,p+1} ⊂ ℓ^N_{a,p₊}` (norm `≤ 1`) acts on representatives as
the diagonal `D_ρ`, `ρ_j = ω_{a,p₊}(j+2)/ω_{a,p+1}(j+2) ≤ 1` (`homModRho`). `homReweight R` is the
same Taylor Hamiltonian `R ∈ 𝒯_s` (`p̄ = p+1`) read in the class with gradient weight `p₊`:
the components `c^±` become `D_ρ c^±` and the operators `M` become `D_ρ M`. The matrix entries,
the pairings `⟨c,z⟩₀`, the bilinear norms and the dual norms are unchanged (`homNormalEntry_rho`,
`homLamCLM_rho`, `homPairRep_rho`); hence the value (`homRval_reweight`) and `N̂`
(`homNhat_reweight`) are unchanged, and the field norm can only decrease
(`homXnorm_reweight_le`, `homFieldBound_reweight`).
-/

@[expose] public noncomputable section

namespace KAM.Wave

open KAM

variable {a p pb s : ℝ}

/-- The diagonal `D_ρ` (the inclusion `ℓ^N_{a,p+1} ⊂ ℓ^N_{a,p₊}` on representatives). -/
def homModRho (a p pb : ℝ) (hc : pb ≤ p + 1) : HomOp :=
  weightedDiagCLM (fun j => (homModRatio a p pb j : ℂ)) (norm_homModRatio_le hc)

theorem homModRho_apply (hc : pb ≤ p + 1) (c : HomL2) (j : ℕ+) :
    homModRho a p pb hc c j = (homModRatio a p pb j : ℂ) * c j := rfl

theorem norm_homModRho_le (hc : pb ≤ p + 1) : ‖homModRho a p pb hc‖ ≤ 1 :=
  norm_diagCLM_le _ _

theorem norm_homModRho_apply_le (hc : pb ≤ p + 1) (c : HomL2) : ‖homModRho a p pb hc c‖ ≤ ‖c‖ :=
  ((homModRho a p pb hc).le_opNorm c).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_homModRho_le hc) (norm_nonneg c))

/-- Post-composition with `D_ρ`, as a continuous linear map on `HomOp`. -/
def homModRhoL (a p pb : ℝ) (hc : pb ≤ p + 1) : HomOp →L[ℂ] HomOp :=
  ContinuousLinearMap.compL ℂ HomL2 HomL2 HomL2 (homModRho a p pb hc)

theorem homModRhoL_apply (hc : pb ≤ p + 1) (A : HomOp) :
    homModRhoL a p pb hc A = (homModRho a p pb hc).comp A := rfl

theorem norm_homModRhoL_apply_le (hc : pb ≤ p + 1) (A : HomOp) :
    ‖homModRhoL a p pb hc A‖ ≤ ‖A‖ :=
  (ContinuousLinearMap.opNorm_comp_le _ _).trans
    (by simpa using mul_le_mul_of_nonneg_right (norm_homModRho_le hc) (norm_nonneg A))

theorem kamEntry_homModRho_comp (hc : pb ≤ p + 1) (A : HomOp) (i j : ℕ+) :
    kamEntry ((homModRho a p pb hc).comp A) i j = (homModRatio a p pb i : ℂ) * kamEntry A i j :=
  rfl

/-- `ω_{a,p₊}(I)/ω_{a,p+1}(I) · ω_{a,p}(J)/ω_{a,p₊}(I) = ω_{a,p}(J)/ω_{a,p+1}(I)`. -/
theorem homNormalEntry_rho (hc : pb ≤ p + 1) (A : HomOp) (i j : ℕ+) :
    homNormalEntry_gen a p pb ((homModRho a p pb hc).comp A) i j =
      homNormalEntry_gen a p (p + 1) A i j := by
  unfold homNormalEntry_gen
  rw [kamEntry_homModRho_comp]
  unfold homModRatio homWt
  have h1 : (ellWeight a pb (i + 2) : ℂ) ≠ 0 := ellWeight_cast_ne_zero a pb (i + 2)
  have h2 : (ellWeight a (p + 1) (i + 2) : ℂ) ≠ 0 := ellWeight_cast_ne_zero a (p + 1) (i + 2)
  push_cast
  field_simp

theorem homLamD_rho (j : ℕ+) :
    homLamD_gen a p pb j * (homModRatio a p pb j : ℂ) = homLamD_gen a p (p + 1) j := by
  unfold homLamD_gen homModRatio
  have h0 : (homWt a p j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a p j).ne'
  have h1 : (homWt a pb j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a pb j).ne'
  have h2 : (homWt a (p + 1) j : ℂ) ≠ 0 := by exact_mod_cast (homWt_pos a (p + 1) j).ne'
  push_cast
  field_simp

theorem homLamDiag_rho (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (c : HomL2) :
    homLamDiag_gen ha (homPP hp hpb) (homModRho a p pb hc c) =
      homLamDiag_gen ha (homPP hp (homModPP1 p)) c := by
  ext j
  rw [homLamDiag_apply_gen, homLamDiag_apply_gen, homModRho_apply, ← mul_assoc, homLamD_rho]

theorem homLamCLM_rho (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (A : HomOp) :
    homLamCLM_gen ha (homPP hp hpb) ((homModRho a p pb hc).comp A) =
      homLamCLM_gen ha (homPP hp (homModPP1 p)) A := by
  refine ContinuousLinearMap.ext fun v => ?_
  rw [homLamCLM_apply_gen, homLamCLM_apply_gen, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, homLamDiag_rho ha hp hpb hc]

theorem homPairRep_rho (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (c z : HomL2) :
    homPairRep_gen ha (homPP hp hpb) (homModRho a p pb hc c) z =
      homPairRep_gen ha (homPP hp (homModPP1 p)) c z := by
  unfold homPairRep_gen
  rw [homLamDiag_rho ha hp hpb hc]

theorem homDualNorm_rho (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1) (c : HomL2) :
    homDualNorm_gen ha (homPP hp hpb) (homModRho a p pb hc c) =
      homDualNorm_gen ha (homPP hp (homModPP1 p)) c := by
  unfold homDualNorm_gen
  rw [homLamDiag_rho ha hp hpb hc]

theorem IsHomComp.clm {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] {u : (Fin 2 → ℂ) → E} (hu : IsHomComp s u)
    (L : E →L[ℂ] F) : IsHomComp s (fun z => L (u z)) := by
  obtain ⟨hd, hp, C, hC⟩ := hu
  refine ⟨L.differentiable.comp_differentiableOn hd, fun i z hz => by simp only [hp i z hz],
    ‖L‖ * C, fun z hz => (L.le_opNorm _).trans (mul_le_mul_of_nonneg_left (hC z hz)
      (norm_nonneg _))⟩

/-- **The reweighted Taylor Hamiltonian**: `R ∈ 𝒯_s` with `p̄ = p+1` read in the class with
gradient weight `p₊ ≤ p+1`. -/
def homReweight (hc : pb ≤ p + 1) (R : HomTaylor_gen a p (p + 1) s) : HomTaylor_gen a p pb s where
  a0 := R.a0
  b := R.b
  cp := fun z => homModRho a p pb hc (R.cp z)
  cm := fun z => homModRho a p pb hc (R.cm z)
  P := fun z => homModRhoL a p pb hc (R.P z)
  P' := fun z => homModRhoL a p pb hc (R.P' z)
  Q := fun z => homModRhoL a p pb hc (R.Q z)
  Qt := fun z => homModRhoL a p pb hc (R.Qt z)
  comp_a0 := R.comp_a0
  comp_b := R.comp_b
  comp_cp := R.comp_cp.clm _
  comp_cm := R.comp_cm.clm _
  comp_P := R.comp_P.clm _
  comp_P' := R.comp_P'.clm _
  comp_Q := R.comp_Q.clm _
  comp_Qt := R.comp_Qt.clm _
  symP := fun θ hθ i j => by
    simp only [homModRhoL_apply, homNormalEntry_rho, R.symP θ hθ i j]
  symP' := fun θ hθ i j => by
    simp only [homModRhoL_apply, homNormalEntry_rho, R.symP' θ hθ i j]
  transQ := fun θ hθ i j => by
    simp only [homModRhoL_apply, homNormalEntry_rho, R.transQ θ hθ i j]

section reweight0

variable (hc : pb ≤ p + 1)

theorem homRz_reweight (R : HomTaylor_gen a p (p + 1) s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRz_gen (homReweight hc R) θ z zb = homModRho a p pb hc (homRz_gen R θ z zb) := by
  simp [homRz_gen, homReweight, homModRhoL_apply, map_add, map_smul]

theorem homRzb_reweight (R : HomTaylor_gen a p (p + 1) s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRzb_gen (homReweight hc R) θ z zb = homModRho a p pb hc (homRzb_gen R θ z zb) := by
  simp [homRzb_gen, homReweight, homModRhoL_apply, map_add, map_smul]

end reweight0

section reweight1

variable (hc : pb ≤ p + 1)

theorem homRu_reweight (R : HomTaylor_gen a p (p + 1) s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRu_gen (homReweight hc R) θ z zb = homModRho a p pb hc (homRu_gen R θ z zb) := by
  rw [homRu_gen, homRu_gen, homRz_reweight, homRzb_reweight, ← map_add,
    ← map_smul]

theorem homRv_reweight (R : HomTaylor_gen a p (p + 1) s) (θ : Fin 2 → ℂ) (z zb : HomL2) :
    homRv_gen (homReweight hc R) θ z zb = homModRho a p pb hc (homRv_gen R θ z zb) := by
  rw [homRv_gen, homRv_gen, homRz_reweight, homRzb_reweight, ← map_sub,
    ← map_smul]

theorem homPartial_rho {u : (Fin 2 → ℂ) → HomL2} {θ : Fin 2 → ℂ} (hu : DifferentiableAt ℂ u θ)
    (i : Fin 2) :
    homPartial i (fun z => homModRho a p pb hc (u z)) θ = homModRho a p pb hc (homPartial i u θ) :=
  homPartial_clm _ hu i

theorem homPartial_rhoL {u : (Fin 2 → ℂ) → HomOp} {θ : Fin 2 → ℂ} (hu : DifferentiableAt ℂ u θ)
    (i : Fin 2) :
    homPartial i (fun z => homModRhoL a p pb hc (u z)) θ =
      homModRhoL a p pb hc (homPartial i u θ) :=
  homPartial_clm _ hu i

end reweight1

section reweight

variable (ha : 0 ≤ a) (hp : 0 ≤ p) (hpb : p ≤ pb) (hc : pb ≤ p + 1)
include ha hp hpb

/-- The angle derivatives are unchanged by the reweighting. -/
theorem homRtheta_reweight (R : HomTaylor_gen a p (p + 1) s) (i : Fin 2) {θ : Fin 2 → ℂ}
    (hθ : θ ∈ complexStrip 2 s) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homRtheta_gen ha hp hpb (homReweight hc R) i θ y z zb =
      homRtheta_gen ha hp (homModPP1 p) R i θ y z zb := by
  have hn := (isOpen_complexStrip 2 s).mem_nhds hθ
  unfold homRtheta_gen
  simp only [homReweight]
  rw [homPartial_rho hc (R.comp_cp.1.differentiableAt hn),
    homPartial_rho hc (R.comp_cm.1.differentiableAt hn),
    homPartial_rhoL hc (R.comp_P.1.differentiableAt hn),
    homPartial_rhoL hc (R.comp_Q.1.differentiableAt hn),
    homPartial_rhoL hc (R.comp_P'.1.differentiableAt hn),
    homPairRep_rho ha hp hpb hc, homPairRep_rho ha hp hpb hc]
  simp only [homModRhoL_apply, ContinuousLinearMap.comp_apply, homPairRep_rho ha hp hpb hc]

/-- **The field norm can only decrease** under the reweighting. -/
theorem homXnorm_reweight_le {r : ℝ} (hr : 0 < r) (R : HomTaylor_gen a p (p + 1) s)
    {θ : Fin 2 → ℂ} (hθ : θ ∈ complexStrip 2 s) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homXnorm_gen ha hp hpb r (homReweight hc R) θ y z zb ≤
      homXnorm_gen ha hp (homModPP1 p) r R θ y z zb := by
  unfold homXnorm_gen
  have e1 : homRy_gen (homReweight hc R) θ = homRy_gen R θ := rfl
  have e2 : (fun i => homRtheta_gen ha hp hpb (homReweight hc R) i θ y z zb) =
      fun i => homRtheta_gen ha hp (homModPP1 p) R i θ y z zb :=
    funext fun i => homRtheta_reweight ha hp hpb hc R i hθ y z zb
  rw [e1, e2, homRu_reweight, homRv_reweight]
  have h1 := norm_homModRho_apply_le (a := a) hc (homRu_gen R θ z zb)
  have h2 := norm_homModRho_apply_le (a := a) hc (homRv_gen R θ z zb)
  have : r⁻¹ * (‖homModRho a p pb hc (homRu_gen R θ z zb)‖ +
      ‖homModRho a p pb hc (homRv_gen R θ z zb)‖) ≤
      r⁻¹ * (‖homRu_gen R θ z zb‖ + ‖homRv_gen R θ z zb‖) :=
    mul_le_mul_of_nonneg_left (add_le_add h1 h2) (by positivity)
  linarith

theorem homFieldBound_reweight {r ε : ℝ} (hr : 0 < r) (R : HomTaylor_gen a p (p + 1) s)
    (hX : HomFieldBound_gen ha hp (homModPP1 p) r ε R) :
    HomFieldBound_gen ha hp hpb r ε (homReweight hc R) := fun θ y z zb hdom =>
  (homXnorm_reweight_le ha hp hpb hc hr R hdom.1 y z zb).trans (hX θ y z zb hdom)

/-- **The value is unchanged** by the reweighting. -/
theorem homRval_reweight (R : HomTaylor_gen a p (p + 1) s) (θ y : Fin 2 → ℂ) (z zb : HomL2) :
    homRval_gen ha hp hpb (homReweight hc R) θ y z zb =
      homRval_gen ha hp (homModPP1 p) R θ y z zb := by
  unfold homRval_gen
  simp only [homReweight, homModRhoL_apply, ContinuousLinearMap.comp_apply,
    homPairRep_rho ha hp hpb hc]

end reweight

theorem homNhat_reweight {a p pb s : ℝ} (hs : 0 < s) (hc : pb ≤ p + 1)
    (R : HomTaylor_gen a p (p + 1) s) (y : Fin 2 → ℂ) (z zb : HomL2) :
    homNhat_gen (homReweight hc R) y z zb = homNhat_gen R y z zb := by
  unfold homNhat_gen
  have hQ : homCoeff (homReweight hc R).Q 0 = (homModRho a p pb hc).comp (homCoeff R.Q 0) := by
    show homCoeff (fun z => homModRhoL a p pb hc (R.Q z)) 0 = _
    rw [homCoeff_clm hs R.comp_Q.1]
    rfl
  rw [hQ]
  simp only [homNormalEntry_rho]
  rfl

theorem homReweight_homSub {a p pb s : ℝ} (hc : pb ≤ p + 1) (R₁ R₂ : HomTaylor_gen a p (p + 1) s) :
    homReweight hc (R₁.homSub R₂) = (homReweight hc R₁).homSub (homReweight hc R₂) := by
  refine HomTaylor_gen.ext_of rfl rfl ?_ ?_ ?_ ?_ ?_ ?_ <;> funext z <;>
    simp [homReweight, HomTaylor_gen.homSub, map_sub]

end KAM.Wave
