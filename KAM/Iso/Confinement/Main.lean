/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Confinement.Setting
public import KAM.Iso.Confinement.PatchConst
public import KAM.Iso.Confinement.RealHam
public import KAM.Iso.Confinement.Graph
public import KAM.Iso.Confinement.Confinement

/-!
# Part 5: the assembly of I-HEAD from the output of Part 3

Blueprint nodes `bpI:p5:hd-eps`,
`hd-fix`, `hd-sol`, `hd-uniq`. `confinement_main_of_tori` is the CONDITIONAL HELPER of the
quarantine: it assumes the output structures of Part 3 (`ChartCover`, `ToriExistence`, which say
"tori exist for a finite cover of `closure B'` by patches") and never stands in for I-HEAD; the
provider closes the gap with Part 3's producer.

The proof follows the blueprint (`hd-eps`, `hd-fix`, `hd-sol`, `hd-uniq`) in three steps.

* `main_step_graph` (`hd-fix`): from the two tori at energy `E = H_ℝ(z₀)` and a patch containing
  `I₀`, the graphs `Y_±` (`torus_graph`), their base points `Ψ(E, m_±)` (`ray_base`) and the
  standing data `SepSetting`.
* `main_step_solution` (`hd-sol`, `hd-uniq`): the maximal solution through `z₀` (`gen_maximal`) is
  global and confined (`confinement_prop`), solves the lifted Hamiltonian equations
  (`realHam_solution_iff`) and is unique on every `(a, b) ∋ 0` (`realHam_unique`).
* `confinement_main_of_tori`: the threshold `ε₀` (`exists_eps0`) and the choice of patch and tori
  (`ToriExistence.tori`).
-/

public section

open Set Metric

namespace KAM.Iso.Confinement

open KAM KAM.ODE

section Main

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-- The base point `Ψ(E, m)` of a ray lies in `𝒦` and has slope `m`, when `E` is in the energy
window of the patch and `|m| ≤ δm`. -/
private theorem ray_base {hR : (Fin 2 → ℝ) → ℝ} {η₁ : ℝ} (p : EnergyPatch hR B η₁) {E m : ℝ}
    (hE : |E - hR p.c| < p.δE) (hm : |m| ≤ p.δm) : p.Ψ (E, m) ∈ p.K ∧ p.m (p.Ψ (E, m)) = m := by
  have hE' := abs_lt.1 hE
  have hm' := abs_le.1 hm
  have hQ : (E, m) ∈ p.Q :=
    ⟨⟨by linarith, by linarith⟩, ⟨hm'.1, hm'.2⟩⟩
  refine ⟨by rw [p.K_eq_image]; exact ⟨_, hQ, rfl⟩, ?_⟩
  exact congrArg Prod.snd (p.Ψ_right _ (p.Q_subset hQ))

/-- The energy `E` of a point `I₀` of the ball `B(c, ρc)` with `|E - h(I₀)| ≤ ε` and `ε < δE/4`
lies in the energy window of the patch. -/
private theorem energy_window {η₁ : ℝ} (p : EnergyPatch (realPart h) B η₁) {E ε : ℝ}
    {I₀ : Fin 2 → ℝ} (hI₀ : ‖I₀ - p.c‖ < p.ρc) (hE : |E - realPart h I₀| ≤ ε)
    (hε : ε < p.δE / 4) : |E - realPart h p.c| < p.δE := by
  have h1 := p.ball_h I₀ (mem_ball_iff_norm.2 hI₀)
  calc |E - realPart h p.c| = |(E - realPart h I₀) + (realPart h I₀ - realPart h p.c)| := by
        rw [sub_add_sub_cancel]
    _ ≤ |E - realPart h I₀| + |realPart h I₀ - realPart h p.c| := abs_add_le _ _
    _ < p.δE := by linarith [p.δE_pos]

/-- Step `hd-fix` (graphs and base points): the two tori of `ToriExistence` over a patch, at an
energy in the window, give the graphs `Y_±` and the standing data `SepSetting`. -/
private theorem main_step_graph (hd : HeadData B s₀ r₀ h B' η) {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ}
    {ε η₁ F₁ C_K : ℝ} {p : EnergyPatch (realPart h) B η₁} {r Lm LΦ κ E : ℝ}
    (hpert : PerturbData B s₀ r₀ f ε)
    (hdb : ∀ z ∈ fractD B s₀ r₀, ‖fderiv ℂ f z‖ ≤ F₁ * ε) (hC : 0 < C_K)
    (pc : PatchConst p r Lm LΦ κ) (hsm : Smallness p r Lm LΦ κ F₁ C_K (rhoInf s₀) ε)
    {I₀ : Fin 2 → ℝ} (hI₀ : ‖I₀ - p.c‖ < p.ρc) (hE : |E - realPart h I₀| ≤ ε)
    {Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {Ip Im ωp ωm : Fin 2 → ℝ}
    (Tp : TorusOutput h f ε C_K s₀ E Kp Ip ωp) (hIp : Ip = p.Ψ (E, p.mPlus))
    (Tm : TorusOutput h f ε C_K s₀ E Km Im ωm) (hIm : Im = p.Ψ (E, p.mMinus)) :
    ∃ Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ),
      SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im ∧
      Set.range (realRestriction Kp) = graphSet Yp ∧
      Set.range (realRestriction Km) = graphSet Ym := by
  have hwin := energy_window p hI₀ hE hsm.lt_dE
  have hδ := p.δm_pos
  have hplus := p.mPlus_mem
  have hminus := p.mMinus_mem
  obtain ⟨hbp, hsp⟩ := ray_base p hwin
    (abs_le.2 ⟨by linarith [hplus.1], hplus.2.le⟩)
  obtain ⟨hbm, hsm'⟩ := ray_base p hwin
    (abs_le.2 ⟨hminus.1.le, by linarith [hminus.2]⟩)
  obtain ⟨Yp, hcp, hnp, hgp, hEp⟩ := torus_graph hd.hs hsm.nonneg hsm.lt_rho hC Tp
  obtain ⟨Ym, hcm, hnm, hgm, hEm⟩ := torus_graph hd.hs hsm.nonneg hsm.lt_rho hC Tm
  subst hIp hIm
  exact ⟨Yp, Ym,
    { base := hd.toBaseData
      perturb := hpert
      dbound := hdb
      pconst := pc
      small := hsm
      plus := ⟨hcp, hnp, hEp, hbp, hsp⟩
      minus := ⟨hcm, hnm, hEm, hbm, hsm'⟩ }, hgp, hgm⟩

/-- Steps `hd-sol`, `hd-uniq`: with the standing data of a patch, the maximal solution through
`z₀` is a global solution of the lifted Hamiltonian system, stays within `η` of `z₀.2`, and
every solution on an interval `(a, b) ∋ 0` through `z₀` agrees with it. -/
private theorem main_step_solution (hd : HeadData B s₀ r₀ h B' η)
    {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {ε η₁ F₁ C_K : ℝ} {p : EnergyPatch (realPart h) B η₁}
    {r Lm LΦ κ E : ℝ} {Yp Ym : (Fin 2 → ℝ) → (Fin 2 → ℝ)} {Ip Im ωp ωm : Fin 2 → ℝ}
    {Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    (hpert : PerturbData B s₀ r₀ f ε) (hη₁ : η₁ ≤ η)
    (S : SepSetting B s₀ r₀ h f ε η₁ F₁ C_K p r Lm LΦ κ E Yp Ym Ip Im)
    (Tp : TorusOutput h f ε C_K s₀ E Kp Ip ωp) (Tm : TorusOutput h f ε C_K s₀ E Km Im ωm)
    (hgp : Set.range (realRestriction Kp) = graphSet Yp)
    (hgm : Set.range (realRestriction Km) = graphSet Ym)
    {z₀ : P2} (hz₀ : ‖z₀.2 - p.c‖ < p.ρc) (hE : E = realHamiltonian h f z₀)
    (hmem : z₀.2 ∈ B) (hη₁pos : 0 < η₁) :
    ∃ z : ℝ → P2, z 0 = z₀ ∧
      KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B univ z ∧
      (∀ t : ℝ, ‖(z t).2 - z₀.2‖ < η) ∧
      ∀ (a b : ℝ) (y : ℝ → P2), a < 0 → 0 < b → y 0 = z₀ →
        KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B (Ioo a b) y →
        ∀ t ∈ Ioo a b, y t = z t := by
  obtain ⟨⟨Tm', Tp', z, hz⟩, -⟩ := gen_maximal (isOpen_univ.prod hd.isOpen)
    (realHam_field_contDiffOn hd.toBaseData hpert) (x₀ := z₀) ⟨mem_univ _, hmem⟩
  obtain ⟨hTm, hTp, -, -, hdist⟩ := confinement_prop S Tp Tm hgp hgm hd.isOpen hz₀ hE hz
  subst hTm hTp
  have hsolU : IsSolutionIn (hamiltonianVectorField (realHamiltonian h f)) (univ ×ˢ B) univ z := by
    simpa only [eIoo_bot_top] using hz.isSolution
  have hsol : KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B univ z :=
    (realHam_solution_iff hd.toBaseData hpert univ z).2 hsolU
  refine ⟨z, hz.init, hsol, fun t => (hdist t).trans_le ?_, ?_⟩
  · linarith
  · intro a b y ha hb hy0 hy t ht
    exact realHam_unique hd.toBaseData hpert ha hb (hy0.trans hz.init.symm) hy
      (fun s _ => hsol s (mem_univ s)) t ht

/-- `bpI:p5:hd-eps`, `hd-fix`, `hd-sol`, `hd-uniq`, from the Part 3 standing data. The conditional
helper of the quarantine: it assumes the OUTPUT STRUCTURES of Part 3 (`ChartCover`,
`ToriExistence`), distinct names, never standing in for a source result; provable now. -/
theorem confinement_main_of_tori (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    {η₁ F₁ ε₁ C_K : ℝ} {patches : Set (EnergyPatch (realPart h) B η₁)}
    (hcov : ChartCover B s₀ r₀ h B' η η₁ F₁ patches)
    (htor : ToriExistence B s₀ r₀ h B' η₁ patches ε₁ C_K) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧
      ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε < ε₀ →
        ∀ z₀ : P2, z₀.2 ∈ B' →
          ∃ z : ℝ → P2, z 0 = z₀ ∧
            KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B univ z ∧
            (∀ t : ℝ, ‖(z t).2 - z₀.2‖ < η) ∧
            ∀ (a b : ℝ) (y : ℝ → P2), a < 0 → 0 < b → y 0 = z₀ →
              KAM.Iso.IsHamiltonianSolutionOn (realHamiltonian h f) B (Ioo a b) y →
              ∀ t ∈ Ioo a b, y t = z t := by
  -- `hne` is a frozen binder of I-HEAD that Part 5 does not use (`B' = ∅` is vacuous).
  have _ := hne
  have hρ : 0 < rhoInf s₀ := div_pos (lt_min hd.hs one_pos) (by norm_num)
  obtain ⟨ε₀, hε₀, hε₀₁, hpatch⟩ :=
    exists_eps0 hcov.finite htor.ε₁_pos htor.ε₁_le_one htor.CK_pos hcov.F₁_pos hρ
  refine ⟨ε₀, hε₀, fun f ε hpert hεlt z₀ hz₀ => ?_⟩
  have hI₀ : z₀.2 ∈ closure B' := subset_closure hz₀
  have hmem : z₀.2 ∈ B := hd.inside hI₀
  have hE := realHam_sub_le hd.toBaseData hpert (z := z₀) (subset_realAct hd.hr hmem)
  obtain ⟨p, hp, hρc, Kp, Km, Ip, Im, ωp, ωm, Tp, hIp, Tm, hIm⟩ :=
    htor.tori f ε hpert (hεlt.trans_le hε₀₁) z₀.2 hI₀ (realHamiltonian h f z₀) hE
  obtain ⟨r, Lm, LΦ, κ, pc, hsm⟩ := hpatch p hp
  have hsm := hsm ε hpert.nonneg hεlt
  obtain ⟨Yp, Ym, S, hgp, hgm⟩ := main_step_graph hd hpert
    (hcov.dbound f ε hpert hsm.le_one) htor.CK_pos pc hsm hρc hE Tp hIp Tm hIm
  exact main_step_solution hd hpert hcov.η₁_le S Tp Tm hgp hgm hρc rfl hmem hcov.η₁_pos

end Main

end KAM.Iso.Confinement
