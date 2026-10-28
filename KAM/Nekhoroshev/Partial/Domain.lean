/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.Partial.Constants
public import KAM.Nekhoroshev.Partial.Coordinates
public import KAM.Weighted.SupWeighted
public import KAM.Frozen.Nekhoroshev.Defs.IsPartialPerturbation
public import KAM.Frozen.Nekhoroshev.Defs.PartialComplexDomain
public import KAM.Frozen.Nekhoroshev.Defs.InnerCore
public import KAM.Frozen.Nekhoroshev.Defs.ComplexifyPhase
public import KAM.Frozen.Planetary.Defs.DegenerateHamiltonian
import KAM.Strip.AnalyticTaylor
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Part 11 (N11-E3): the block setting, the complex domain and the field equality

The block geometry `block_setting`, the signed pair `signedH`, `signedF`, the slow rescaling
`slowScale` and `blockPert`, the physical real set `physicalDomain`, the lemma `domain`
(`bpN:p11:domain`, steps `dm-pts` and `dm-norm`: complex points, holomorphy, periodicity,
reality and the weighted bound of the rescaled perturbation) and `domain_field` (step `dm-field`:
the frozen Hamiltonian field equals the signed weighted field on the physical set), with the
companions `domain_field_scaled` (slow-scaling transport of the field and of orbits, weight
`2π` to `c = 2π/λ²`, physical/scaled domain identification) and `domain_physical_analytic`
(holomorphic-real restriction and real analyticity of the frozen Hamiltonian on the physical set).
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.
-/

@[expose] public noncomputable section

open Set Metric
open KAM.Weighted

namespace KAM.Nekhoroshev

variable {n k : ℕ}

def block_setting (a : PartialData n k) (μ : ℝ) (Ic : Fin n → ℝ) (r : ℝ) : PartialBlock n k :=
  ⟨Ic, innerCore a.D (3*(constants a).d μ/4), r, (constants a).d μ/4⟩
def signedH (a : PartialData n k) (σ : ℝ) (I : Fin n → ℂ) : ℂ :=
  (σ:ℂ)*a.h I/(2*(Real.pi:ℂ))
def signedF (_a : PartialData n k) (σ μ : ℝ) (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ)
    (z : EC n k) : ℂ :=
  (σ*μ/(2*Real.pi):ℝ)*P (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)
/-- Pull physical slow coordinates back by the fixed block scale. -/
def slowScale (lam : ℝ) (z : EC n k) : EC n k :=
  (z.1, Fin.append (fastAction z)
    (Fin.append (fun i => (lam:ℂ)*(slowPair z).1 i) (fun i => (lam:ℂ)*(slowPair z).2 i)))
def blockPert (a : PartialData n k) (μ σ : ℝ) (Ic : Fin n → ℝ) (r : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) : EC n k → ℂ :=
  signedF a σ μ P ∘ slowScale (block_setting a μ Ic r).lam

/-- Physical period-one coordinates (no block-dependent coordinate scale). -/
def physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) : Set (ER n k) :=
  {z | ‖fastAction z-Ic‖ < R ∧ ∃ v ∈ S, ‖slowPair z-v‖ < w}

/-- The physical phase point attached to an extended point (cf. `signedF`). -/
private def blockLift (z : EC n k) : (Fin (n+k) → ℂ) × (Fin (n+k) → ℂ) :=
  (Fin.append (fun i => (2*Real.pi:ℂ)*z.1 i) (slowPair z).1,
    Fin.append (fastAction z) (slowPair z).2)

private theorem signedF_eq (a : PartialData n k) (σ μ : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (z : EC n k) :
    signedF a σ μ P z = ((σ*μ/(2*Real.pi):ℝ):ℂ) * P (blockLift z) := rfl

@[simp] private theorem fastAction_slowScale (lam : ℝ) (z : EC n k) :
    fastAction (slowScale lam z) = fastAction z := by
  funext i
  simp [fastAction, slowScale, Fin.append_left]

@[simp] private theorem slowPair_slowScale_fst (lam : ℝ) (z : EC n k) (i : Fin k) :
    (slowPair (slowScale lam z)).1 i = (lam:ℂ) * (slowPair z).1 i := by
  simp [slowPair, slowScale, Fin.append_right, Fin.append_left]

@[simp] private theorem slowPair_slowScale_snd (lam : ℝ) (z : EC n k) (i : Fin k) :
    (slowPair (slowScale lam z)).2 i = (lam:ℂ) * (slowPair z).2 i := by
  show Fin.append _ (Fin.append _ _) (Fin.natAdd n (Fin.natAdd k i)) = _
  rw [Fin.append_right, Fin.append_right]

private theorem blockLift_extCx (w : ER n k) :
    blockLift (extCx w) = complexifyPhase (thetaInv w) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_left]
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_right, slowPair]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_left, fastAction]
    · simp [blockLift, complexifyPhase, thetaInv, extCx, Fin.append_right, slowPair]

private theorem realWfield_const_mul {σ : ℝ} (hσ : σ = 1 ∨ σ = -1) (c : ℝ) (f : ER n k → ℝ)
    (z : ER n k) :
    realWfield c (fun w => σ * f w) z = σ • realWfield c f z := by
  have hA : ∀ v, fderiv ℝ (fun w => σ * f w) z v = σ * fderiv ℝ f z v := fun v => by
    rcases hσ with rfl | rfl
    · simp
    · have hf : (fun w => (-1:ℝ) * f w) = -f := by funext w; show _ = -(f w); ring
      rw [hf, fderiv_neg]; simp
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp only [realWfield, Prod.smul_fst, Pi.smul_apply, smul_eq_mul, hA]
  · refine ext_cases (P := fun i => (realWfield c (fun w => σ * f w) z).2 i =
        (σ • realWfield c f z).2 i) (fun j => ?_) (fun j => ?_) (fun j => ?_) i
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left]
      ring
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left,
        Fin.append_right]
      ring
    · simp only [realWfield, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, hA, Fin.append_left,
        Fin.append_right]
      ring

theorem domain_field (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h)
      (fun _ w => (P (complexifyPhase w)).re) μ
    EqOn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
      (realWfield (2*Real.pi)
        (fun z => (liftFast (signedH a σ) (extCx z)+signedF a σ μ P (extCx z)).re))
      (physicalDomain Ic R b.w b.S) := by
  intro b H z _
  have hpt : ∀ w : ER n k, σ * converted H w =
      (liftFast (signedH a σ) (extCx w) + signedF a σ μ P (extCx w)).re := by
    intro w
    have hfast : (KAM.Planetary.fast (b := k) (thetaInv w).2) = fastAction w := by
      funext i; simp [KAM.Planetary.fast, thetaInv, Fin.append_left, fastAction]
    have hrp : realPart a.h (fastAction w) = (a.h (fastAction (extCx w))).re := rfl
    simp only [converted, H, KAM.Planetary.degenerateHamiltonian, hfast, hrp, liftFast, signedH,
      signedF_eq, blockLift_extCx, Complex.add_re, Complex.re_ofReal_mul]
    have hc : ∀ x : ℂ, ((σ:ℂ) * x / (2*(Real.pi:ℂ))).re = σ/(2*Real.pi) * x.re := fun x => by
      have : (σ:ℂ) * x / (2*(Real.pi:ℂ)) = ((σ/(2*Real.pi):ℝ):ℂ) * x := by push_cast; ring
      rw [this, Complex.re_ofReal_mul]
    have : (2*Real.pi) ≠ 0 := by positivity
    simp only [hc]
    field_simp
  have hfun : (fun w => (liftFast (signedH a σ) (extCx w) + signedF a σ μ P (extCx w)).re) =
      fun w => σ * converted H w := funext fun w => (hpt w).symm
  simp only [hfun]
  exact (realWfield_const_mul hσ.1 _ _ z).symm

/-- A real ball around a point of `G` of radius at most `ρ` lies in the complex collar. -/
theorem polyNbhd_realBall_subset (a : PartialData n k) {Ic : Fin n → ℝ} (hIc : Ic ∈ a.G)
    {R : ℝ} (hR : R ≤ a.ρ) :
    polyNbhd {KAM.realInclusion n Ic} R ⊆ KAM.actionNbhd a.G' a.ρ := by
  rintro I ⟨I', hI', hlt⟩
  rw [mem_singleton_iff] at hI'
  subst hI'
  exact ⟨Ic, a.collar Ic hIc (mem_closedBall_self a.hρ.le), hlt.trans_le hR⟩

private theorem d_pos (a : PartialData n k) {μ : ℝ} (hμ : 0 < μ) : 0 < (constants a).d μ :=
  Real.rpow_pos_of_pos hμ _

private theorem lam_mul (a : PartialData n k) {μ R : ℝ} {Ic : Fin n → ℝ} (hμ : 0 < μ)
    (hR : 0 < R) : (block_setting a μ Ic R).lam * R = (constants a).d μ / 4 := by
  have := d_pos a hμ
  simp only [PartialBlock.lam, block_setting]
  field_simp

private theorem lam_pos (a : PartialData n k) {μ R : ℝ} {Ic : Fin n → ℝ} (hμ : 0 < μ)
    (hR : 0 < R) : 0 < (block_setting a μ Ic R).lam := by
  have := d_pos a hμ
  simp only [PartialBlock.lam, block_setting]
  positivity

private theorem two_s (a : PartialData n k) :
    (constants a).s + (constants a).s = a.ρ / (2*Real.pi) := by
  simp only [PartialConstants.s, constants]
  have := Real.pi_pos
  field_simp
  ring

private theorem s_pos (a : PartialData n k) : 0 < (constants a).s := by
  simp only [PartialConstants.s, constants]
  have := a.hρ
  positivity

private theorem blockLift_fst_castAdd (z : EC n k) (j : Fin n) :
    (blockLift z).1 (Fin.castAdd k j) = (2*Real.pi:ℂ) * z.1 j := by
  unfold blockLift; dsimp only; exact Fin.append_left _ _ _

private theorem blockLift_fst_natAdd (z : EC n k) (j : Fin k) :
    (blockLift z).1 (Fin.natAdd n j) = (slowPair z).1 j := by
  unfold blockLift; dsimp only; exact Fin.append_right _ _ _

private theorem blockLift_snd_castAdd (z : EC n k) (j : Fin n) :
    (blockLift z).2 (Fin.castAdd k j) = fastAction z j := by
  unfold blockLift; dsimp only; exact Fin.append_left _ _ _

private theorem blockLift_snd_natAdd (z : EC n k) (j : Fin k) :
    (blockLift z).2 (Fin.natAdd n j) = (slowPair z).2 j := by
  unfold blockLift; dsimp only; exact Fin.append_right _ _ _

/-- Complex points of the block domain lie in the frozen tube (step `dm-pts`). -/
private theorem blockLift_mem (a : PartialData n k) {μ R : ℝ} {Ic : Fin n → ℝ} (hμ : 0 < μ)
    (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ) {z : EC n k}
    (hz : z ∈ Dom n (block_setting a μ Ic R).base R ((constants a).s + (constants a).s)) :
    blockLift (slowScale (block_setting a μ Ic R).lam z) ∈ partialComplexDomain a.G' a.D a.ρ := by
  obtain ⟨hθ, J, ⟨x, hxS, hJx⟩, hJ⟩ := hz
  have hr0 : R ≤ a.ρ / 2 := hRR.trans (min_le_left _ _)
  have hρ := a.hρ
  have hdp := d_pos a hμ
  set lam := (block_setting a μ Ic R).lam with hlam
  have hl : 0 < lam := lam_pos a hμ hR
  have hlR : lam * R = (constants a).d μ / 4 := lam_mul a hμ hR
  have hcomp : ∀ j, ‖z.2 j - J j‖ < R := fun j => (norm_le_pi_norm (z.2 - J) j).trans_lt hJ
  have hJ1 : ∀ i : Fin n, J (Fin.castAdd (k+k) i) = (Ic i : ℂ) := fun i => by
    rw [hJx, Fin.append_left]; rfl
  have hJ2 : ∀ i : Fin k, J (Fin.natAdd n (Fin.castAdd k i)) = ((x.1 i / lam : ℝ) : ℂ) :=
    fun i => by rw [hJx, Fin.append_right, Fin.append_left]
  have hJ3 : ∀ i : Fin k, J (Fin.natAdd n (Fin.natAdd k i)) = ((x.2 i / lam : ℝ) : ℂ) :=
    fun i => by rw [hJx, Fin.append_right, Fin.append_right]
  have hc1 : ∀ i : Fin n, ‖z.2 (Fin.castAdd (k+k) i) - (Ic i : ℂ)‖ < R := fun i => by
    have := hcomp (Fin.castAdd (k+k) i)
    rwa [hJ1 i] at this
  have key : ∀ (y : ℂ) (xr : ℝ), ‖y - ((xr / lam : ℝ) : ℂ)‖ < R →
      ‖(lam : ℂ) * y - (xr : ℂ)‖ < (constants a).d μ / 4 := fun y xr h => by
    have : (lam : ℂ) * y - (xr : ℂ) = (lam : ℂ) * (y - ((xr / lam : ℝ) : ℂ)) := by
      have : (lam : ℂ) ≠ 0 := by exact_mod_cast hl.ne'
      push_cast; field_simp
    rw [this, norm_mul, Complex.norm_real, Real.norm_of_nonneg hl.le, ← hlR]
    exact mul_lt_mul_of_pos_left h hl
  have hc2 : ∀ i : Fin k, ‖(lam : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd k i)) - (x.1 i : ℂ)‖ <
      (constants a).d μ / 4 := fun i => by
    have := hcomp (Fin.natAdd n (Fin.castAdd k i))
    rw [hJ2 i] at this
    exact key _ _ this
  have hc3 : ∀ i : Fin k, ‖(lam : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd k i)) - (x.2 i : ℂ)‖ <
      (constants a).d μ / 4 := fun i => by
    have := hcomp (Fin.natAdd n (Fin.natAdd k i))
    rw [hJ3 i] at this
    exact key _ _ this
  have hre : ∀ w : ℂ, |w.re| ≤ ‖w‖ := Complex.abs_re_le_norm
  have him : ∀ w : ℂ, |w.im| ≤ ‖w‖ := Complex.abs_im_le_norm
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- fast actions
    refine a.collar Ic hIc ?_
    rw [mem_closedBall_iff_norm]
    refine (pi_norm_le_iff_of_nonneg a.hρ.le).2 fun i => ?_
    show ‖((blockLift (slowScale lam z)).2 (Fin.castAdd k i)).re - Ic i‖ ≤ a.ρ
    rw [blockLift_snd_castAdd, fastAction_slowScale]
    have h' : ‖(fastAction z i).re - Ic i‖ ≤ ‖z.2 (Fin.castAdd (k+k) i) - (Ic i : ℂ)‖ := by
      have := hre (z.2 (Fin.castAdd (k+k) i) - (Ic i : ℂ))
      simpa [fastAction] using this
    linarith [hc1 i]
  · -- slow coordinates
    refine hxS.2 ?_
    rw [mem_closedBall_iff_norm, Prod.norm_def]
    simp only [Prod.fst_sub, Prod.snd_sub]
    refine max_le ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
      ((pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_)
    · show ‖((blockLift (slowScale lam z)).1 (Fin.natAdd n i)).re - x.1 i‖ ≤ _
      rw [blockLift_fst_natAdd, slowPair_slowScale_fst]
      have := hre ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd k i)) - (x.1 i : ℂ))
      have h2 := hc2 i
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      rw [Real.norm_eq_abs]
      exact this.trans (h2.le.trans (by linarith))
    · show ‖((blockLift (slowScale lam z)).2 (Fin.natAdd n i)).re - x.2 i‖ ≤ _
      rw [blockLift_snd_natAdd, slowPair_slowScale_snd]
      have := hre ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd k i)) - (x.2 i : ℂ))
      have h2 := hc3 i
      simp only [Complex.sub_re, Complex.ofReal_re] at this
      rw [Real.norm_eq_abs]
      exact this.trans (h2.le.trans (by linarith))
  · -- angle strip
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [blockLift_fst_castAdd]
      have h1 := hθ j
      have e : (((2*Real.pi:ℂ)) * (slowScale lam z).1 j).im = 2*Real.pi * (z.1 j).im := by
        simp [Complex.mul_im, slowScale]
      rw [e, abs_mul, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi)]
      have := two_s a
      calc 2*Real.pi * |(z.1 j).im| < 2*Real.pi * ((constants a).s + (constants a).s) := by
            gcongr
        _ = a.ρ := by rw [this]; field_simp
    · rw [blockLift_fst_natAdd, slowPair_slowScale_fst]
      have h' := (him _).trans (hc2 j).le
      have h2 : ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd k j)) - (x.1 j : ℂ)).im =
          ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.castAdd k j))).im := by simp
      rw [h2] at h'
      exact h'.trans_lt (by linarith)
  · -- action strip
    intro i
    refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · rw [blockLift_snd_castAdd, fastAction_slowScale]
      have h' := (him _).trans (hc1 j).le
      have h2 : (z.2 (Fin.castAdd (k+k) j) - (Ic j : ℂ)).im = (z.2 (Fin.castAdd (k+k) j)).im := by
        simp
      rw [h2] at h'
      show |(z.2 (Fin.castAdd (k+k) j)).im| < a.ρ
      linarith [hc1 j]
    · rw [blockLift_snd_natAdd, slowPair_slowScale_snd]
      have h' := (him _).trans (hc3 j).le
      have h2 : ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd k j)) - (x.2 j : ℂ)).im =
          ((lam : ℂ) * z.2 (Fin.natAdd n (Fin.natAdd k j))).im := by simp
      rw [h2] at h'
      exact h'.trans_lt (by linarith)

private theorem differentiable_blockLift (lam : ℝ) :
    Differentiable ℂ (fun z : EC n k => blockLift (slowScale lam z)) := by
  refine Differentiable.prodMk (differentiable_pi.2 fun i => ?_) (differentiable_pi.2 fun i => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have e : (fun z : EC n k => (blockLift (slowScale lam z)).1 (Fin.castAdd k j)) =
          fun z => (2*Real.pi:ℂ) * z.1 j := funext fun z => blockLift_fst_castAdd _ _
      show Differentiable ℂ (fun z : EC n k => (blockLift (slowScale lam z)).1 (Fin.castAdd k j))
      rw [e]; fun_prop
    · have e : (fun z : EC n k => (blockLift (slowScale lam z)).1 (Fin.natAdd n j)) =
          fun z => (lam:ℂ) * z.2 (Fin.natAdd n (Fin.castAdd k j)) := funext fun z => by
        rw [blockLift_fst_natAdd, slowPair_slowScale_fst]; rfl
      show Differentiable ℂ (fun z : EC n k => (blockLift (slowScale lam z)).1 (Fin.natAdd n j))
      rw [e]; fun_prop
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · have e : (fun z : EC n k => (blockLift (slowScale lam z)).2 (Fin.castAdd k j)) =
          fun z => z.2 (Fin.castAdd (k+k) j) := funext fun z => by
        rw [blockLift_snd_castAdd, fastAction_slowScale]; rfl
      show Differentiable ℂ (fun z : EC n k => (blockLift (slowScale lam z)).2 (Fin.castAdd k j))
      rw [e]; fun_prop
    · have e : (fun z : EC n k => (blockLift (slowScale lam z)).2 (Fin.natAdd n j)) =
          fun z => (lam:ℂ) * z.2 (Fin.natAdd n (Fin.natAdd k j)) := funext fun z => by
        rw [blockLift_snd_natAdd, slowPair_slowScale_snd]; rfl
      show Differentiable ℂ (fun z : EC n k => (blockLift (slowScale lam z)).2 (Fin.natAdd n j))
      rw [e]; fun_prop

private theorem blockLift_shift (lam : ℝ) (z : EC n k) (j : Fin n) :
    blockLift (slowScale lam (z.1 + Pi.single j 1, z.2)) = blockLift (slowScale lam z) +
      complexifyPhase (KAM.Planetary.fastShift (b := k) (Pi.single j (1:ℤ))) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [Prod.fst_add, Pi.add_apply, blockLift_fst_castAdd, blockLift_fst_castAdd]
      simp only [complexifyPhase, KAM.Planetary.fastShift, Fin.append_left]
      by_cases hl : l = j
      · subst hl; simp [slowScale]; ring
      · simp [slowScale, hl]
    · rw [Prod.fst_add, Pi.add_apply, blockLift_fst_natAdd, blockLift_fst_natAdd]
      simp only [complexifyPhase, KAM.Planetary.fastShift, Fin.append_right]
      simp [slowPair, slowScale]
  · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
    · rw [Prod.snd_add, Pi.add_apply, blockLift_snd_castAdd, blockLift_snd_castAdd]
      simp [complexifyPhase, KAM.Planetary.fastShift, fastAction_slowScale]
      rfl
    · rw [Prod.snd_add, Pi.add_apply, blockLift_snd_natAdd, blockLift_snd_natAdd]
      simp [complexifyPhase, KAM.Planetary.fastShift, slowPair, slowScale]

private theorem slowScale_extCx (lam : ℝ) (x : ER n k) :
    slowScale lam (extCx x) = extCx (x.1, Fin.append (fastAction x)
      (Fin.append (fun i => lam * (slowPair x).1 i) (fun i => lam * (slowPair x).2 i))) := by
  refine Prod.ext rfl (funext fun i => ?_)
  refine ext_cases (P := fun i => (slowScale lam (extCx x)).2 i = (extCx (x.1, Fin.append
    (fastAction x) (Fin.append (fun i => lam * (slowPair x).1 i)
      (fun i => lam * (slowPair x).2 i)))).2 i) (fun j => ?_) (fun j => ?_) (fun j => ?_) i
  · simp [slowScale, extCx, fastAction, Fin.append_left]
  · simp [slowScale, extCx, slowPair, Fin.append_left, Fin.append_right]
  · simp only [slowScale, extCx, slowPair, Fin.append_right]
    push_cast; rfl

private theorem norm_signed (σ μ : ℝ) (hσ : σ = 1 ∨ σ = -1) (hμ : 0 < μ) :
    ‖((σ*μ/(2*Real.pi):ℝ):ℂ)‖ = μ / (2*Real.pi) := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases hσ with rfl | rfl
  · rw [abs_of_pos (by positivity)]; ring_nf
  · rw [abs_of_neg (by have := Real.pi_pos; apply div_neg_of_neg_of_pos <;> nlinarith)]; ring

theorem domain (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    polyNbhd {KAM.realInclusion n Ic} R ⊆ KAM.actionNbhd a.G' a.ρ ∧
    ext_class b R (constants a).s (blockPert a μ σ Ic R P) ∧
    WBound b.base R (constants a).s (blockPert a μ σ Ic R P) ((constants a).eps μ) := by
  intro b
  have hr0 : R ≤ a.ρ / 2 := hRR.trans (min_le_left _ _)
  have hρ := a.hρ
  have hs := s_pos a
  have hmem : ∀ z ∈ Dom n b.base R ((constants a).s + (constants a).s),
      blockLift (slowScale b.lam z) ∈ partialComplexDomain a.G' a.D a.ρ := fun z hz =>
    blockLift_mem a hμ hIc hR hRR hd hz
  have hdiff : DifferentiableOn ℂ (blockPert a μ σ Ic R P)
      (Dom n b.base R ((constants a).s + (constants a).s)) := by
    have h1 : DifferentiableOn ℂ (fun z : EC n k => P (blockLift (slowScale b.lam z)))
        (Dom n b.base R ((constants a).s + (constants a).s)) :=
      hP.1.comp (differentiable_blockLift b.lam).differentiableOn hmem
    exact (h1.const_mul _)
  have hper : ∀ j : Fin n, ∀ z ∈ Dom n b.base R ((constants a).s + (constants a).s),
      blockPert a μ σ Ic R P (z.1 + Pi.single j 1, z.2) = blockPert a μ σ Ic R P z := by
    intro j z hz
    simp only [blockPert, Function.comp, signedF_eq]
    rw [blockLift_shift]
    rw [hP.2.2.2 _ (hmem z hz)]
  have hbd : ∀ z ∈ Dom n b.base R ((constants a).s + (constants a).s),
      ‖blockPert a μ σ Ic R P z‖ ≤ μ / (2*Real.pi) := by
    intro z hz
    simp only [blockPert, Function.comp, signedF_eq]
    rw [norm_mul, norm_signed σ μ hσ.1 hμ]
    calc μ / (2*Real.pi) * ‖P (blockLift (slowScale b.lam z))‖ ≤ μ / (2*Real.pi) * 1 := by
          gcongr; exact hP.2.1 _ (hmem z hz)
      _ = μ / (2*Real.pi) := mul_one _
  have hcls : InClass b.base R ((constants a).s + (constants a).s) (blockPert a μ σ Ic R P) :=
    ⟨hdiff, hper⟩
  have hle : (constants a).s ≤ (constants a).s + (constants a).s := by linarith
  refine ⟨polyNbhd_realBall_subset a hIc (hr0.trans (by linarith)), ⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
  · exact hdiff.mono (Dom_mono le_rfl hle)
  · intro j z hz
    exact hper j z (Dom_mono le_rfl hle hz)
  · intro x hx
    have hx2 := Dom_mono (n := n) le_rfl hle hx
    have hz : extCx x ∈ Dom n b.base R ((constants a).s + (constants a).s) := hx2
    have hw := hP.2.2.1 (thetaInv ((x.1, Fin.append (fastAction x)
      (Fin.append (fun i => b.lam * (slowPair x).1 i) (fun i => b.lam * (slowPair x).2 i)))))
    have hlift : blockLift (slowScale b.lam (extCx x)) = complexifyPhase (thetaInv ((x.1,
        Fin.append (fastAction x) (Fin.append (fun i => b.lam * (slowPair x).1 i)
          (fun i => b.lam * (slowPair x).2 i))))) := by
      rw [slowScale_extCx, blockLift_extCx]
    have hm := hmem _ hz
    rw [hlift] at hm
    have hPim := hw hm
    show (blockPert a μ σ Ic R P (extCx x)).im = 0
    simp only [blockPert, Function.comp, signedF_eq]
    rw [hlift, Complex.im_ofReal_mul, hPim, mul_zero]
  · have := wbound_of_sup_bound (D := b.base) (r := R) (s := (constants a).s)
      (σ := (constants a).s) hs hs hcls hbd
    have e : coth (Real.pi * (constants a).s) ^ n * (μ / (2*Real.pi)) = (constants a).eps μ := by
      simp only [PartialConstants.eps, PartialConstants.kappaC, constants]
      ring
    rwa [e] at this

/-! ### The slow scaling of the physical field (step `dm-field`) -/

/-- The real slow scaling `(θ; I, q, p) ↦ (θ; I, λ q, λ p)` as a continuous linear map; on
`extCx` it is the real form of `slowScale`. -/
def slowScaleReal (lam : ℝ) : ER n k →L[ℝ] ER n k :=
  (ContinuousLinearMap.id ℝ (Fin n → ℝ)).prodMap
    (LinearMap.toContinuousLinearMap
      { toFun := fun v i => Fin.append (fun _ : Fin n => (1:ℝ)) (fun _ : Fin (k+k) => lam) i * v i
        map_add' := fun x y => funext fun i => mul_add _ _ _
        map_smul' := fun c x => funext fun i => by simp [mul_left_comm] })

private theorem slowScaleReal_fst (lam : ℝ) (z : ER n k) : (slowScaleReal lam z).1 = z.1 := rfl

private theorem slowScaleReal_castAdd (lam : ℝ) (z : ER n k) (i : Fin n) :
    (slowScaleReal lam z).2 (Fin.castAdd (k+k) i) = z.2 (Fin.castAdd (k+k) i) := by
  simp [slowScaleReal, Fin.append_left]

private theorem slowScaleReal_natAdd (lam : ℝ) (z : ER n k) (j : Fin (k+k)) :
    (slowScaleReal lam z).2 (Fin.natAdd n j) = lam * z.2 (Fin.natAdd n j) := by
  simp [slowScaleReal, Fin.append_right]

private theorem slowScaleReal_inv {lam : ℝ} (h : lam ≠ 0) (z : ER n k) :
    slowScaleReal lam⁻¹ (slowScaleReal lam z) = z := by
  refine Prod.ext rfl (funext fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [slowScaleReal_castAdd, slowScaleReal_castAdd]
  · rw [slowScaleReal_natAdd, slowScaleReal_natAdd, inv_mul_cancel_left₀ h]

private def slowEquiv {lam : ℝ} (h : lam ≠ 0) : ER n k ≃L[ℝ] ER n k :=
  ContinuousLinearEquiv.equivOfInverse (slowScaleReal lam) (slowScaleReal lam⁻¹)
    (slowScaleReal_inv h) (fun z => by
      have := slowScaleReal_inv (inv_ne_zero h) z
      rwa [inv_inv] at this)

private theorem fderiv_slowScaleReal {lam : ℝ} (h : lam ≠ 0) (K : ER n k → ℝ) (z u : ER n k) :
    fderiv ℝ (fun y => K (slowScaleReal lam y)) z u =
      fderiv ℝ K (slowScaleReal lam z) (slowScaleReal lam u) := by
  have := congrArg (fun L : ER n k →L[ℝ] ℝ => L u)
    ((slowEquiv h).comp_right_fderiv (f := K) (x := z))
  exact this

private theorem slowScaleReal_single_fast (lam : ℝ) (i : Fin n) :
    slowScaleReal lam (0, Pi.single (Fin.castAdd (k+k) i) 1) =
      (0, Pi.single (Fin.castAdd (k+k) i) 1) := by
  refine Prod.ext rfl (funext fun m => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) m
  · rw [slowScaleReal_castAdd]
  · rw [slowScaleReal_natAdd]
    have hne : Fin.natAdd n j ≠ Fin.castAdd (k+k) i := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, hne]

private theorem slowScaleReal_single_slow (lam : ℝ) (j : Fin (k+k)) :
    slowScaleReal lam (0, Pi.single (Fin.natAdd n j) 1) =
      lam • ((0 : Fin n → ℝ), Pi.single (Fin.natAdd n j) (1:ℝ)) := by
  refine Prod.ext (by simp [slowScaleReal]) (funext fun m => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) m
  · rw [slowScaleReal_castAdd]
    have hne : Fin.castAdd (k+k) i ≠ Fin.natAdd n j := fun h => by
      have := congrArg Fin.val h
      simp at this
      omega
    simp [Pi.single_apply, hne]
  · rw [slowScaleReal_natAdd]
    simp [Pi.single_apply]

private theorem slowScaleReal_single_angle (lam : ℝ) (i : Fin n) :
    slowScaleReal lam ((Pi.single i 1 : Fin n → ℝ), (0 : Fin (n+(k+k)) → ℝ)) =
      (Pi.single i 1, 0) := by
  refine Prod.ext rfl (funext fun m => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) m
  · rw [slowScaleReal_castAdd]
  · rw [slowScaleReal_natAdd]; simp

/-- Chain rule for the slow scaling: the weight-`2π/λ²` field of `K ∘ S_λ` is `S_λ⁻¹` of the
weight-`2π` field of `K`. -/
private theorem slowScaleReal_realWfield {lam : ℝ} (hl : 0 < lam) (K : ER n k → ℝ) (z : ER n k) :
    slowScaleReal lam (realWfield (2*Real.pi/lam^2) (fun y => K (slowScaleReal lam y)) z) =
      realWfield (2*Real.pi) K (slowScaleReal lam z) := by
  have h0 : lam ≠ 0 := hl.ne'
  have hfd := fun u => fderiv_slowScaleReal h0 K z u
  refine Prod.ext ?_ (funext fun m => ?_)
  · funext i
    show fderiv ℝ (fun y => K (slowScaleReal lam y)) z (0, Pi.single (Fin.castAdd (k+k) i) 1) = _
    rw [hfd, slowScaleReal_single_fast]
    rfl
  · refine ext_cases (P := fun m => (slowScaleReal lam (realWfield (2*Real.pi/lam^2)
      (fun y => K (slowScaleReal lam y)) z)).2 m =
        (realWfield (2*Real.pi) K (slowScaleReal lam z)).2 m) (fun j => ?_) (fun j => ?_)
      (fun j => ?_) m
    · rw [slowScaleReal_castAdd]
      simp only [realWfield, Fin.append_left]
      rw [hfd, slowScaleReal_single_angle]
    · rw [slowScaleReal_natAdd]
      simp only [realWfield, Fin.append_right, Fin.append_left]
      rw [hfd, slowScaleReal_single_slow, map_smul]
      simp only [smul_eq_mul]
      field_simp
    · rw [slowScaleReal_natAdd]
      simp only [realWfield, Fin.append_right, Fin.append_left]
      rw [hfd, slowScaleReal_single_slow, map_smul]
      simp only [smul_eq_mul]
      field_simp

private theorem slowScale_castAdd (lam : ℝ) (z : EC n k) (i : Fin n) :
    (slowScale lam z).2 (Fin.castAdd (k+k) i) = z.2 (Fin.castAdd (k+k) i) := by
  simp [slowScale, Fin.append_left, fastAction]

private theorem slowScale_natAdd (lam : ℝ) (z : EC n k) (j : Fin (k+k)) :
    (slowScale lam z).2 (Fin.natAdd n j) = (lam:ℂ) * z.2 (Fin.natAdd n j) := by
  refine Fin.addCases (fun i => ?_) (fun i => ?_) j
  · show Fin.append _ (Fin.append _ _) (Fin.natAdd n (Fin.castAdd k i)) = _
    rw [Fin.append_right, Fin.append_left]; rfl
  · show Fin.append _ (Fin.append _ _) (Fin.natAdd n (Fin.natAdd k i)) = _
    rw [Fin.append_right, Fin.append_right]; rfl

private theorem slowScale_extCx_real (lam : ℝ) (x : ER n k) :
    slowScale lam (extCx x) = extCx (slowScaleReal lam x) := by
  refine Prod.ext rfl (funext fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [slowScale_castAdd]
    show _ = ((slowScaleReal lam x).2 (Fin.castAdd (k+k) j) : ℂ)
    rw [slowScaleReal_castAdd]; rfl
  · rw [slowScale_natAdd]
    show _ = ((slowScaleReal lam x).2 (Fin.natAdd n j) : ℂ)
    rw [slowScaleReal_natAdd]; push_cast; rfl

private theorem slowScale_inv {lam : ℝ} (h : lam ≠ 0) (z : EC n k) :
    slowScale lam (slowScale lam⁻¹ z) = z := by
  have h' : (lam : ℂ) ≠ 0 := by exact_mod_cast h
  refine Prod.ext rfl (funext fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · rw [slowScale_castAdd, slowScale_castAdd]
  · rw [slowScale_natAdd, slowScale_natAdd]
    push_cast
    exact mul_inv_cancel_left₀ h' _

private theorem differentiable_slowScale (lam : ℝ) :
    Differentiable ℂ (slowScale (n := n) (k := k) lam) := by
  refine Differentiable.prodMk differentiable_fst (differentiable_pi.2 fun i => ?_)
  refine Fin.addCases (fun j => ?_) (fun j => ?_) i
  · have e : (fun z : EC n k => (slowScale lam z).2 (Fin.castAdd (k+k) j)) =
        fun z => z.2 (Fin.castAdd (k+k) j) := funext fun z => slowScale_castAdd _ _ _
    show Differentiable ℂ (fun z : EC n k => (slowScale lam z).2 (Fin.castAdd (k+k) j))
    rw [e]; fun_prop
  · have e : (fun z : EC n k => (slowScale lam z).2 (Fin.natAdd n j)) =
        fun z => (lam:ℂ) * z.2 (Fin.natAdd n j) := funext fun z => slowScale_natAdd _ _ _
    show Differentiable ℂ (fun z : EC n k => (slowScale lam z).2 (Fin.natAdd n j))
    rw [e]; fun_prop

private theorem realWfield_congr {c : ℝ} {f g : ER n k → ℝ} {z : ER n k}
    (h : f =ᶠ[nhds z] g) : realWfield c f z = realWfield c g z := by
  unfold realWfield
  rw [h.fderiv_eq]

private theorem isOpen_physicalDomain (Ic : Fin n → ℝ) (R w : ℝ) (S : Set (KAM.Planetary.Phase k)) :
    IsOpen (physicalDomain Ic R w S) := by
  have hf : Continuous (fun z : ER n k => fastAction z) :=
    continuous_pi fun i => (continuous_apply _).comp continuous_snd
  have hs : Continuous (fun z : ER n k => slowPair z) :=
    Continuous.prodMk (continuous_pi fun i => (continuous_apply _).comp continuous_snd)
      (continuous_pi fun i => (continuous_apply _).comp continuous_snd)
  have e : physicalDomain Ic R w S = {z | ‖fastAction z - Ic‖ < R} ∩
      ⋃ v ∈ S, {z | ‖slowPair z - v‖ < w} := by
    ext z; simp [physicalDomain]
  rw [e]
  exact (isOpen_lt (hf.sub continuous_const).norm continuous_const).inter
    (isOpen_biUnion fun v _ => isOpen_lt (hs.sub continuous_const).norm continuous_const)

private theorem mem_realDom_iff (a : PartialData n k) {μ R : ℝ} {Ic : Fin n → ℝ} (hμ : 0 < μ)
    (hR : 0 < R) (z : ER n k) :
    z ∈ (block_setting a μ Ic R).realDom R ↔
      slowScaleReal (block_setting a μ Ic R).lam z ∈
        physicalDomain Ic R (block_setting a μ Ic R).w (block_setting a μ Ic R).S := by
  set lam := (block_setting a μ Ic R).lam with hlam
  have hl : 0 < lam := lam_pos a hμ hR
  have hlR : lam * R = (block_setting a μ Ic R).w := lam_mul a hμ hR
  have hw : 0 < (block_setting a μ Ic R).w := by rw [← hlR]; positivity
  have hnorm : ∀ x y : ℝ, ‖(x:ℂ) - (y:ℂ)‖ = |x - y| := fun x y => by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  have key : ∀ y xr : ℝ, |y - xr/lam| < R ↔ |lam*y - xr| < (block_setting a μ Ic R).w := by
    intro y xr
    have e : lam*y - xr = lam * (y - xr/lam) := by field_simp
    rw [e, abs_mul, abs_of_pos hl, ← hlR]
    exact (mul_lt_mul_iff_of_pos_left hl).symm
  constructor
  · rintro ⟨-, J, ⟨x, hxS, hJx⟩, hJ⟩
    have hcomp : ∀ j, ‖((z.2 j : ℝ) : ℂ) - J j‖ < R := fun j =>
      (norm_le_pi_norm ((extCx z).2 - J) j).trans_lt hJ
    refine ⟨(pi_norm_lt_iff hR).2 fun i => ?_, x, hxS, ?_⟩
    · have := hcomp (Fin.castAdd (k+k) i)
      rw [hJx, Fin.append_left] at this
      show |((slowScaleReal lam z).2 (Fin.castAdd (k+k) i)) - Ic i| < R
      rw [slowScaleReal_castAdd]
      rwa [hnorm] at this
    · rw [Prod.norm_def]
      refine max_lt ((pi_norm_lt_iff hw).2 fun i => ?_) ((pi_norm_lt_iff hw).2 fun i => ?_)
      · have := hcomp (Fin.natAdd n (Fin.castAdd k i))
        rw [hJx, Fin.append_right, Fin.append_left, hnorm] at this
        show |(slowScaleReal lam z).2 (Fin.natAdd n (Fin.castAdd k i)) - x.1 i| < _
        rw [slowScaleReal_natAdd]
        exact (key _ _).1 this
      · have := hcomp (Fin.natAdd n (Fin.natAdd k i))
        rw [hJx, Fin.append_right, Fin.append_right, hnorm] at this
        show |(slowScaleReal lam z).2 (Fin.natAdd n (Fin.natAdd k i)) - x.2 i| < _
        rw [slowScaleReal_natAdd]
        exact (key _ _).1 this
  · rintro ⟨hf, v, hv, hs⟩
    refine ⟨fun i => by simp [extCx], Fin.append (fun i => (Ic i : ℂ))
      (Fin.append (fun i => ((v.1 i/lam : ℝ) : ℂ)) (fun i => ((v.2 i/lam : ℝ) : ℂ))),
      ⟨v, hv, rfl⟩, (pi_norm_lt_iff hR).2 fun j => ?_⟩
    rw [Prod.norm_def] at hs
    have hs1 := (pi_norm_lt_iff hw).1 (max_lt_iff.1 hs).1
    have hs2 := (pi_norm_lt_iff hw).1 (max_lt_iff.1 hs).2
    have hf' := (pi_norm_lt_iff hR).1 hf
    refine Fin.addCases (fun i => ?_) (fun i => ?_) j
    · have := hf' i
      change |((slowScaleReal lam z).2 (Fin.castAdd (k+k) i)) - Ic i| < R at this
      rw [slowScaleReal_castAdd] at this
      show ‖((z.2 (Fin.castAdd (k+k) i) : ℝ) : ℂ) -
        Fin.append (fun i => (Ic i : ℂ)) (Fin.append (fun i => ((v.1 i/lam : ℝ) : ℂ))
          (fun i => ((v.2 i/lam : ℝ) : ℂ))) (Fin.castAdd (k+k) i)‖ < R
      rw [Fin.append_left, hnorm]
      exact this
    · refine Fin.addCases (fun l => ?_) (fun l => ?_) i
      · have := hs1 l
        change |(slowScaleReal lam z).2 (Fin.natAdd n (Fin.castAdd k l)) - v.1 l| < _ at this
        rw [slowScaleReal_natAdd] at this
        show ‖((z.2 (Fin.natAdd n (Fin.castAdd k l)) : ℝ) : ℂ) -
          Fin.append (fun i => (Ic i : ℂ)) (Fin.append (fun i => ((v.1 i/lam : ℝ) : ℂ))
            (fun i => ((v.2 i/lam : ℝ) : ℂ))) (Fin.natAdd n (Fin.castAdd k l))‖ < R
        rw [Fin.append_right, Fin.append_left, hnorm]
        exact (key _ _).2 this
      · have := hs2 l
        change |(slowScaleReal lam z).2 (Fin.natAdd n (Fin.natAdd k l)) - v.2 l| < _ at this
        rw [slowScaleReal_natAdd] at this
        show ‖((z.2 (Fin.natAdd n (Fin.natAdd k l)) : ℝ) : ℂ) -
          Fin.append (fun i => (Ic i : ℂ)) (Fin.append (fun i => ((v.1 i/lam : ℝ) : ℂ))
            (fun i => ((v.2 i/lam : ℝ) : ℂ))) (Fin.natAdd n (Fin.natAdd k l))‖ < R
        rw [Fin.append_right, Fin.append_right, hnorm]
        exact (key _ _).2 this

private theorem converted_eq (a : PartialData n k) (σ μ : ℝ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (w : ER n k) :
    σ * converted (KAM.Planetary.degenerateHamiltonian (realPart a.h)
      (fun _ w => (P (complexifyPhase w)).re) μ) w =
      (liftFast (signedH a σ) (extCx w) + signedF a σ μ P (extCx w)).re := by
  have hfast : (KAM.Planetary.fast (b := k) (thetaInv w).2) = fastAction w := by
    funext i; simp [KAM.Planetary.fast, thetaInv, Fin.append_left, fastAction]
  have hrp : realPart a.h (fastAction w) = (a.h (fastAction (extCx w))).re := rfl
  simp only [converted, KAM.Planetary.degenerateHamiltonian, hfast, hrp, liftFast, signedH,
    signedF_eq, blockLift_extCx, Complex.add_re, Complex.re_ofReal_mul]
  have hc : ∀ x : ℂ, ((σ:ℂ) * x / (2*(Real.pi:ℂ))).re = σ/(2*Real.pi) * x.re := fun x => by
    have : (σ:ℂ) * x / (2*(Real.pi:ℂ)) = ((σ/(2*Real.pi):ℝ):ℂ) * x := by push_cast; ring
    rw [this, Complex.re_ofReal_mul]
  have : (2*Real.pi) ≠ 0 := by positivity
  simp only [hc]
  field_simp

/-- `stepN:p11:dm-field` (slow scaling): for the fixed positive `λ = w/R` the physical field of
`σ Ĥ_μ` at weight `2π` is carried by the slow scaling `S_λ` to the field of the signed block
Hamiltonian `h̆ + f̆` at weight `c = 2π/λ²` on the scaled domain `W^e_R`; the scaled and physical
domains correspond, the physical domain is open, and block orbits go to physical orbits. -/
theorem domain_field_scaled (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h)
      (fun _ w => (P (complexifyPhase w)).re) μ
    0 < b.lam ∧ b.c * b.lam ^ 2 = 2 * Real.pi ∧
    IsOpen (physicalDomain Ic R b.w b.S) ∧
    (∀ z, z ∈ b.realDom R ↔ slowScaleReal b.lam z ∈ physicalDomain Ic R b.w b.S) ∧
    (∀ z ∈ b.realDom R,
      slowScaleReal b.lam (realWfield b.c (realHamiltonianExt b R
        (fun z => liftFast (signedH a σ) z + blockPert a μ σ Ic R P z)) z) =
      σ • realWfield (2*Real.pi) (converted H) (slowScaleReal b.lam z)) ∧
    ∀ (J : Set ℝ) (y : ℝ → ER n k),
      ExtOrbit b R (fun z => liftFast (signedH a σ) z + blockPert a μ σ Ic R P z) J y ↔
      KAM.ODE.IsSolutionIn (fun z => σ • realWfield (2*Real.pi) (converted H) z)
        (physicalDomain Ic R b.w b.S) J (fun t => slowScaleReal b.lam (y t)) := by
  intro b H
  have hl : 0 < b.lam := lam_pos a hμ hR
  have h0 : b.lam ≠ 0 := hl.ne'
  have hc : b.c = 2*Real.pi/b.lam^2 := rfl
  have hdf := domain_field a hμ hσ hIc hR hRR hd P hP
  have hopen : IsOpen (b.realDom R) := by
    have hc : Continuous (extCx : ER n k → EC n k) := by unfold extCx; fun_prop
    exact (isOpen_Dom b.base R 1).preimage hc
  have hfield : ∀ z ∈ b.realDom R,
      slowScaleReal b.lam (realWfield b.c (realHamiltonianExt b R
        (fun z => liftFast (signedH a σ) z + blockPert a μ σ Ic R P z)) z) =
      σ • realWfield (2*Real.pi) (converted H) (slowScaleReal b.lam z) := by
    intro z hz
    have hev : realHamiltonianExt b R
        (fun z => liftFast (signedH a σ) z + blockPert a μ σ Ic R P z) =ᶠ[nhds z]
        fun y => (liftFast (signedH a σ) (extCx (slowScaleReal b.lam y)) +
          signedF a σ μ P (extCx (slowScaleReal b.lam y))).re := by
      filter_upwards [hopen.mem_nhds hz] with y hy
      have e1 : fastAction (extCx (slowScaleReal b.lam y)) = fastAction (extCx y) := by
        funext i; exact congrArg Complex.ofReal (slowScaleReal_castAdd _ _ _)
      simp only [realHamiltonianExt, Set.indicator_of_mem hy, liftFast, blockPert,
        Function.comp, e1, slowScale_extCx_real]
      rfl
    rw [realWfield_congr hev, hc]
    exact (slowScaleReal_realWfield hl (fun y => (liftFast (signedH a σ) (extCx y) +
      signedF a σ μ P (extCx y)).re) z).trans
      (hdf ((mem_realDom_iff a hμ hR z).1 hz)).symm
  refine ⟨hl, ?_, isOpen_physicalDomain _ _ _ _, mem_realDom_iff a hμ hR, hfield, ?_⟩
  · rw [hc]; field_simp
  · intro J y
    constructor
    · intro hy t ht
      obtain ⟨hyW, hder⟩ := hy t ht
      refine ⟨(mem_realDom_iff a hμ hR _).1 hyW, ?_⟩
      have := (slowScaleReal b.lam).hasFDerivAt.comp_hasDerivAt t hder
      rw [hfield _ hyW] at this
      exact this
    · intro hy t ht
      obtain ⟨hyW, hder⟩ := hy t ht
      have hyW' : y t ∈ b.realDom R := (mem_realDom_iff a hμ hR _).2 hyW
      refine ⟨hyW', ?_⟩
      have := (slowScaleReal b.lam⁻¹).hasFDerivAt.comp_hasDerivAt t hder
      have e1 : (fun t => slowScaleReal b.lam⁻¹ (slowScaleReal b.lam (y t))) = y :=
        funext fun t => slowScaleReal_inv h0 _
      have e2 : slowScaleReal b.lam⁻¹ (σ • realWfield (2*Real.pi) (converted H)
          (slowScaleReal b.lam (y t))) = realWfield b.c (realHamiltonianExt b R
            (fun z => liftFast (signedH a σ) z + blockPert a μ σ Ic R P z)) (y t) := by
        rw [← hfield _ hyW', slowScaleReal_inv h0]
      simpa only [Function.comp_def, e1, e2] using this

private theorem isOpen_actionNbhd_cx (B : Set (Fin n → ℝ)) (r : ℝ) :
    IsOpen (KAM.actionNbhd B r) := by
  have : KAM.actionNbhd B r = ⋃ J ∈ B, ball (fun i => (J i : ℂ)) r := by
    ext I
    simp [KAM.actionNbhd, dist_eq_norm]
  rw [this]
  exact isOpen_biUnion fun _ _ => isOpen_ball

/-- `stepN:p11:dm-field` (physical analyticity): `σ Ĥ_μ` is the real part of the function
`liftFast (signedH) + signedF`, holomorphic on an open set of complex points containing the
real points of the physical domain, so `Ĥ_μ` is real analytic there. -/
theorem domain_physical_analytic (a : PartialData n k) {μ σ R : ℝ} {Ic : Fin n → ℝ}
    (hμ : 0 < μ) (hσ : DefiniteSign a σ) (hIc : Ic ∈ a.G) (hR : 0 < R) (hRR : R ≤ (constants a).r0)
    (hd : (constants a).d μ ≤ a.ρ)
    (P : ((Fin (n+k) → ℂ) × (Fin (n+k) → ℂ)) → ℂ) (hP : IsPartialPerturbation a.G' a.D a.ρ P) :
    let b := block_setting a μ Ic R
    let H := KAM.Planetary.degenerateHamiltonian (realPart a.h)
      (fun _ w => (P (complexifyPhase w)).re) μ
    let F : EC n k → ℂ := fun z => liftFast (signedH a σ) z + signedF a σ μ P z
    (∀ w : ER n k, σ * converted H w = (F (extCx w)).re) ∧
    (∃ Ω : Set (EC n k), IsOpen Ω ∧ (∀ w ∈ physicalDomain Ic R b.w b.S, extCx w ∈ Ω) ∧
      DifferentiableOn ℂ F Ω) ∧
    AnalyticOnNhd ℝ (converted H) (physicalDomain Ic R b.w b.S) := by
  intro b H F
  have hl : 0 < b.lam := lam_pos a hμ hR
  have h0 : b.lam ≠ 0 := hl.ne'
  have hdom := domain a hμ hσ hIc hR hRR hd P hP
  have hcls : DifferentiableOn ℂ (blockPert a μ σ Ic R P) (Dom n b.base R (constants a).s) :=
    hdom.2.1.1.1
  have hs := s_pos a
  have hr0 : R ≤ a.ρ / 2 := hRR.trans (min_le_left _ _)
  have hRρ : R ≤ a.ρ := by linarith [a.hρ]
  have hfa : Continuous (fun z : EC n k => fastAction z) :=
    continuous_pi fun i => (continuous_apply _).comp continuous_snd
  have hfd : Differentiable ℂ (fun z : EC n k => fastAction z) :=
    differentiable_pi.2 fun i => by
      show Differentiable ℂ (fun z : EC n k => z.2 (Fin.castAdd (k+k) i))
      fun_prop
  have hsF : ∀ z, signedF a σ μ P z = blockPert a μ σ Ic R P (slowScale b.lam⁻¹ z) := fun z => by
    simp only [blockPert, Function.comp]
    rw [show b.lam = b.lam from rfl, slowScale_inv h0]
  let Ω : Set (EC n k) := {z | fastAction z ∈ KAM.actionNbhd a.G' a.ρ} ∩
    {z | slowScale b.lam⁻¹ z ∈ Dom n b.base R (constants a).s}
  have hΩ : IsOpen Ω :=
    ((isOpen_actionNbhd_cx _ _).preimage hfa).inter
      ((isOpen_Dom b.base R _).preimage (differentiable_slowScale _).continuous)
  have hmem : ∀ w ∈ physicalDomain Ic R b.w b.S, extCx w ∈ Ω := by
    intro w hw
    have hz0 : slowScaleReal b.lam⁻¹ w ∈ b.realDom R := by
      refine (mem_realDom_iff a hμ hR _).2 ?_
      have := slowScaleReal_inv (inv_ne_zero h0) w
      rw [inv_inv] at this
      show slowScaleReal b.lam (slowScaleReal b.lam⁻¹ w) ∈ _
      rw [this]
      exact hw
    refine ⟨?_, ?_⟩
    · refine polyNbhd_realBall_subset a hIc hRρ ⟨KAM.realInclusion n Ic, rfl, ?_⟩
      have e : fastAction (extCx w) = KAM.realInclusion n (fastAction w) := rfl
      rw [e, ← map_sub, KAM.norm_realInclusion]
      exact hw.1
    · show slowScale b.lam⁻¹ (extCx w) ∈ Dom n b.base R (constants a).s
      rw [slowScale_extCx_real]
      exact ⟨fun i => by simpa [extCx] using hs, hz0.2⟩
  have hdiff : DifferentiableOn ℂ F Ω := by
    have h1 : DifferentiableOn ℂ (liftFast (signedH a σ) : EC n k → ℂ) Ω := by
      have h2 : DifferentiableOn ℂ (signedH a σ) (KAM.actionNbhd a.G' a.ρ) := by
        show DifferentiableOn ℂ (fun I => (σ:ℂ) * a.h I / (2*(Real.pi:ℂ))) _
        have h4 : DifferentiableOn ℂ (fun I => (σ:ℂ) * a.h I * (2*(Real.pi:ℂ))⁻¹) _ :=
          (a.hol.const_mul (σ:ℂ)).mul_const _
        exact h4.congr fun I _ => by simp [div_eq_mul_inv]
      exact h2.comp hfd.differentiableOn (fun z hz => hz.1)
    have h3 : DifferentiableOn ℂ (fun z => signedF a σ μ P z) Ω := by
      have := hcls.comp (differentiable_slowScale b.lam⁻¹).differentiableOn
        (fun z (hz : z ∈ Ω) => hz.2)
      exact this.congr fun z _ => hsF z
    exact h1.add h3
  have hconv : ∀ w : ER n k, σ * converted H w = (F (extCx w)).re := fun w =>
    converted_eq a σ μ P w
  refine ⟨hconv, ⟨Ω, hΩ, hmem, hdiff⟩, fun w hw => ?_⟩
  have hσ1 : σ * σ = 1 := by rcases hσ.1 with rfl | rfl <;> norm_num
  have e : converted H = fun w => σ * (F (extCx w)).re := funext fun w => by
    rw [← hconv w, ← mul_assoc, hσ1, one_mul]
  rw [e]
  have hC : AnalyticAt ℂ F (extCx w) := by
    exact KAM.analyticOnNhd_of_differentiableOn hΩ hdiff _ (hmem w hw)
  have hF : AnalyticAt ℝ F (extCx w) := hC.restrictScalars
  have hex : AnalyticAt ℝ (extCx : ER n k → EC n k) w :=
    ((KAM.realInclusion n).prodMap (KAM.realInclusion (n+(k+k)))).analyticAt w
  exact analyticAt_const.mul ((Complex.reCLM.analyticAt _).comp (hF.comp hex))

end KAM.Nekhoroshev

end
