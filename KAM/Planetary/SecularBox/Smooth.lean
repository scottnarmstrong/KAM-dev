/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Kepler.Plane
public import KAM.Planetary.SecularBox.Region
public import KAM.Planetary.SecularBox.ParametricIntegral
public import KAM.Frozen.Planetary.Defs.EllipseMomentum
public import KAM.Frozen.Planetary.Defs.ExactSecularHamiltonian
public import KAM.Frozen.Planetary.Defs.MovingHamiltonian
public import KAM.Frozen.Planetary.Defs.SecularIntegrand
public import KAM.Frozen.Planetary.Defs.SecularRegular

/-!
# Smoothness of the exact secular Hamiltonian

`sb_smooth_prop` (blueprint `bpP:p14:sb-smooth-prop`) with its internal steps `sb-sm-1`
(`secular_integrand_identity`: the frozen integrand after `assemble` is the explicit one),
`sb-sm-2` (`secular_integrand_smooth`: joint `C^∞` on `S × ℝ²` and `2π`-periodicity) and `sb-sm-3`
(`secular_parametric_integral`, from `SecularBox/ParametricIntegral`), `sb-sm-4` (regularity).
-/

@[expose] public noncomputable section

open Set MeasureTheory
open scoped ContDiff
open KAM.Kepler

namespace KAM.Planetary

private theorem sbSmooth_cd_body {n : ℕ} (i : Fin n) (k : Fin 2) :
    ContDiff ℝ ∞ fun z : Phase (n*2) => bodyVector z.1 i k := by
  unfold bodyVector; fun_prop

private theorem sbSmooth_cd_planeLength {α : Type*} [NormedAddCommGroup α] [NormedSpace ℝ α]
    {f : α → Fin 2 → ℝ}
    {x : α} (hf : ContDiffAt ℝ ∞ f x) (h0 : 0 < planeLength (f x)) :
    ContDiffAt ℝ ∞ (fun y => planeLength (f y)) x :=
  ContDiffAt.comp (g := planeLength) x
    ((analyticAt_planeLength (planeLength_pos_iff.1 h0)).contDiffAt.of_le le_top) hf

private theorem sbSmooth_cd_moving (m : Fin 2 → ℝ) (mu : ℝ) {z : Phase (2*2)}
    (hz : NoCollision z.1) :
    ContDiffAt ℝ ∞ (movingHamiltonian 1 1 m mu) z := by
  have hb : ∀ i, ContDiffAt ℝ ∞ (fun z : Phase (2*2) => bodyVector z.1 i) z := fun i =>
    contDiffAt_pi.2 fun k => (sbSmooth_cd_body i k).contDiffAt
  have hb2 : ∀ i, ContDiffAt ℝ ∞ (fun z : Phase (2*2) => bodyVector z.2 i) z := fun i =>
    contDiffAt_pi.2 fun k => by
      unfold bodyVector; fun_prop
  have hsq : ∀ v : Fin 2 → ℝ, planeSq v = v 0 ^ 2 + v 1 ^ 2 := fun v => by
    simp [planeSq, Fin.sum_univ_two]
  have hdot : ∀ v w : Fin 2 → ℝ, planeDot v w = v 0 * w 0 + v 1 * w 1 := fun v w => by
    simp [planeDot, Fin.sum_univ_two]
  have hpos : ∀ i, 0 < planeLength (bodyVector z.1 i) := hz.1
  have hdiff : ∀ i j, i ≠ j → ContDiffAt ℝ ∞
      (fun z : Phase (2*2) => planeLength (bodyVector z.1 i - bodyVector z.1 j)) z :=
    fun i j hij => sbSmooth_cd_planeLength ((hb i).sub (hb j)) (hz.2 i j hij)
  unfold movingHamiltonian
  refine ContDiffAt.add (ContDiffAt.sum fun i _ => ?_) (contDiffAt_const.mul
    (ContDiffAt.sum fun i _ => ContDiffAt.sum fun j hj => ?_))
  · refine ContDiffAt.sub ?_ (contDiffAt_const.div (sbSmooth_cd_planeLength (hb i) (hpos i))
      (hpos i).ne')
    simp only [hsq]
    have h0 := contDiffAt_pi.1 (hb2 i) 0
    have h1 := contDiffAt_pi.1 (hb2 i) 1
    exact ((contDiffAt_const.mul ((h0.pow 2).add (h1.pow 2))).div_const 2)
  · have hij : i ≠ j := (Finset.mem_filter.1 hj).2.ne
    refine ContDiffAt.sub ?_ (contDiffAt_const.div (hdiff i j hij) (hz.2 i j hij).ne')
    simp only [hdot]
    have a0 := contDiffAt_pi.1 (hb2 i) 0
    have a1 := contDiffAt_pi.1 (hb2 i) 1
    have b0 := contDiffAt_pi.1 (hb2 j) 0
    have b1 := contDiffAt_pi.1 (hb2 j) 1
    exact ((a0.mul b0).add (a1.mul b1)).div_const _

section Ellipse

variable {m : Fin 2 → ℝ} {p : Phase (2+2) × (Fin 2 → ℝ)} (i : Fin 2)

private theorem sbSmooth_cd_fast :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => fast p.1.2 i := by
  unfold fast; fun_prop
private theorem sbSmooth_cd_slow1 :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => slow p.1.1 i := by
  unfold slow; fun_prop
private theorem sbSmooth_cd_slow2 :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => slow p.1.2 i := by
  unfold slow; fun_prop
private theorem sbSmooth_cd_F :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => p.2 i := by fun_prop

private theorem sbSmooth_cd_gamma :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => secularGamma p.1 i := by
  unfold secularGamma oscillatorAction
  have := sbSmooth_cd_slow1 i
  have := sbSmooth_cd_slow2 i
  fun_prop

private theorem sbSmooth_cd_root (hL : 0 < fast p.1.2 i) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) => secularRoot p.1 i) p := by
  unfold secularRoot
  exact contDiffAt_const.sub (((sbSmooth_cd_gamma i).contDiffAt).div
    (sbSmooth_cd_fast i).contDiffAt hL.ne')

private theorem sbSmooth_cd_scale (hL : 0 < fast p.1.2 i)
    (h : 0 < (1 - secularGamma p.1 i / (2 * fast p.1.2 i)) / fast p.1.2 i) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      Real.sqrt ((1 - secularGamma p.1 i / (2 * fast p.1.2 i)) / fast p.1.2 i)) p := by
  refine ContDiffAt.sqrt ?_ h.ne'
  exact (contDiffAt_const.sub (((sbSmooth_cd_gamma i).contDiffAt).div
    (contDiffAt_const.mul (sbSmooth_cd_fast i).contDiffAt) (by positivity))).div
    (sbSmooth_cd_fast i).contDiffAt hL.ne'


private theorem sbSmooth_gamma_nonneg (w : Phase (2+2)) (i : Fin 2) : 0 ≤ secularGamma w i := by
  unfold secularGamma oscillatorAction; positivity

/-- Local radicand margin of step `sb-S-1`, consumed by `sb-sm-2`. -/
private theorem sbSmooth_radicand_margin {w : Phase (2+2)} (i : Fin 2)
    (h : 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) :
    (99/100 : ℝ) < 1 - secularGamma w i / (2 * fast w.2 i) ∧
      99 / (100 * fast w.2 i) <
        (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i := by
  obtain ⟨hL, hg⟩ := h
  have g0 := sbSmooth_gamma_nonneg w i
  have h2 : secularGamma w i / (2 * fast w.2 i) < 1/100 := by
    rw [div_lt_iff₀ (by positivity)]; linarith
  refine ⟨by linarith, ?_⟩
  rw [show 99 / (100 * fast w.2 i) = (99/100) / fast w.2 i by field_simp]
  exact div_lt_div_of_pos_right (by linarith) hL

private theorem sbSmooth_reg {w : Phase (2+2)} (i : Fin 2)
    (h : 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i) :
    0 < (1 - secularGamma w i / (2 * fast w.2 i)) / fast w.2 i ∧ 0 < secularRoot w i := by
  obtain ⟨hL, hg⟩ := h
  have g0 := sbSmooth_gamma_nonneg w i
  have hm := (sbSmooth_radicand_margin i ⟨hL, hg⟩).1
  have : secularGamma w i / fast w.2 i < 1/50 := by rw [div_lt_iff₀ hL]; linarith
  refine ⟨div_pos (by linarith) hL, ?_⟩
  unfold secularRoot; linarith

private theorem sbSmooth_cd_unit (k : Fin 2) :
    ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => orbitalUnit (p.2 i) k := by
  have := sbSmooth_cd_F i
  fin_cases k <;> simp [orbitalUnit] <;> fun_prop

variable (hw : 0 < fast p.1.2 i ∧ 50 * secularGamma p.1 i < fast p.1.2 i)
include hw

private theorem sbSmooth_cd_ecc (k : Fin 2) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) => secularEccVector p.1 i k) p := by
  fin_cases k
  · simpa [secularEccVector] using ((sbSmooth_cd_scale i hw.1 (sbSmooth_reg i hw).1).mul
      (sbSmooth_cd_slow1 i).contDiffAt)
  · simpa [secularEccVector] using ((sbSmooth_cd_scale i hw.1 (sbSmooth_reg i hw).1).mul
      (sbSmooth_cd_slow2 i).contDiffAt)


private theorem sbSmooth_cd_dot :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      planeDot (secularEccVector p.1 i) (orbitalUnit (p.2 i))) p := by
  simp only [planeDot, Fin.sum_univ_two]
  exact ((sbSmooth_cd_ecc i hw 0).mul (sbSmooth_cd_unit i 0).contDiffAt).add
    ((sbSmooth_cd_ecc i hw 1).mul (sbSmooth_cd_unit i 1).contDiffAt)

private theorem sbSmooth_cd_jac :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      longitudeJacobian p.1 i (p.2 i)) p :=
  contDiffAt_const.sub (sbSmooth_cd_dot i hw)

private theorem sbSmooth_cd_pos (k : Fin 2) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      ellipsePosition m p.1 i (p.2 i) k) p := by
  have hr := sbSmooth_cd_root i hw.1
  have h1 : (1 + secularRoot p.1 i) ≠ 0 := by linarith [(sbSmooth_reg i hw).2]
  have haxis : ContDiff ℝ ∞ fun p : Phase (2+2) × (Fin 2 → ℝ) => secularAxis m p.1 i := by
    unfold secularAxis
    have := sbSmooth_cd_fast i
    fun_prop
  simp only [ellipsePosition, Pi.smul_apply, Pi.add_apply, Pi.sub_apply, smul_eq_mul]
  exact haxis.contDiffAt.mul (((hr.mul (sbSmooth_cd_unit i k).contDiffAt).sub
    (sbSmooth_cd_ecc i hw k)).add
    (((sbSmooth_cd_dot i hw).div (contDiffAt_const.add hr) h1).mul (sbSmooth_cd_ecc i hw k)))


private theorem sbSmooth_cd_mom (hj : 0 < longitudeJacobian p.1 i (p.2 i)) (k : Fin 2) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      ellipseMomentum m p.1 i (p.2 i) k) p := by
  have hr := sbSmooth_cd_root i hw.1
  have h1 : (1 + secularRoot p.1 i) ≠ 0 := by linarith [(sbSmooth_reg i hw).2]
  have hden : ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      fast p.1.2 i * longitudeJacobian p.1 i (p.2 i)) p :=
    (sbSmooth_cd_fast i).contDiffAt.mul (sbSmooth_cd_jac i hw)
  have hden0 : fast p.1.2 i * longitudeJacobian p.1 i (p.2 i) ≠ 0 := (mul_pos hw.1 hj).ne'
  have hc := sbSmooth_cd_unit i
  have hv := sbSmooth_cd_ecc i hw
  have hco : ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      planeDot (secularEccVector p.1 i) (orbitalUnit (p.2 i)) / (1 + secularRoot p.1 i)) p :=
    (sbSmooth_cd_dot i hw).div (contDiffAt_const.add hr) h1
  have hs := (contDiffAt_const (c := m i ^ 2)).div hden hden0
  simp only [ellipseMomentum, Pi.smul_apply, Pi.sub_apply, smul_eq_mul]
  refine hs.mul ?_
  fin_cases k
  · simp only [quarterTurn]
    simpa using ((hc 1).contDiffAt.neg.sub (hco.mul (hv 1).neg))
  · simp only [quarterTurn]
    simpa using (((hc 0).contDiffAt).sub (hco.mul (hv 0)))

end Ellipse

private theorem sbSmooth_cd_phase (m : Fin 2 → ℝ) {p : Phase (2+2) × (Fin 2 → ℝ)}
    (hw : ∀ i, 0 < fast p.1.2 i ∧ 50 * secularGamma p.1 i < fast p.1.2 i)
    (hj : ∀ i, 0 < longitudeJacobian p.1 i (p.2 i)) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) => ellipsePhase m p.1 p.2) p := by
  refine ContDiffAt.prodMk (contDiffAt_pi.2 fun k => ?_) (contDiffAt_pi.2 fun k => ?_)
  · exact sbSmooth_cd_pos (m := m) (finProdFinEquiv.symm k).1 (hw _) (finProdFinEquiv.symm k).2
  · exact sbSmooth_cd_mom (m := m) (finProdFinEquiv.symm k).1 (hw _) (hj _)
      (finProdFinEquiv.symm k).2

def explicitSecularIntegrand (m : Fin 2 → ℝ) (mu : ℝ)
    (w : Phase (2+2)) (F : Fin 2 → ℝ) : ℝ :=
  movingHamiltonian 1 1 m mu (ellipsePhase m w F) * ∏ i, longitudeJacobian w i (F i)

private theorem sbSmooth_fast_assemble_snd {a b : ℕ} (I phi : Fin a → ℝ) (p q : Fin b → ℝ) :
    fast (assemble I phi p q).2 = I := by
  funext i; simp [fast, assemble]

private theorem sbSmooth_slow_assemble_snd {a b : ℕ} (I phi : Fin a → ℝ) (p q : Fin b → ℝ) :
    slow (assemble I phi p q).2 = p := by
  funext i; simp [slow, assemble]

private theorem sbSmooth_fast_assemble_fst {a b : ℕ} (I phi : Fin a → ℝ) (p q : Fin b → ℝ) :
    fast (assemble I phi p q).1 = phi := by
  funext i; simp [fast, assemble]

private theorem sbSmooth_slow_assemble_fst {a b : ℕ} (I phi : Fin a → ℝ) (p q : Fin b → ℝ) :
    slow (assemble I phi p q).1 = q := by
  funext i; simp [slow, assemble]

theorem secular_integrand_identity (m : Fin 2 → ℝ) (mu : ℝ)
    (w : Phase (2+2)) (F : Fin 2 → ℝ) :
    secularIntegrand m mu (assemble (fast w.2) F (slow w.2) (slow w.1)) =
      explicitSecularIntegrand m mu w F := by
  simp only [explicitSecularIntegrand, secularIntegrand, ellipsePhase, ellipsePosition,
    ellipseMomentum, longitudeJacobian, secularEccVector, secularRoot, secularGamma,
    secularAxis, sbSmooth_fast_assemble_snd, sbSmooth_slow_assemble_snd,
    sbSmooth_fast_assemble_fst, sbSmooth_slow_assemble_fst]

private theorem sbSmooth_hm (saturn : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ∀ i, 0 < jupiterSaturnWeights saturn i := by
  intro i
  fin_cases i
  · simp [jupiterSaturnWeights]
  · have := hs.1
    simp [jupiterSaturnWeights]; linarith

private theorem sbSmooth_contDiffAt (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100))
    {p : Phase (2+2) × (Fin 2 → ℝ)} (hp : p ∈ sb_sdef saturn ×ˢ (univ : Set (Fin 2 → ℝ))) :
    ContDiffAt ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu p.1 p.2) p := by
  obtain ⟨hS, -⟩ := hp
  have hw : ∀ i, 0 < fast p.1.2 i ∧ 50 * secularGamma p.1 i < fast p.1.2 i := hS.1
  obtain ⟨-, hs2⟩ := sb_s saturn hs
  obtain ⟨hj, hnc⟩ := hs2 p.1 hS p.2
  have hj' : ∀ i, 0 < longitudeJacobian p.1 i (p.2 i) := fun i => lt_trans (by norm_num) (hj i).2.2
  have hph := sbSmooth_cd_phase (jupiterSaturnWeights saturn) hw hj'
  have hmv := ContDiffAt.comp (g := movingHamiltonian 1 1 (jupiterSaturnWeights saturn) mu) p
    (sbSmooth_cd_moving _ mu hnc) hph
  unfold explicitSecularIntegrand
  simp only [Fin.prod_univ_two]
  exact hmv.mul ((sbSmooth_cd_jac 0 (hw 0)).mul (sbSmooth_cd_jac 1 (hw 1)))

private theorem sbSmooth_unit_add (x : ℝ) : orbitalUnit (x + 2 * Real.pi) = orbitalUnit x := by
  simp [orbitalUnit, Real.cos_add_two_pi, Real.sin_add_two_pi]

private theorem sbSmooth_periodic (m : Fin 2 → ℝ) (w : Phase (2+2)) (F G : Fin 2 → ℝ)
    (i : Fin 2) (hG : G = F + Pi.single i (2 * Real.pi)) :
    (∀ j, ellipsePosition m w j (G j) = ellipsePosition m w j (F j)) ∧
    (∀ j, ellipseMomentum m w j (G j) = ellipseMomentum m w j (F j)) ∧
    (∀ j, longitudeJacobian w j (G j) = longitudeJacobian w j (F j)) := by
  have key : ∀ j, G j = F j ∨ G j = F j + 2 * Real.pi := by
    intro j
    by_cases h : j = i
    · subst h; right; simp [hG]
    · left; simp [hG, h]
  refine ⟨fun j => ?_, fun j => ?_, fun j => ?_⟩ <;> rcases key j with h | h <;> rw [h]
  · simp [ellipsePosition, sbSmooth_unit_add]
  · simp [ellipseMomentum, longitudeJacobian, sbSmooth_unit_add]
  · simp [longitudeJacobian, sbSmooth_unit_add]

theorem secular_integrand_smooth (saturn mu : ℝ)
    (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ContDiffOn ℝ ∞ (fun p : Phase (2+2) × (Fin 2 → ℝ) =>
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu p.1 p.2)
      (sb_sdef saturn ×ˢ univ) ∧
    ∀ w : Phase (2+2), ∀ F : Fin 2 → ℝ, ∀ i : Fin 2,
      explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w (F + Pi.single i (2*Real.pi)) =
        explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w F := by
  refine ⟨fun p hp => (sbSmooth_contDiffAt saturn mu hs hp).contDiffWithinAt, ?_⟩
  intro w F i
  obtain ⟨h1, h2, h3⟩ := sbSmooth_periodic (jupiterSaturnWeights saturn) w F _ i rfl
  have hph : ellipsePhase (jupiterSaturnWeights saturn) w (F + Pi.single i (2 * Real.pi)) =
      ellipsePhase (jupiterSaturnWeights saturn) w F := by
    simp only [ellipsePhase]
    congr 1
    · funext k; exact congrFun (h1 _) _
    · funext k; exact congrFun (h2 _) _
  unfold explicitSecularIntegrand
  rw [hph]
  congr 1
  exact Finset.prod_congr rfl fun j _ => h3 j

theorem sb_smooth_prop (saturn mu : ℝ) (hs : saturn ∈ Icc (29/100 : ℝ) (31/100)) :
    ContDiffOn ℝ ∞ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu) (sb_sdef saturn) ∧
    (∀ w ∈ sb_sdef saturn, SecularRegular (jupiterSaturnWeights saturn) mu w) ∧
    ∀ w : Phase (2+2), ∀ lam : Fin 2 → ℝ,
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu
        (assemble (fast w.2) lam (slow w.2) (slow w.1)) =
      exactSecularHamiltonian (jupiterSaturnWeights saturn) mu w := by
  obtain ⟨hopen, hgeo⟩ := sb_s saturn hs
  obtain ⟨hsm, -⟩ := secular_integrand_smooth saturn mu hs
  have hQ : IsCompact (Set.pi Set.univ (fun _ : Fin 2 => Set.Icc 0 (2 * Real.pi))) :=
    isCompact_univ_pi fun _ => isCompact_Icc
  have hH : ∀ w, exactSecularHamiltonian (jupiterSaturnWeights saturn) mu w =
      (2 * Real.pi) ^ (-((2 : ℕ) : ℤ)) *
        ∫ F in Set.pi Set.univ (fun _ : Fin 2 => Set.Icc 0 (2 * Real.pi)),
          explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w F := by
    intro w
    unfold exactSecularHamiltonian secularAverage
    simp only [secular_integrand_identity]
  have hcd : ContDiffOn ℝ ∞ (exactSecularHamiltonian (jupiterSaturnWeights saturn) mu)
      (sb_sdef saturn) := by
    rw [contDiffOn_infty] at hsm ⊢
    intro k
    have := secular_parametric_integral (U := sb_sdef saturn) hopen hQ
      (g := explicitSecularIntegrand (jupiterSaturnWeights saturn) mu) k (hsm k)
    exact (contDiffOn_const.mul this).congr fun w _ => hH w
  refine ⟨hcd, ?_, ?_⟩
  · intro w hw
    have hS : ∀ i, 0 < fast w.2 i ∧ 50 * secularGamma w i < fast w.2 i := hw.1
    refine ⟨fun i => ⟨sbSmooth_hm saturn hs i, (hS i).1, sbSmooth_gamma_nonneg w i, ?_⟩,
      fun F => ⟨fun i => lt_trans (by norm_num) ((hgeo w hw F).1 i).2.2, (hgeo w hw F).2⟩,
      ?_, (hcd.contDiffAt (hopen.mem_nhds hw)).differentiableAt (by simp)⟩
    · have := sbSmooth_gamma_nonneg w i
      linarith [(hS i).2, (hS i).1]
    · have hfun : (fun F : Fin 2 → ℝ =>
          secularIntegrand (jupiterSaturnWeights saturn) mu
            (assemble (fast w.2) F (slow w.2) (slow w.1))) =
          fun F => explicitSecularIntegrand (jupiterSaturnWeights saturn) mu w F :=
        funext fun F => secular_integrand_identity _ _ w F
      rw [hfun]
      refine ContinuousOn.integrableOn_compact hQ fun F _ => ?_
      exact (ContinuousAt.comp (f := fun F : Fin 2 → ℝ => (w, F))
        (sbSmooth_contDiffAt saturn mu hs ⟨hw, mem_univ F⟩).continuousAt
        (by fun_prop)).continuousWithinAt
  · intro w lam
    unfold exactSecularHamiltonian
    simp only [sbSmooth_fast_assemble_snd, sbSmooth_slow_assemble_snd,
      sbSmooth_slow_assemble_fst]

end KAM.Planetary

end
