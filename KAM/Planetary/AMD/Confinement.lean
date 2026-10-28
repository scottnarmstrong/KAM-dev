/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Frozen.Planetary.Defs.AMDBoxAdmissible
public import KAM.Frozen.Planetary.Defs.StoppedActionBound
public import KAM.Frozen.Planetary.Defs.MovingUniqueOn
public import KAM.Planetary.AMD.Setting
public import KAM.Planetary.AMD.Closure
public import KAM.Planetary.AMD.Geometry
public import KAM.Planetary.AMD.MovingODE
public import KAM.Planetary.AMD.AngularMomentum
public import KAM.Planetary.AMD.ConfinementExit
public import KAM.Planetary.Newtonian.Reconstruction
public import KAM.ODE.Maximal
public import KAM.ODE.Continuation
public import KAM.ODE.Uniqueness
public import KAM.ODE.Lipschitz

/-!
# AMD confinement (P14, package A6)

Blueprint P, Part 14 (`bpP:p14:amd`).  Under the stopped action bound, the maximal solution of
the moving-frame system through an inner datum stays in the collar region on `[-T, T]`
(`amd_collar_of_solution`, by the first-exit argument, the stopped bound, angular-momentum
conservation and `amd_closure`), hence in the compact geometric set; `amd` then assembles the
frozen conclusion via `gen_confinement` and the reconstruction of Newtonian solutions.
-/

@[expose] public noncomputable section

open Set Filter Topology

namespace KAM.Planetary

variable {n : ℕ}

theorem isMovingSolutionOn_mono_of_subset {m : Fin n → ℝ} {mu : ℝ} {J J' : Set ℝ}
    {z : ℝ → Phase (n * 2)} (hz : IsMovingSolutionOn m mu J z) (h : J' ⊆ J) :
    IsMovingSolutionOn m mu J' z :=
  ⟨fun t ht => hz.1 t (h ht), fun t ht => hz.2 t (h ht)⟩

/-- The inner datum lies in the collar region. -/
theorem amd_inner_mem_collar (B : AMDBox n) {delta : ℝ} (hd : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    {z0 : Phase (n * 2)} (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD) :
    z0 ∈ amdCollar B delta := by
  obtain ⟨hp, hact, hamd⟩ := hz0
  have hnd : 0 ≤ (n : ℝ) * delta := by positivity
  refine ⟨⟨hp, fun i => ⟨?_, ?_⟩, ?_⟩, fun i => ⟨?_, ?_⟩, ?_⟩
  · linarith [(hmargin i).1, (hact i).1]
  · linarith [(hmargin i).2, (hact i).2]
  · linarith
  · linarith [(hmargin i).1, (hact i).1]
  · linarith [(hmargin i).2, (hact i).2]
  · linarith

/-- On an interval containing `0` and inside `[-T, T]`, a solution through `z0` that stays in the
outer region stays in the collar region (stopped bound plus angular momentum). -/
theorem amd_collar_at (B : AMDBox n) {mu T delta : ℝ}
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    {z0 : Phase (n * 2)} (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) {a b : ℝ} (ha : a ≤ 0) (hb : 0 ≤ b) (hab : a < b)
    (hT : Icc a b ⊆ Icc (-T) T) {y : ℝ → Phase (n * 2)} (hy0 : y 0 = z0)
    (hy : IsMovingSolutionOn B.mass mu (Icc a b) y) (hout : ∀ t ∈ Icc a b, y t ∈ amdOuter B) :
    ∀ t ∈ Icc a b, y t ∈ amdCollar B delta := by
  have hdrift := hstop a b y ha hb hab hy0 hy hout
  have h0 : (0 : ℝ) ∈ Icc a b := ⟨ha, hb⟩
  intro t ht
  have hd : ∀ i, |keplerAction B.mass (y t) i - keplerAction B.mass z0 i| ≤ delta :=
    hdrift t ⟨ht, hT ht⟩
  have hmom : totalMomentum (y t) = totalMomentum z0 := by
    rw [← hy0]; exact ang_mom ordConnected_Icc hy 0 h0 t ht
  refine ⟨hout t ht, fun i => ?_, ?_⟩
  · have := abs_le.1 (hd i)
    have h1 := hz0.2.1 i
    have h2 := hmargin i
    constructor <;> linarith [this.1, this.2, h1.1, h1.2, h2.1, h2.2]
  · have hsum : ∑ i, keplerAction B.mass (y t) i ≤
        ∑ i, keplerAction B.mass z0 i + (n : ℝ) * delta := by
      have : ∑ i, (keplerAction B.mass (y t) i - keplerAction B.mass z0 i) ≤ ∑ _i : Fin n, delta :=
        Finset.sum_le_sum fun i _ => (abs_le.1 (hd i)).2
      simp only [Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
        nsmul_eq_mul] at this
      linarith
    have := hz0.2.2
    have e : physicalAMD B.mass (y t) = (∑ i, keplerAction B.mass (y t) i) - totalMomentum z0 := by
      rw [physicalAMD, hmom]
    have e0 : physicalAMD B.mass z0 = (∑ i, keplerAction B.mass z0 i) - totalMomentum z0 := rfl
    linarith

/-- First-exit argument: a moving solution on `J ⊆ [-T, T]` through an inner datum stays in the
collar region. -/
theorem amd_collar_of_solution (B : AMDBox n) (hB : B.Admissible) {mu T delta : ℝ}
    (hd : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    {z0 : Phase (n * 2)} (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) {J : Set ℝ} (hJ : J.OrdConnected)
    (h0 : (0 : ℝ) ∈ J) (hJT : J ⊆ Icc (-T) T) {y : ℝ → Phase (n * 2)} (hy0 : y 0 = z0)
    (hy : IsMovingSolutionOn B.mass mu J y) :
    ∀ t ∈ J, y t ∈ amdCollar B delta := by
  obtain ⟨hopen, hclosed⟩ := amd_closure B hB hd hmargin hAMD
  have hc0 : z0 ∈ amdCollar B delta := amd_inner_mem_collar B hd hmargin hAMD hz0
  have hcont : ContinuousOn y J := fun t ht => (hy.1 t ht).2.2.continuousAt.continuousWithinAt
  have hN : ∀ t ∈ J, y t ∈ {w : Phase (n * 2) | ∀ i, 0 < planeLength (bodyVector w.1 i)} :=
    fun t ht i => (hy.2 t ht).1 i
  have hcl : ∀ (x : ℕ → Phase (n * 2)) (xs : Phase (n * 2)), (∀ k, x k ∈ amdCollar B delta) →
      Tendsto x atTop (𝓝 xs) → xs ∈ {w : Phase (n * 2) | ∀ i, 0 < planeLength (bodyVector w.1 i)} →
      xs ∈ amdCollar B delta := fun x xs hx hl hn => hclosed x xs hx hl hn
  have hy0V : y 0 ∈ amdOuter B := by rw [hy0]; exact (hc0).1
  have hfwd := amd_exit_forward hJ h0 hcont hopen (fun w hw => hw.1) hcl hN hy0V
    (fun s hs hs0 hV => by
      rcases hs0.eq_or_lt with rfl | hpos
      · rw [hy0]; exact hc0
      · have hsub : Icc 0 s ⊆ J := hJ.out h0 hs
        exact amd_collar_at B hmargin hz0 hstop le_rfl hpos.le hpos
          (fun t ht => hJT (hsub ht)) hy0 (isMovingSolutionOn_mono_of_subset hy hsub)
          (fun t ht => hV t ht.1 ht.2) s ⟨hpos.le, le_rfl⟩)
  have hbwd := amd_exit_backward hJ h0 hcont hopen (fun w hw => hw.1) hcl hN hy0V
    (fun s hs hs0 hV => by
      rcases hs0.eq_or_lt with hneg | hneg
      · have : s = 0 := hneg
        subst this
        rw [hy0]; exact hc0
      · have hsub : Icc s 0 ⊆ J := hJ.out hs h0
        exact amd_collar_at B hmargin hz0 hstop hneg.le le_rfl hneg
          (fun t ht => hJT (hsub ht)) hy0 (isMovingSolutionOn_mono_of_subset hy hsub)
          (fun t ht => hV t ht.1 ht.2) s ⟨le_rfl, hneg.le⟩)
  intro t ht
  rcases le_total 0 t with h | h
  · exact hfwd t ht h
  · exact hbwd t ht h

/-- `bpP:p14:amd`: the library assembly of the confinement theorem (exact frozen type). -/
theorem amd {n : ℕ} (hn : 2 ≤ n) (B : AMDBox n) (hB : B.Admissible)
    (mu T delta : ℝ) (hmu : 0 < mu) (hT : 0 < T) (hdelta : 0 < delta)
    (hmargin : ∀ i, B.lower i + 2 * delta < B.innerLower i ∧
      B.innerUpper i + 2 * delta < B.upper i)
    (hAMD : B.initialAMD + 2 * (n : ℝ) * delta < B.outerAMD)
    (z0 : Phase (n * 2))
    (hz0 : z0 ∈ LowAMDRegion B.mass B.innerLower B.innerUpper B.initialAMD)
    (hstop : StoppedActionBound B mu T delta z0) :
    ∃ z : ℝ → Phase (n * 2), z 0 = z0 ∧ (IsMovingSolutionOn B.mass mu (Set.Icc (-T) T) z ∧
      MovingUniqueOn B.mass mu (Set.Icc (-T) T) z ∧
      IsNewtonSolutionOn (actualMasses 1 B.mass mu) (Set.Icc (-T) T)
        (fun t => barycentricPositions 1 B.mass mu (z t).1)
        (fun t => barycentricVelocities 1 B.mass mu (z t).2) ∧
      ∀ t ∈ (Set.Icc (-T) T),
        z t ∈ LowAMDRegion B.mass B.lower B.upper B.outerAMD ∧
        totalMomentum (z t) = totalMomentum (z 0) ∧
        (∀ i, planeLength (keplerEccVector B.mass (z t) i) < B.ecc ∧
          B.distance ≤ planeLength (bodyVector (z t).1 i) ∧
          planeLength (bodyVector (z t).1 i) ≤ B.radius) ∧
        PairBounds B.distance (2 * B.radius) (barycentricPositions 1 B.mass mu (z t).1)) ∧
      ∀ t ∈ Set.Icc (-T) T,
        physicalAMD B.mass (z t) ≤ B.initialAMD + (n : ℝ) * delta ∧
        ∀ i, |keplerAction B.mass (z t) i - keplerAction B.mass z0 i| ≤ delta := by
  have _hn := hn
  obtain ⟨hW, hF, hiff⟩ := moving_ode B.mass mu
  obtain ⟨hcomp, hcompW⟩ := amd_compact B hB
  obtain ⟨δ', M, L, hU, -, -⟩ := KAM.ODE.gen_uniform_compact hW hF hcomp hcompW
  have hz0W : z0 ∈ collisionFreeDomain n := by
    have := geometry B hB (amd_inner_mem_collar B hdelta hmargin hAMD hz0).1
    exact this.2.2.2.1
  have hconf : ∀ (J : Set ℝ) (y : ℝ → Phase (n * 2)), IsOpen J → J.OrdConnected →
      (0 : ℝ) ∈ J → y 0 = z0 →
      KAM.ODE.IsSolutionIn (KAM.hamiltonianVectorField (movingHamiltonian 1 1 B.mass mu))
        (collisionFreeDomain n) J y → ∀ t ∈ J, |t| ≤ T → y t ∈ amdCompact B := by
    intro J y _ hJ h0 hy0 hy t ht htT
    have hmov := (hiff J y).2 hy
    have hJ' : (J ∩ Icc (-T) T).OrdConnected := hJ.inter ordConnected_Icc
    have := amd_collar_of_solution B hB hdelta hmargin hAMD hz0 hstop hJ'
      ⟨h0, by constructor <;> linarith⟩ inter_subset_right hy0
      (isMovingSolutionOn_mono_of_subset hmov inter_subset_left) t ⟨ht, abs_le.1 htT⟩
    exact (geometry B hB this.1).2.2.1
  obtain ⟨Tm, Tp, z, hz, hTm, hTp, hsol, -, -⟩ :=
    KAM.ODE.gen_confinement hW hF hz0W hT hU hconf
  have hmov : IsMovingSolutionOn B.mass mu (Icc (-T) T) z := (hiff _ z).2 hsol
  have hJ : (Icc (-T) T).OrdConnected := ordConnected_Icc
  have h0 : (0 : ℝ) ∈ Icc (-T) T := ⟨by linarith, hT.le⟩
  have hcol := amd_collar_of_solution B hB hdelta hmargin hAMD hz0 hstop hJ h0 subset_rfl
    hz.init hmov
  refine ⟨z, hz.init, ⟨hmov, ?_, ?_, fun t ht => ?_⟩, fun t ht => ⟨(hcol t ht).2.2, fun i => ?_⟩⟩
  · intro U w hUo hUc h0U hw0 hwU t ht
    exact KAM.ODE.gen_uniqueness_inter hW hF (convex_iff_ordConnected.1 hUc) hJ
      (t₀ := 0) ⟨h0U, h0⟩ ((hiff U w).1 hwU) hsol hw0 ht
  · exact isNewtonSolutionOn_of_isMovingSolutionOn (fun i => (hB.1 i).1) hmu.le hmov
  · have hg := geometry B hB (hcol t ht).1
    exact ⟨(hcol t ht).1, ang_mom hJ hmov 0 h0 t ht, hg.2.2.2.2.1, hg.2.2.2.2.2 mu⟩
  · exact hstop (-T) T z (by linarith) hT.le (by linarith) hz.init hmov
      (fun t ht => (hcol t ht).1) t ⟨ht, ht⟩ i

end KAM.Planetary

end
