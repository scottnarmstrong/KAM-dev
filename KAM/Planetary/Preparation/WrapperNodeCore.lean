/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.PreparedBasic

/-!
# Literal-carrier domain chain and Hamiltonian identity (GAP-WR, `stepP:p11:wr-chain`)

The domain chain and the identity `H_fix ∘ chart ∘ ... = ε (N + P)` of `PreparedBasic`, with the
rescaled-domain membership as a hypothesis instead of membership in the complex prepared domain.
This lets them hold on the literal carrier `|r| < 2`, `|ρ'| < π/2` of the source.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter
namespace KAM.Planetary

section Chain

variable {n : ℕ} {C : P11SecularData n} {Fast : P11FastData n} {A : P11SlowData n} {nu eps : ℝ}

/-- The Hamiltonian identity `H_fix ∘ chart ∘ Θ̂ ∘ Ψ₂ ∘ A_ε = ε (h₀ + g₂ + f₃) ∘ A_ε / ε`,
for a real point whose rescaling lies in the slow half-box. -/
theorem p11_wr_ham_core {D : P11Physical n} (hC : P11SecularSpec D C)
    (heps : 0 < eps) (hpe : Real.pi*eps ≤ p11s2 C nu eps) (hsm : 64*eps < C.rz^2)
    (Hfix : Phase (n*2) → ℝ)
    (hchart : ∀ w : Phase (n+n), KAM.realInclusion₂ (n+n) w ∈
      p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz →
      Hfix (C.chart w) = (p11WorkingH C eps (KAM.realInclusion₂ (n+n) w)).re)
    (hFreal : ∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈
      p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2) → ∀ i,
      ((Fast.map (KAM.realInclusion₂ (n+n) z)).1 i).im = 0 ∧
      ((Fast.map (KAM.realInclusion₂ (n+n) z)).2 i).im = 0)
    (hFmaps : MapsTo Fast.map (p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2))
      (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz))
    (hPsireal : ∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈
      KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) → ∀ i,
      ((A.Psi (KAM.realInclusion₂ (n+n) z)).1 i).im = 0 ∧
      ((A.Psi (KAM.realInclusion₂ (n+n) z)).2 i).im = 0)
    (hPsimaps : MapsTo A.Psi (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2))
      (KAM.complexStrip (n+n) (C.sigma/12) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps)))
    (hf2 : ∀ z ∈ KAM.complexStrip (n+n) (C.sigma/12) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps),
      A.h0 z.2 + A.f2 z = p11WorkingH C eps (Fast.map (p11PolarC z)))
    (hid : ∀ z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2),
      A.h0 (A.Psi z).2 + A.f2 (A.Psi z) = A.h0 z.2 + A.g2 z.2 + A.f3 z)
    {z : Phase (n+n)}
    (hydom : p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z) ∈
      KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) :
    Hfix (C.chart ((fun i => ((Fast.map (p11PolarC (A.Psi
        (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))).1 i).re),
       fun i => ((Fast.map (p11PolarC (A.Psi
        (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))))).2 i).re)) =
      eps*((A.h0 (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z)).2 +
        A.g2 (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z)).2)/(eps : ℂ) +
        A.f3 (p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z))/(eps : ℂ)).re := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hs2pos : 0 < p11s2 C nu eps := lt_of_lt_of_le (by positivity) hpe
  have hs2le : p11s2 C nu eps ≤ p11s1 C eps/4 := min_le_left _ _
  have hs1rC : p11s1 C eps ≤ C.rC := min_le_left _ _
  set y := p11Rescale C.J0 eps (KAM.realInclusion₂ (n+n) z) with hy
  have hyreal : y = KAM.realInclusion₂ (n+n) (p11RescaleReal C.J0 eps z) :=
    p11Rescale_real _ _ _
  have hPsi := hPsimaps hydom
  have hre := hPsireal (p11RescaleReal C.J0 eps z) (hyreal ▸ hydom)
  rw [← hyreal] at hre
  set Pr : Phase (n+n) := ((fun i => ((A.Psi y).1 i).re), fun i => ((A.Psi y).2 i).re) with hPr
  have hPsiR : A.Psi y = KAM.realInclusion₂ (n+n) Pr := by
    refine Prod.ext (funext fun i => Complex.ext (by simp [hPr]) (by simp [hPr, (hre i).1]))
      (funext fun i => Complex.ext (by simp [hPr]) (by simp [hPr, (hre i).2]))
  have hpos : ∀ i : Fin n, 0 < Pr.2 (Fin.natAdd n i) := fun i => by
    have := p11_slowBox_re_pos (nu := nu) hPsi.2 i
    simp only [hPr]
    nlinarith [Real.pi_pos]
  have hbox := p11SlowBox_mem (C := C) (nu := nu) hs2pos heps (I := (A.Psi y).2) hPsi.2
  have hmem : p11PolarC (A.Psi y) ∈
      p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2) := by
    refine (p11_polarC_mem hC heps hsm (z := A.Psi y) ?_ ?_ ?_).2.2
    · intro i
      exact (hPsi.1 i).trans (by linarith)
    · exact lt_of_lt_of_le hbox.1 (by linarith)
    · have h1 := hbox.2
      have h2 : ‖(fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ ≤ 2*Real.pi*eps :=
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
          simp [abs_of_pos heps, abs_of_pos Real.pi_pos]
      have h3 := norm_le_norm_add_norm_sub' (p11SlowR (A.Psi y).2)
        (fun _ : Fin n => (2*Real.pi*eps : ℂ))
      calc ‖p11SlowR (A.Psi y).2‖ ≤ ‖(fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ +
            ‖p11SlowR (A.Psi y).2 - fun _ : Fin n => (2*Real.pi*eps : ℂ)‖ := h3
        _ < 3*Real.pi*eps := by
          have := h1
          change ‖(fun i : Fin n => (A.Psi y).2 (Fin.natAdd n i)) -
            (fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ < _ at this
          show _ + ‖(fun i : Fin n => (A.Psi y).2 (Fin.natAdd n i)) -
            (fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ < _
          linarith
  have hpolar : p11PolarC (A.Psi y) = KAM.realInclusion₂ (n+n) (p11PolarR Pr) := by
    rw [hPsiR]; exact p11_polarC_real hpos
  have hWreal : ∀ i, ((Fast.map (p11PolarC (A.Psi y))).1 i).im = 0 ∧
      ((Fast.map (p11PolarC (A.Psi y))).2 i).im = 0 := by
    rw [hpolar]; exact hFreal (p11PolarR Pr) (hpolar ▸ hmem)
  have hW0eq : KAM.realInclusion₂ (n+n) ((fun i => ((Fast.map (p11PolarC (A.Psi y))).1 i).re),
      fun i => ((Fast.map (p11PolarC (A.Psi y))).2 i).re) = Fast.map (p11PolarC (A.Psi y)) :=
    Prod.ext (funext fun i => Complex.ext (by simp) (by simp [(hWreal i).1]))
      (funext fun i => Complex.ext (by simp) (by simp [(hWreal i).2]))
  have hWdom : Fast.map (p11PolarC (A.Psi y)) ∈
      p11WorkingDom n C.J0 (2*C.sigma) (2*C.rC) C.rz :=
    p11WorkingDom_mono (by linarith) (by linarith) le_rfl (hFmaps hmem)
  show Hfix (C.chart ((fun i => ((Fast.map (p11PolarC (A.Psi y))).1 i).re),
      fun i => ((Fast.map (p11PolarC (A.Psi y))).2 i).re)) = _
  rw [hchart _ (by rw [hW0eq]; exact hWdom), hW0eq, ← hf2 _ hPsi, hid y hydom]
  show _ = eps * ((A.h0 y.2 + A.g2 y.2)/(eps : ℂ) + A.f3 y/(eps : ℂ)).re
  rw [← add_div, Complex.div_ofReal_re]
  field_simp


/-- The complex domain chain of `stepP:p11:pr-basic`, for a point whose rescaling lies in the
slow half-box. -/
theorem p11_wr_chain_dom {D : P11Physical n} (hC : P11SecularSpec D C) (heps : 0 < eps)
    (hpe : Real.pi*eps ≤ p11s2 C nu eps) (hsm : 256*eps < C.rz^2)
    (hFmaps : MapsTo Fast.map (p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2))
      (p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz))
    (hPsimaps : MapsTo A.Psi (KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2))
      (KAM.complexStrip (n+n) (C.sigma/12) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps)))
    {z : P11Phase (n+n)}
    (hydom : p11Rescale C.J0 eps z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)) :
    p11Rescale C.J0 eps z ∈ KAM.complexStrip (n+n) (C.sigma/12/6) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2) ∧
      A.Psi (p11Rescale C.J0 eps z) ∈ KAM.complexStrip (n+n) (C.sigma/12) ×ˢ
        p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps) ∧
      p11PolarC (A.Psi (p11Rescale C.J0 eps z)) ∈
        p11WorkingDom n C.J0 (C.sigma/6) (p11s2 C nu eps) (C.rz/4) ∧
      p11PolarC (A.Psi (p11Rescale C.J0 eps z)) ∈
        p11WorkingDom n C.J0 (C.sigma/6) (p11s1 C eps/2) (C.rz/2) ∧
      Fast.map (p11PolarC (A.Psi (p11Rescale C.J0 eps z))) ∈
        p11WorkingDom n C.J0 C.sigma (p11s1 C eps) C.rz := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, hrC1, hσ0, hσ1, hrz0, hrz1, hMF⟩ := fast_consts hC
  have hs2pos : 0 < p11s2 C nu eps := lt_of_lt_of_le (by positivity) hpe
  have hs2le : p11s2 C nu eps ≤ p11s1 C eps/4 := min_le_left _ _
  have hs1rC : p11s1 C eps ≤ C.rC := min_le_left _ _
  have hs1pos : 0 < p11s1 C eps := by linarith
  have hPsi := hPsimaps hydom
  have hbox := p11SlowBox_mem (C := C) (nu := nu) hs2pos heps (I := (A.Psi _).2) hPsi.2
  have hsm' : 64*eps < C.rz^2 := by nlinarith
  have hmem := p11_polarC_mem hC heps hsm' (z := A.Psi (p11Rescale C.J0 eps z)) (by
      intro i
      exact (hPsi.1 i).trans (by linarith)) (lt_of_lt_of_le hbox.1 (by linarith)) (by
      have h1 := hbox.2
      have h2 : ‖(fun _ : Fin n => (2*Real.pi*eps : ℂ))‖ ≤ 2*Real.pi*eps :=
        (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => by
          simp [abs_of_pos heps, abs_of_pos Real.pi_pos]
      have h3 := norm_le_norm_add_norm_sub' (p11SlowR (A.Psi (p11Rescale C.J0 eps z)).2)
        (fun _ : Fin n => (2*Real.pi*eps : ℂ))
      have h4 : ‖p11SlowR (A.Psi (p11Rescale C.J0 eps z)).2 -
          fun _ : Fin n => (2*Real.pi*eps : ℂ)‖ < Real.pi*eps := h1
      linarith)
  have hPr : ‖p11PolPt (A.Psi (p11Rescale C.J0 eps z))‖ < C.rz/4 := by
    refine lt_of_le_of_lt hmem.1 ?_
    have : (4 * Real.sqrt eps) ^ 2 < (C.rz / 4) ^ 2 := by
      nlinarith [Real.sq_sqrt heps.le]
    exact lt_of_pow_lt_pow_left₀ 2 (by positivity) this
  refine ⟨hydom, hPsi, ⟨hmem.2.2.1, ?_, ?_, ?_⟩, hmem.2.2, hFmaps hmem.2.2⟩
  · have h : (fun i : Fin n => (p11PolarC (A.Psi (p11Rescale C.J0 eps z))).2 (Fin.castAdd n i)) =
        p11SlowJ (A.Psi (p11Rescale C.J0 eps z)).2 := by
      funext i; simp [p11PolarC, p11SlowJ]
    show ‖(fun i : Fin n =>
      (p11PolarC (A.Psi (p11Rescale C.J0 eps z))).2 (Fin.castAdd n i)) - _‖ < _
    rw [h]; exact hbox.1
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_left _ _ |>.trans' le_rfl) hPr
  · exact lt_of_le_of_lt (by
      rw [Prod.norm_def]; exact le_max_right _ _ |>.trans' le_rfl) hPr


end Chain

end KAM.Planetary

end
