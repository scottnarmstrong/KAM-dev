/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.PGAssembly.KAMInputsF
public import KAM.Planetary.PGAssembly.ChartLoc

/-!
# P Part 5: the KAM hypothesis inputs, periodicity and reality (`bpP:p5:kam-hyp`)

Periodicity of `kamF` in every angle on the strip domain, and reality of `kamH` and `kamF` on the
real slice over the real neighbourhood of the action domain (via `oscillatorPolarComplex_real`,
the real trace of the averaging map and `ext_P_real`).
Design `docs/tracks/P/design/P45-LEAN-DESIGN.md`, package P5-KH.
-/

@[expose] public noncomputable section

open Set Metric Filter Topology

namespace KAM.Planetary

variable {a b : ℕ} {d : PGData a b} {r mu : ℝ}

theorem kh_single_castAdd_natAdd (k : Fin a) (k' : Fin b) :
    (Pi.single (Fin.castAdd b k) (1:ℂ) : Fin (a+b) → ℂ) (Fin.natAdd a k') = 0 := by
  refine Pi.single_eq_of_ne (fun hh => ?_) _
  have := congrArg Fin.val hh
  have := k.isLt
  simp at *
  omega

theorem kh_single_natAdd_castAdd (k : Fin b) (k' : Fin a) :
    (Pi.single (Fin.natAdd a k) (1:ℂ) : Fin (a+b) → ℂ) (Fin.castAdd b k') = 0 := by
  refine Pi.single_eq_of_ne (fun hh => ?_) _
  have := congrArg Fin.val hh
  have := k'.isLt
  simp at *
  omega

theorem kh_single_natAdd_natAdd (k k' : Fin b) :
    (Pi.single (Fin.natAdd a k) (1:ℂ) : Fin (a+b) → ℂ) (Fin.natAdd a k') =
      (Pi.single k (1:ℂ) : Fin b → ℂ) k' := by
  by_cases hk : k' = k
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro hh
    apply hk
    apply Fin.ext
    have := congrArg Fin.val hh
    simp at this
    omega

theorem kh_single_castAdd_castAdd (k k' : Fin a) :
    (Pi.single (Fin.castAdd b k) (1:ℂ) : Fin (a+b) → ℂ) (Fin.castAdd b k') =
      (Pi.single k (1:ℂ) : Fin a → ℂ) k' := by
  by_cases hk : k' = k
  · subst hk; simp
  · rw [Pi.single_eq_of_ne hk, Pi.single_eq_of_ne]
    intro hh
    apply hk
    apply Fin.ext
    have := congrArg Fin.val hh
    simpa using this

theorem kamPolarPt_add_slow (z : PGComplexPhase (a+b)) (k : Fin b) :
    kamPolarPt (z.1 + Pi.single (Fin.natAdd a k) 1, z.2) = kamPolarPt z := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun k' => ?_) (fun k' => ?_) i
    · rw [kamPolarPt_fst_fast, kamPolarPt_fst_fast]
      simp [kh_single_natAdd_castAdd]
    · rw [kamPolarPt_fst_slow, kamPolarPt_fst_slow]
      simp only [Pi.add_apply, kh_single_natAdd_natAdd]
      by_cases hk : k' = k
      · subst hk
        have : 2*(Real.pi:ℂ)*(z.1 (Fin.natAdd a k') + (Pi.single k' (1:ℂ) : Fin b → ℂ) k') =
            2*Real.pi*z.1 (Fin.natAdd a k') + 2*Real.pi := by simp; ring
        rw [this, Complex.sin_add_two_pi]
      · simp [Pi.single_eq_of_ne hk]
  · refine Fin.addCases (fun k' => ?_) (fun k' => ?_) i
    · rw [kamPolarPt_snd_fast, kamPolarPt_snd_fast]
    · rw [kamPolarPt_snd_slow, kamPolarPt_snd_slow]
      simp only [Pi.add_apply, kh_single_natAdd_natAdd]
      by_cases hk : k' = k
      · subst hk
        have : 2*(Real.pi:ℂ)*(z.1 (Fin.natAdd a k') + (Pi.single k' (1:ℂ) : Fin b → ℂ) k') =
            2*Real.pi*z.1 (Fin.natAdd a k') + 2*Real.pi := by simp; ring
        rw [this, Complex.cos_add_two_pi]
      · simp [Pi.single_eq_of_ne hk]

theorem kamPolarPt_add_fast (z : PGComplexPhase (a+b)) (k : Fin a) :
    kamPolarPt (z.1 + Pi.single (Fin.castAdd b k) 1, z.2) = kamPolarPt z +
      KAM.realInclusion₂ (a+b) (fastShift (Pi.single k (1:ℤ))) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun k' => ?_) (fun k' => ?_) i
    · rw [Prod.fst_add, Pi.add_apply, kamPolarPt_fst_fast, kamPolarPt_fst_fast]
      simp only [Pi.add_apply, kh_single_castAdd_castAdd, fastShift,
        KAM.realInclusion₂_apply, KAM.realInclusion_apply, Fin.append_left]
      by_cases hk : k' = k
      · subst hk; simp; ring
      · simp [Pi.single_eq_of_ne hk]
    · rw [Prod.fst_add, Pi.add_apply, kamPolarPt_fst_slow, kamPolarPt_fst_slow]
      simp [fastShift, kh_single_castAdd_natAdd]
  · refine Fin.addCases (fun k' => ?_) (fun k' => ?_) i
    · rw [Prod.snd_add, Pi.add_apply, kamPolarPt_snd_fast, kamPolarPt_snd_fast]
      simp [fastShift]
    · rw [Prod.snd_add, Pi.add_apply, kamPolarPt_snd_slow, kamPolarPt_snd_slow]
      simp [fastShift, kh_single_castAdd_natAdd]

theorem kamF_periodic (h : admissible d (pgRstar d) r mu) {z : PGComplexPhase (a+b)}
    (hz1 : z.1 ∈ KAM.complexStrip (a+b) (pgWidth d/(12*Real.pi)))
    (hz2 : z.2 ∈ KAM.actionNbhd (pgActionDomain d r mu) (params d r mu).rho) (j : Fin (a+b)) :
    kamF d r mu h (z.1 + Pi.single j 1, z.2) = kamF d r mu h z := by
  have hspec := kh_avg_spec h
  obtain ⟨hav, -⟩ := kamPolar_mem h hz1 hz2
  refine Fin.addCases (fun k => ?_) (fun k => ?_) j
  · have hP := hspec.2.2.2.2.2.2.2.1 (kamPolarPt z) hav (Pi.single k 1)
    have hext := hspec.2.2.1 hav
    have hper := (pgExtension d).periodic mu (mu_mem_Icc h) _ hext (Pi.single k 1)
    have e : kamPolarPt (z.1 + Pi.single (Fin.castAdd b k) 1, z.2) = kamPolarPt z +
        KAM.realInclusion₂ (a+b) (fastShift (Pi.single k (1:ℤ))) := kamPolarPt_add_fast z k
    have e2 : blockFast ((pgAvg d r mu h).Psi (kamPolarPt z) +
        KAM.realInclusion₂ (a+b) (fastShift (Pi.single k (1:ℤ)))).2 =
        blockFast ((pgAvg d r mu h).Psi (kamPolarPt z)).2 := by
      funext i; simp [blockFast, fastShift]
    show ((pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi
        (kamPolarPt (z.1 + Pi.single (Fin.castAdd b k) 1, z.2))).2) +
      mu*(pgExtension d).P mu ((pgAvg d r mu h).Psi
        (kamPolarPt (z.1 + Pi.single (Fin.castAdd b k) 1, z.2))))/(2*Real.pi) -
      kamH d mu z.2 = _
    rw [e, hP, e2, hper]
    rfl
  · rw [show kamF d r mu h (z.1 + Pi.single (Fin.natAdd a k) 1, z.2) =
      ((pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi
        (kamPolarPt (z.1 + Pi.single (Fin.natAdd a k) 1, z.2))).2) +
      mu*(pgExtension d).P mu ((pgAvg d r mu h).Psi
        (kamPolarPt (z.1 + Pi.single (Fin.natAdd a k) 1, z.2))))/(2*Real.pi) -
      kamH d mu z.2 from rfl, kamPolarPt_add_slow]
    rfl

/-! ### Reality -/

theorem jetPolynomial_realSlice (d : PGData a b) {mu : ℝ} (hmu : mu ∈ Icc 0 d.mu0)
    {J : Fin (a+b) → ℝ} (hJ : blockFast J ∈ d.V) :
    jetPolynomial d mu (KAM.realInclusion (a+b) J) =
      (secularPolynomial d.P0 d.Omega d.beta mu (blockFast J) (blockSlow J) : ℝ) := by
  have e1 : blockFast (KAM.realInclusion (a+b) J) = KAM.realInclusion a (blockFast J) := rfl
  have e2 : blockSlow (KAM.realInclusion (a+b) J) = KAM.realInclusion b (blockSlow J) := rfl
  simp only [jetPolynomial, e1, e2, jetP0_real d hmu hJ, jetOmega_real d hmu hJ,
    jetBeta_real d hmu hJ, secularPolynomial, KAM.realInclusion_apply]
  push_cast
  ring

theorem kh_real_fast (h : admissible d (pgRstar d) r mu) {J : Fin (a+b) → ℝ}
    (hJ : J ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    blockFast J ∈ d.V := by
  obtain ⟨hr1, -, -, hl1, hl12, -⟩ := kh_dyn h
  obtain ⟨y, hy, hd⟩ := hJ
  have hr0 : 0 < r := h.1
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  refine mem_of_dist_lt_innerCore (y := blockFast y) hy.1.1.1 hy.1.1.2 ?_
  have h1 : dist (blockFast J) (blockFast y) ≤ dist J y := by
    rw [dist_eq_norm, dist_eq_norm]; exact norm_blockFast_sub_le_real J y
  have h2 : r < Real.sqrt r := by
    rw [Real.lt_sqrt hr0.le]; nlinarith
  rw [hrho] at hd
  nlinarith

theorem kamH_real (h : admissible d (pgRstar d) r mu) {J : Fin (a+b) → ℝ}
    (hJ : J ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    ∃ x : ℝ, kamH d mu (KAM.realInclusion (a+b) J) = x := by
  have hf := kh_real_fast h hJ
  have hδ := (pgExtension d).delta_pos
  have hH0 := (pgExtension d).h0real (blockFast J)
    (realInclusion_mem_actionNbhd hδ (subset_closure hf))
  have hj := jetPolynomial_realSlice d (mu_mem_Icc h) hf
  refine ⟨(d.H0 (blockFast J) + mu*secularPolynomial d.P0 d.Omega d.beta mu (blockFast J)
    (blockSlow J))/(2*Real.pi), ?_⟩
  have e1 : blockFast (KAM.realInclusion (a+b) J) = KAM.realInclusion a (blockFast J) := rfl
  rw [kamH, complexIntegrable, e1, hH0, hj]
  push_cast
  rfl

theorem kamF_real (h : admissible d (pgRstar d) r mu) {z : Phase (a+b)}
    (hz : z.2 ∈ realNbhd (pgActionDomain d r mu) (params d r mu).rho) :
    (kamF d r mu h (KAM.realInclusion₂ (a+b) z)).im = 0 := by
  obtain ⟨hr1, -, -, hl1, hl12, hlr, -, -⟩ := kh_dyn h
  have hspec := kh_avg_spec h
  have hmu := mu_mem_Icc h
  have hr0 : 0 < r := h.1
  have hδ := (pgExtension d).delta_pos
  have hrho : (params d r mu).rho = (params d r mu).l1/2 := rfl
  have hz0 := hz
  obtain ⟨y, hy, hd⟩ := hz
  -- the slow actions
  have hslow : ∀ j, (params d r mu).l1/2 < blockSlow z.2 j ∧ blockSlow z.2 j < r^2 := by
    intro j
    have h1 : (params d r mu).l1 < blockSlow y j ∧ blockSlow y j < (params d r mu).l2top :=
      hy.2 j (mem_univ j)
    have hbs : blockSlow y j = y (Fin.natAdd a j) := rfl
    rw [hbs] at h1
    have h2 := (abs_lt.1 (lt_of_le_of_lt (norm_le_pi_norm (z.2 - y) (Fin.natAdd a j))
      (by rw [← dist_eq_norm]; exact hd))).1
    have h3 := (abs_lt.1 (lt_of_le_of_lt (norm_le_pi_norm (z.2 - y) (Fin.natAdd a j))
      (by rw [← dist_eq_norm]; exact hd))).2
    have h4 := params_l2top d r mu
    simp only [Pi.sub_apply] at h2 h3
    have h5 : y (Fin.natAdd a j) < (params d r mu).l2top := h1.2
    have h6 : (params d r mu).l1 < y (Fin.natAdd a j) := h1.1
    rw [hrho] at h2 h3
    show _ < z.2 (Fin.natAdd a j) ∧ z.2 (Fin.natAdd a j) < _
    constructor <;> linarith
  have hpos : ∀ j : Fin b, 0 < blockSlow z.2 j := fun j => lt_trans (by linarith) (hslow j).1
  set u : Phase (a+b) := (((2*Real.pi:ℝ)) • z.1, z.2) with hu
  have hphi : u ∈ phiDomain d r mu := by
    refine ⟨?_, fun j _ => ?_⟩
    · refine mem_actionNbhd_iff.2 ⟨blockFast y, hy.1, ?_⟩
      have : ‖KAM.realInclusion a (blockFast u.2) - KAM.realInclusion a (blockFast y)‖ =
          ‖blockFast z.2 - blockFast y‖ := by
        rw [← map_sub, KAM.norm_realInclusion]
      rw [this]
      have h1 := norm_blockFast_sub_le_real z.2 y
      have h2 : ‖z.2 - y‖ < (params d r mu).rho := by rw [← dist_eq_norm]; exact hd
      have h3 : (params d r mu).rho ≤ (params d r mu).rhoBar/2 := by rw [hrho]; linarith
      linarith
    · exact ⟨(hslow j).1, by rw [params_l2_eq]; linarith [(hslow j).2]⟩
  have hav := polar_mem_averagingDomain h hphi
  have hpt : kamPolarPt (KAM.realInclusion₂ (a+b) z) =
      KAM.realInclusion₂ (a+b) (oscillatorPolar u) := by
    rw [← oscillatorPolarComplex_real u (fun j => hpos j)]
    show oscillatorPolarComplex ((2*Real.pi:ℂ) • (KAM.realInclusion₂ (a+b) z).1,
      (KAM.realInclusion₂ (a+b) z).2) = _
    congr 1
    refine Prod.ext (funext fun i => ?_) rfl
    simp [hu]
  have hPsi := hspec.2.2.2.2.2.2.2.2.1 (oscillatorPolar u) hav
  have hext := hspec.2.2.1 hav
  rw [hPsi] at hext
  set W := realAverageMap (pgAvg d r mu h) (oscillatorPolar u) with hW
  have hP := ext_P_real d hmu W hext
  have hfm := kh_ext_fast_mem hext
  have hH0 := (pgExtension d).h0real (blockFast W.2) hfm
  obtain ⟨k, hk⟩ := kamH_real h hz0
  have hPv : (pgExtension d).P mu (KAM.realInclusion₂ (a+b) W) =
      (((pgExtension d).P mu (KAM.realInclusion₂ (a+b) W)).re : ℂ) :=
    Complex.ext (by simp) (by simpa using hP)
  have key : kamF d r mu h (KAM.realInclusion₂ (a+b) z) =
      ((((d.H0 (blockFast W.2) + mu*((pgExtension d).P mu
        (KAM.realInclusion₂ (a+b) W)).re)/(2*Real.pi) - k : ℝ)) : ℂ) := by
    show ((pgExtension d).H0 (blockFast ((pgAvg d r mu h).Psi
        (kamPolarPt (KAM.realInclusion₂ (a+b) z))).2) + mu*(pgExtension d).P mu
        ((pgAvg d r mu h).Psi (kamPolarPt (KAM.realInclusion₂ (a+b) z))))/(2*Real.pi) -
        kamH d mu (KAM.realInclusion (a+b) z.2) = _
    rw [hpt, hPsi, hk]
    have e : blockFast (KAM.realInclusion₂ (a+b) W).2 = KAM.realInclusion a (blockFast W.2) := rfl
    rw [e, hH0]
    push_cast
    rw [← hPv]
  rw [key]
  exact Complex.ofReal_im _

end KAM.Planetary

end
