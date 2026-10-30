/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.ConstantsQ
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.NormNum

/-!
# The real sharp constants are bounded by their mirrors

Layers `DomA` (fixed-frequency constants), `DomB`,
    `DomC` (isoenergetic chain): each real constant at
the casts of the rational data, with a real `c_R ≤ cRq`, is at most its rational mirror. Only
`c_R` is inexact; the rest of the data are exact casts.
-/

@[expose] public section

namespace KAM.CertificateSharp

open KAM KAM.Sharp KAM.Iso.Sharp

variable {n τ : ℕ} {cR : ℝ} {cRq Mq σKq σBq σTq γbq μq νq : ℚ}

/-- Positivity of the real constants. -/
structure Pos (n τ : ℕ) (cR : ℝ) (Mq σKq σBq σTq γbq μq νq : ℚ) : Prop where
  p_cOm : 0 < cOm n cR (σKq:ℝ)
  p_cSym : 0 < cSym n cR (σKq:ℝ) (σBq:ℝ)
  p_cRed : 0 < cRed n (σKq:ℝ) (σBq:ℝ)
  p_cT0 : 0 < cT0 n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_cT1 : 0 < cT1 n (σKq:ℝ) (σBq:ℝ)
  p_wT : 0 < wT n (Mq:ℝ) (σKq:ℝ)
  p_cT2 : 0 < cT2 n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_hT : 0 < hT n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_cGram : 0 < cGram n (σKq:ℝ)
  p_cB : 0 < cB n (σKq:ℝ) (σBq:ℝ)
  p_cDab : 0 < cDab n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_cDc : 0 < cDc n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_thetaS : 0 < thetaS n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_iCS : 0 < iCS n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCXiN : 0 < iCXiN n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCG : 0 < iCG n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCDXi : 0 < iCDXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCXi : 0 < iCXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCDK : 0 < iCDK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCDw : 0 < iCDw n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCP : 0 < iCP n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ)
  p_iCdK : 0 < iCdK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCLin : 0 < iCLin n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCE1 : 0 < iCE1 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCE2 : 0 < iCE2 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCE : 0 < iCE n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCDT : 0 < iCDT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCDTb : 0 < iCDTb n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iRateD : 0 < iRateD n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iRateB : 0 < iRateB n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iRateT : 0 < iRateT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCStep : 0 < iCStep n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCSum : 0 < iCSum n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
  p_iCStar : 0 < iCStar n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) (μq:ℝ) (νq:ℝ)

/-- The data: `n ≥ 1`, `c_R > 0` with `c_R ≤ cRq`, rational parameters positive. -/
structure Data (n : ℕ) (cR : ℝ) (cRq Mq σKq σBq σTq γbq μq νq : ℚ) : Prop where
  hn : 1 ≤ n
  hcR0 : 0 < cR
  hcR : cR ≤ (cRq : ℝ)
  hM : 0 < Mq
  hσK : 0 < σKq
  hσB : 0 < σBq
  hσT : 0 < σTq
  hγb : 0 < γbq
  hμ : 0 < μq
  hν : 0 < νq

theorem pos_of (τ : ℕ) {cR : ℝ} {cRq Mq σKq σBq σTq γbq μq νq : ℚ}
    (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq) : Pos n τ cR Mq σKq σBq σTq γbq μq νq := by
  obtain ⟨hn, hcR0, -, hM, hσK, hσB, hσT, hγb, hμ, hν⟩ := D
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < Mq := by exact_mod_cast hM
  have hσK' : (0 : ℝ) < σKq := by exact_mod_cast hσK
  have hσB' : (0 : ℝ) < σBq := by exact_mod_cast hσB
  have hσT' : (0 : ℝ) < σTq := by exact_mod_cast hσT
  have hγb' : (0 : ℝ) < γbq := by exact_mod_cast hγb
  have hμ' : (0 : ℝ) < μq := by exact_mod_cast hμ
  have hν' : (0 : ℝ) < νq := by exact_mod_cast hν
  have p_cOm : 0 < cOm n cR (σKq:ℝ) := by unfold cOm; positivity
  have p_cSym : 0 < cSym n cR (σKq:ℝ) (σBq:ℝ) := by unfold cSym; positivity
  have p_cRed : 0 < cRed n (σKq:ℝ) (σBq:ℝ) := by unfold cRed; positivity
  have p_cT0 : 0 < cT0 n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold cT0; positivity
  have p_cT1 : 0 < cT1 n (σKq:ℝ) (σBq:ℝ) := by unfold cT1; positivity
  have p_wT : 0 < wT n (Mq:ℝ) (σKq:ℝ) := by unfold wT; positivity
  have p_cT2 : 0 < cT2 n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold cT2; positivity
  have p_hT : 0 < hT n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold hT; positivity
  have p_cGram : 0 < cGram n (σKq:ℝ) := by unfold cGram vth; positivity
  have p_cB : 0 < cB n (σKq:ℝ) (σBq:ℝ) := by unfold cB vthh; positivity
  have p_cDab : 0 < cDab n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold cDab vthh; positivity
  have p_cDc : 0 < cDc n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold cDc vthh; positivity
  have p_thetaS : 0 < thetaS n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold thetaS; positivity
  have p_iCS : 0 < iCS n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCS; positivity
  have p_iCXiN :
      0 < iCXiN n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCXiN; positivity
  have p_iCG : 0 < iCG n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCG; positivity
  have p_iCDXi :
      0 < iCDXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCDXi; positivity
  have p_iCXi : 0 < iCXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCXi; positivity
  have p_iCDK : 0 < iCDK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCDK; positivity
  have p_iCDw : 0 < iCDw n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCDw; positivity
  have p_iCP : 0 < iCP n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) := by unfold iCP; positivity
  have p_iCdK : 0 < iCdK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCdK; positivity
  have p_iCLin :
      0 < iCLin n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCLin; positivity
  have p_iCE1 : 0 < iCE1 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCE1; positivity
  have p_iCE2 : 0 < iCE2 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCE2; positivity
  have p_iCE : 0 < iCE n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCE; positivity
  have p_iCDT :
      0 < iCDT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCDT vthh; positivity
  have p_iCDTb :
      0 < iCDTb n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCDTb vthh; positivity
  have p_iRateD :
      0 < iRateD n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iRateD; positivity
  have p_iRateB :
      0 < iRateB n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iRateB; positivity
  have p_iRateT :
      0 < iRateT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iRateT vthh; positivity
  have p_iCStep :
      0 < iCStep n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          := by unfold iCStep vth; positivity
  have p_iCSum :
      0 < iCSum n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) := by unfold iCSum; positivity
  have p_iCStar :
      0 < iCStar n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) (μq:ℝ) (νq:ℝ)
          := by unfold iCStar; positivity
  exact ⟨p_cOm, p_cSym, p_cRed, p_cT0, p_cT1, p_wT, p_cT2, p_hT, p_cGram, p_cB, p_cDab, p_cDc,
      p_thetaS, p_iCS, p_iCXiN, p_iCG, p_iCDXi, p_iCXi, p_iCDK, p_iCDw, p_iCP, p_iCdK, p_iCLin,
      p_iCE1, p_iCE2, p_iCE, p_iCDT, p_iCDTb, p_iRateD, p_iRateB, p_iRateT, p_iCStep, p_iCSum,
      p_iCStar⟩

/-- Comparison with the mirrors, layer A. -/
structure DomA (n τ : ℕ) (cR : ℝ) (cRq Mq σKq σBq σTq γbq μq νq : ℚ) : Prop where
  h_cOm : cOm n cR (σKq:ℝ) ≤ (cOmQ n cRq σKq : ℝ)
  h_cSym : cSym n cR (σKq:ℝ) (σBq:ℝ) ≤ (cSymQ n cRq σKq σBq : ℝ)
  h_cRed : cRed n (σKq:ℝ) (σBq:ℝ) ≤ (cRedQ n σKq σBq : ℝ)
  h_cT0 : cT0 n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cT0Q n Mq σKq σBq : ℝ)
  h_cT1 : cT1 n (σKq:ℝ) (σBq:ℝ) ≤ (cT1Q n σKq σBq : ℝ)
  h_wT : wT n (Mq:ℝ) (σKq:ℝ) ≤ (wTQ n Mq σKq : ℝ)
  h_cT2 : cT2 n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cT2Q n τ cRq Mq σKq σBq : ℝ)
  h_hT : hT n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (hTQ n Mq σKq σBq : ℝ)
  h_cGram : cGram n (σKq:ℝ) ≤ (cGramQ n σKq : ℝ)
  h_cB : cB n (σKq:ℝ) (σBq:ℝ) ≤ (cBQ n σKq σBq : ℝ)
  h_cDab : cDab n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cDabQ n Mq σKq σBq : ℝ)
  h_cDc : cDc n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cDcQ n Mq σKq σBq : ℝ)

theorem domA (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq) (P : Pos n τ cR Mq σKq σBq σTq γbq μq
    νq) :
    DomA n τ cR cRq Mq σKq σBq σTq γbq μq νq := by
  obtain ⟨hn, hcR0, hcR, hM, hσK, hσB, hσT, hγb, hμ, hν⟩ := D
  obtain ⟨p_cOm, p_cSym, p_cRed, p_cT0, p_cT1, p_wT, p_cT2, p_hT, p_cGram, p_cB, p_cDab, p_cDc,
      p_thetaS, p_iCS, p_iCXiN, p_iCG, p_iCDXi, p_iCXi, p_iCDK, p_iCDw, p_iCP, p_iCdK, p_iCLin,
      p_iCE1, p_iCE2, p_iCE, p_iCDT, p_iCDTb, p_iRateD, p_iRateB, p_iRateT, p_iCStep, p_iCSum,
      p_iCStar⟩ := P
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < Mq := by exact_mod_cast hM
  have hσK' : (0 : ℝ) < σKq := by exact_mod_cast hσK
  have hσB' : (0 : ℝ) < σBq := by exact_mod_cast hσB
  have hσT' : (0 : ℝ) < σTq := by exact_mod_cast hσT
  have hγb' : (0 : ℝ) < γbq := by exact_mod_cast hγb
  have hμ' : (0 : ℝ) < μq := by exact_mod_cast hμ
  have hν' : (0 : ℝ) < νq := by exact_mod_cast hν
  have hcRq : (0 : ℝ) < cRq := hcR0.trans_le hcR
  have h_cOm : cOm n cR (σKq:ℝ) ≤ (cOmQ n cRq σKq : ℝ) := by
    unfold cOm cOmQ; push_cast; gcongr
  have m_cOm : (0 : ℝ) ≤ (cOmQ n cRq σKq : ℝ) := p_cOm.le.trans h_cOm
  have h_cSym : cSym n cR (σKq:ℝ) (σBq:ℝ) ≤ (cSymQ n cRq σKq σBq : ℝ) := by
    unfold cSym cSymQ; push_cast; gcongr
  have m_cSym : (0 : ℝ) ≤ (cSymQ n cRq σKq σBq : ℝ) := p_cSym.le.trans h_cSym
  have h_cRed : cRed n (σKq:ℝ) (σBq:ℝ) ≤ (cRedQ n σKq σBq : ℝ) := by
    unfold cRed cRedQ; push_cast; gcongr
  have m_cRed : (0 : ℝ) ≤ (cRedQ n σKq σBq : ℝ) := p_cRed.le.trans h_cRed
  have h_cT0 : cT0 n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cT0Q n Mq σKq σBq : ℝ) := by
    unfold cT0 cT0Q; push_cast; gcongr
  have m_cT0 : (0 : ℝ) ≤ (cT0Q n Mq σKq σBq : ℝ) := p_cT0.le.trans h_cT0
  have h_cT1 : cT1 n (σKq:ℝ) (σBq:ℝ) ≤ (cT1Q n σKq σBq : ℝ) := by
    unfold cT1 cT1Q; push_cast; gcongr
  have m_cT1 : (0 : ℝ) ≤ (cT1Q n σKq σBq : ℝ) := p_cT1.le.trans h_cT1
  have h_wT : wT n (Mq:ℝ) (σKq:ℝ) ≤ (wTQ n Mq σKq : ℝ) := by
    unfold wT wTQ; push_cast; gcongr
  have m_wT : (0 : ℝ) ≤ (wTQ n Mq σKq : ℝ) := p_wT.le.trans h_wT
  have h_cT2 : cT2 n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cT2Q n τ cRq Mq σKq σBq : ℝ) := by
    have h2 : (2 : ℝ) ^ ((τ : ℝ) + 1) = (2 : ℝ) ^ (τ + 1) := by
      rw [← Real.rpow_natCast]; norm_num
    unfold cT2 cT2Q; rw [h2]; push_cast; gcongr
  have m_cT2 : (0 : ℝ) ≤ (cT2Q n τ cRq Mq σKq σBq : ℝ) := p_cT2.le.trans h_cT2
  have h_hT : hT n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (hTQ n Mq σKq σBq : ℝ) := by
    unfold hT hTQ; push_cast; gcongr
  have m_hT : (0 : ℝ) ≤ (hTQ n Mq σKq σBq : ℝ) := p_hT.le.trans h_hT
  have h_cGram : cGram n (σKq:ℝ) ≤ (cGramQ n σKq : ℝ) := by
    unfold cGram vth cGramQ; push_cast; gcongr
  have m_cGram : (0 : ℝ) ≤ (cGramQ n σKq : ℝ) := p_cGram.le.trans h_cGram
  have h_cB : cB n (σKq:ℝ) (σBq:ℝ) ≤ (cBQ n σKq σBq : ℝ) := by
    unfold cB vthh cBQ; push_cast; gcongr
  have m_cB : (0 : ℝ) ≤ (cBQ n σKq σBq : ℝ) := p_cB.le.trans h_cB
  have h_cDab : cDab n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cDabQ n Mq σKq σBq : ℝ) := by
    unfold cDab vthh cDabQ; push_cast; gcongr
  have m_cDab : (0 : ℝ) ≤ (cDabQ n Mq σKq σBq : ℝ) := p_cDab.le.trans h_cDab
  have h_cDc : cDc n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (cDcQ n Mq σKq σBq : ℝ) := by
    unfold cDc vthh cDcQ; push_cast; gcongr
  have m_cDc : (0 : ℝ) ≤ (cDcQ n Mq σKq σBq : ℝ) := p_cDc.le.trans h_cDc
  exact ⟨h_cOm, h_cSym, h_cRed, h_cT0, h_cT1, h_wT, h_cT2, h_hT, h_cGram, h_cB, h_cDab, h_cDc⟩

/-- Comparison with the mirrors, layer B. -/
structure DomB (n τ : ℕ) (cR : ℝ) (cRq Mq σKq σBq σTq γbq μq νq : ℚ) : Prop where
  h_thetaS : thetaS n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (thetaSQ n Mq σKq σBq : ℝ)
  h_iCS : iCS n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCSQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCXiN :
      iCXiN n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCXiNQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCG : iCG n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCGQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCDXi :
      iCDXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDXiQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCXi : iCXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCXiQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCDK : iCDK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDKQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCDw : iCDw n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDwQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCP : iCP n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (iCPQ n Mq σKq σBq : ℝ)
  h_iCdK : iCdK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCdKQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCLin :
      iCLin n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCLinQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCE1 : iCE1 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCE1Q n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCE2 : iCE2 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCE2Q n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCE : iCE n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCEQ n cRq Mq σKq σBq σTq γbq : ℝ)

theorem domB (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq) (P : Pos n τ cR Mq σKq σBq σTq γbq μq
    νq) (dA : DomA n τ cR cRq Mq σKq σBq σTq γbq μq νq) :
    DomB n τ cR cRq Mq σKq σBq σTq γbq μq νq := by
  obtain ⟨hn, hcR0, hcR, hM, hσK, hσB, hσT, hγb, hμ, hν⟩ := D
  obtain ⟨p_cOm, p_cSym, p_cRed, p_cT0, p_cT1, p_wT, p_cT2, p_hT, p_cGram, p_cB, p_cDab, p_cDc,
      p_thetaS, p_iCS, p_iCXiN, p_iCG, p_iCDXi, p_iCXi, p_iCDK, p_iCDw, p_iCP, p_iCdK, p_iCLin,
      p_iCE1, p_iCE2, p_iCE, p_iCDT, p_iCDTb, p_iRateD, p_iRateB, p_iRateT, p_iCStep, p_iCSum,
      p_iCStar⟩ := P
  obtain ⟨h_cOm, h_cSym, h_cRed, h_cT0, h_cT1, h_wT, h_cT2, h_hT, h_cGram, h_cB, h_cDab,
      h_cDc⟩ := dA
  have m_cOm : (0 : ℝ) ≤ (cOmQ n cRq σKq : ℝ) := p_cOm.le.trans h_cOm
  have m_cSym : (0 : ℝ) ≤ (cSymQ n cRq σKq σBq : ℝ) := p_cSym.le.trans h_cSym
  have m_cRed : (0 : ℝ) ≤ (cRedQ n σKq σBq : ℝ) := p_cRed.le.trans h_cRed
  have m_cT0 : (0 : ℝ) ≤ (cT0Q n Mq σKq σBq : ℝ) := p_cT0.le.trans h_cT0
  have m_cT1 : (0 : ℝ) ≤ (cT1Q n σKq σBq : ℝ) := p_cT1.le.trans h_cT1
  have m_wT : (0 : ℝ) ≤ (wTQ n Mq σKq : ℝ) := p_wT.le.trans h_wT
  have m_cT2 : (0 : ℝ) ≤ (cT2Q n τ cRq Mq σKq σBq : ℝ) := p_cT2.le.trans h_cT2
  have m_hT : (0 : ℝ) ≤ (hTQ n Mq σKq σBq : ℝ) := p_hT.le.trans h_hT
  have m_cGram : (0 : ℝ) ≤ (cGramQ n σKq : ℝ) := p_cGram.le.trans h_cGram
  have m_cB : (0 : ℝ) ≤ (cBQ n σKq σBq : ℝ) := p_cB.le.trans h_cB
  have m_cDab : (0 : ℝ) ≤ (cDabQ n Mq σKq σBq : ℝ) := p_cDab.le.trans h_cDab
  have m_cDc : (0 : ℝ) ≤ (cDcQ n Mq σKq σBq : ℝ) := p_cDc.le.trans h_cDc
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < Mq := by exact_mod_cast hM
  have hσK' : (0 : ℝ) < σKq := by exact_mod_cast hσK
  have hσB' : (0 : ℝ) < σBq := by exact_mod_cast hσB
  have hσT' : (0 : ℝ) < σTq := by exact_mod_cast hσT
  have hγb' : (0 : ℝ) < γbq := by exact_mod_cast hγb
  have hμ' : (0 : ℝ) < μq := by exact_mod_cast hμ
  have hν' : (0 : ℝ) < νq := by exact_mod_cast hν
  have hcRq : (0 : ℝ) < cRq := hcR0.trans_le hcR
  have h_thetaS : thetaS n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (thetaSQ n Mq σKq σBq : ℝ) := by
    unfold thetaS thetaSQ; push_cast; gcongr
  have m_thetaS : (0 : ℝ) ≤ (thetaSQ n Mq σKq σBq : ℝ) := p_thetaS.le.trans h_thetaS
  have h_iCS :
      iCS n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCSQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCS iCSQ; push_cast; gcongr
  have m_iCS : (0 : ℝ) ≤ (iCSQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCS.le.trans h_iCS
  have h_iCXiN :
      iCXiN n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCXiNQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCXiN iCXiNQ; push_cast; gcongr
  have m_iCXiN : (0 : ℝ) ≤ (iCXiNQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCXiN.le.trans h_iCXiN
  have h_iCG :
      iCG n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCGQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCG iCGQ; push_cast; gcongr
  have m_iCG : (0 : ℝ) ≤ (iCGQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCG.le.trans h_iCG
  have h_iCDXi :
      iCDXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCDXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCDXi iCDXiQ; push_cast; gcongr
  have m_iCDXi : (0 : ℝ) ≤ (iCDXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDXi.le.trans h_iCDXi
  have h_iCXi :
      iCXi n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCXi iCXiQ; push_cast; gcongr
  have m_iCXi : (0 : ℝ) ≤ (iCXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCXi.le.trans h_iCXi
  have h_iCDK :
      iCDK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDKQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCDK iCDKQ; push_cast; gcongr
  have m_iCDK : (0 : ℝ) ≤ (iCDKQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDK.le.trans h_iCDK
  have h_iCDw :
      iCDw n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDwQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCDw iCDwQ; push_cast; gcongr
  have m_iCDw : (0 : ℝ) ≤ (iCDwQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDw.le.trans h_iCDw
  have h_iCP : iCP n (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) ≤ (iCPQ n Mq σKq σBq : ℝ) := by
    unfold iCP iCPQ; push_cast; gcongr
  have m_iCP : (0 : ℝ) ≤ (iCPQ n Mq σKq σBq : ℝ) := p_iCP.le.trans h_iCP
  have h_iCdK :
      iCdK n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCdKQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCdK iCdKQ; push_cast; gcongr
  have m_iCdK : (0 : ℝ) ≤ (iCdKQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCdK.le.trans h_iCdK
  have h_iCLin :
      iCLin n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCLinQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCLin iCLinQ; push_cast; gcongr
  have m_iCLin : (0 : ℝ) ≤ (iCLinQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCLin.le.trans h_iCLin
  have h_iCE1 :
      iCE1 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCE1Q n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCE1 iCE1Q; push_cast; gcongr
  have m_iCE1 : (0 : ℝ) ≤ (iCE1Q n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE1.le.trans h_iCE1
  have h_iCE2 :
      iCE2 n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCE2Q n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCE2 iCE2Q; push_cast; gcongr
  have m_iCE2 : (0 : ℝ) ≤ (iCE2Q n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE2.le.trans h_iCE2
  have h_iCE :
      iCE n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCEQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCE iCEQ; push_cast; gcongr
  have m_iCE : (0 : ℝ) ≤ (iCEQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE.le.trans h_iCE
  exact ⟨h_thetaS, h_iCS, h_iCXiN, h_iCG, h_iCDXi, h_iCXi, h_iCDK, h_iCDw, h_iCP, h_iCdK, h_iCLin,
      h_iCE1, h_iCE2, h_iCE⟩

/-- Comparison with the mirrors, layer C. -/
structure DomC (n τ : ℕ) (cR : ℝ) (cRq Mq σKq σBq σTq γbq μq νq : ℚ) : Prop where
  h_iCDT : iCDT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDTQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCDTb :
      iCDTb n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDTbQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iRateD :
      iRateD n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iRateDQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iRateB :
      iRateB n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iRateBQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iRateT :
      iRateT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iRateTQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCStep :
      iCStep n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCStepQ n τ cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCSum :
      iCSum n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCSumQ n cRq Mq σKq σBq σTq γbq : ℝ)
  h_iCStar :
      iCStar n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) (μq:ℝ) (νq:ℝ)
          ≤ (iCStarQ n τ cRq Mq σKq σBq σTq γbq μq νq : ℝ)

theorem domC (D : Data n cR cRq Mq σKq σBq σTq γbq μq νq) (P : Pos n τ cR Mq σKq σBq σTq γbq μq
    νq) (dA : DomA n τ cR cRq Mq σKq σBq σTq γbq μq νq) (dB : DomB n τ cR cRq Mq σKq σBq σTq γbq
    μq νq) :
    DomC n τ cR cRq Mq σKq σBq σTq γbq μq νq := by
  obtain ⟨hn, hcR0, hcR, hM, hσK, hσB, hσT, hγb, hμ, hν⟩ := D
  obtain ⟨p_cOm, p_cSym, p_cRed, p_cT0, p_cT1, p_wT, p_cT2, p_hT, p_cGram, p_cB, p_cDab, p_cDc,
      p_thetaS, p_iCS, p_iCXiN, p_iCG, p_iCDXi, p_iCXi, p_iCDK, p_iCDw, p_iCP, p_iCdK, p_iCLin,
      p_iCE1, p_iCE2, p_iCE, p_iCDT, p_iCDTb, p_iRateD, p_iRateB, p_iRateT, p_iCStep, p_iCSum,
      p_iCStar⟩ := P
  obtain ⟨h_cOm, h_cSym, h_cRed, h_cT0, h_cT1, h_wT, h_cT2, h_hT, h_cGram, h_cB, h_cDab,
      h_cDc⟩ := dA
  have m_cOm : (0 : ℝ) ≤ (cOmQ n cRq σKq : ℝ) := p_cOm.le.trans h_cOm
  have m_cSym : (0 : ℝ) ≤ (cSymQ n cRq σKq σBq : ℝ) := p_cSym.le.trans h_cSym
  have m_cRed : (0 : ℝ) ≤ (cRedQ n σKq σBq : ℝ) := p_cRed.le.trans h_cRed
  have m_cT0 : (0 : ℝ) ≤ (cT0Q n Mq σKq σBq : ℝ) := p_cT0.le.trans h_cT0
  have m_cT1 : (0 : ℝ) ≤ (cT1Q n σKq σBq : ℝ) := p_cT1.le.trans h_cT1
  have m_wT : (0 : ℝ) ≤ (wTQ n Mq σKq : ℝ) := p_wT.le.trans h_wT
  have m_cT2 : (0 : ℝ) ≤ (cT2Q n τ cRq Mq σKq σBq : ℝ) := p_cT2.le.trans h_cT2
  have m_hT : (0 : ℝ) ≤ (hTQ n Mq σKq σBq : ℝ) := p_hT.le.trans h_hT
  have m_cGram : (0 : ℝ) ≤ (cGramQ n σKq : ℝ) := p_cGram.le.trans h_cGram
  have m_cB : (0 : ℝ) ≤ (cBQ n σKq σBq : ℝ) := p_cB.le.trans h_cB
  have m_cDab : (0 : ℝ) ≤ (cDabQ n Mq σKq σBq : ℝ) := p_cDab.le.trans h_cDab
  have m_cDc : (0 : ℝ) ≤ (cDcQ n Mq σKq σBq : ℝ) := p_cDc.le.trans h_cDc
  obtain ⟨h_thetaS, h_iCS, h_iCXiN, h_iCG, h_iCDXi, h_iCXi, h_iCDK, h_iCDw, h_iCP, h_iCdK,
      h_iCLin, h_iCE1, h_iCE2, h_iCE⟩ := dB
  have m_thetaS : (0 : ℝ) ≤ (thetaSQ n Mq σKq σBq : ℝ) := p_thetaS.le.trans h_thetaS
  have m_iCS : (0 : ℝ) ≤ (iCSQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCS.le.trans h_iCS
  have m_iCXiN : (0 : ℝ) ≤ (iCXiNQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCXiN.le.trans h_iCXiN
  have m_iCG : (0 : ℝ) ≤ (iCGQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCG.le.trans h_iCG
  have m_iCDXi : (0 : ℝ) ≤ (iCDXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDXi.le.trans h_iCDXi
  have m_iCXi : (0 : ℝ) ≤ (iCXiQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCXi.le.trans h_iCXi
  have m_iCDK : (0 : ℝ) ≤ (iCDKQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDK.le.trans h_iCDK
  have m_iCDw : (0 : ℝ) ≤ (iCDwQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDw.le.trans h_iCDw
  have m_iCP : (0 : ℝ) ≤ (iCPQ n Mq σKq σBq : ℝ) := p_iCP.le.trans h_iCP
  have m_iCdK : (0 : ℝ) ≤ (iCdKQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCdK.le.trans h_iCdK
  have m_iCLin : (0 : ℝ) ≤ (iCLinQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCLin.le.trans h_iCLin
  have m_iCE1 : (0 : ℝ) ≤ (iCE1Q n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE1.le.trans h_iCE1
  have m_iCE2 : (0 : ℝ) ≤ (iCE2Q n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE2.le.trans h_iCE2
  have m_iCE : (0 : ℝ) ≤ (iCEQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCE.le.trans h_iCE
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hM' : (0 : ℝ) < Mq := by exact_mod_cast hM
  have hσK' : (0 : ℝ) < σKq := by exact_mod_cast hσK
  have hσB' : (0 : ℝ) < σBq := by exact_mod_cast hσB
  have hσT' : (0 : ℝ) < σTq := by exact_mod_cast hσT
  have hγb' : (0 : ℝ) < γbq := by exact_mod_cast hγb
  have hμ' : (0 : ℝ) < μq := by exact_mod_cast hμ
  have hν' : (0 : ℝ) < νq := by exact_mod_cast hν
  have hcRq : (0 : ℝ) < cRq := hcR0.trans_le hcR
  have h_iCDT :
      iCDT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) ≤ (iCDTQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCDT vthh iCDTQ; push_cast; gcongr
  have m_iCDT : (0 : ℝ) ≤ (iCDTQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDT.le.trans h_iCDT
  have h_iCDTb :
      iCDTb n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCDTbQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCDTb vthh iCDTbQ; push_cast; gcongr
  have m_iCDTb : (0 : ℝ) ≤ (iCDTbQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCDTb.le.trans h_iCDTb
  have h_iRateD :
      iRateD n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iRateDQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iRateD iRateDQ; push_cast; gcongr
  have m_iRateD : (0 : ℝ) ≤ (iRateDQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iRateD.le.trans h_iRateD
  have h_iRateB :
      iRateB n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iRateBQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iRateB iRateBQ; push_cast; gcongr
  have m_iRateB : (0 : ℝ) ≤ (iRateBQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iRateB.le.trans h_iRateB
  have h_iRateT :
      iRateT n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iRateTQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iRateT vthh iRateTQ; push_cast; gcongr
  have m_iRateT : (0 : ℝ) ≤ (iRateTQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iRateT.le.trans h_iRateT
  have h_iCStep :
      iCStep n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCStepQ n τ cRq Mq σKq σBq σTq γbq : ℝ) := by
    have h2 := h_cT2
    unfold iCStep iCStepQ vth; push_cast; gcongr
  have m_iCStep : (0 : ℝ) ≤ (iCStepQ n τ cRq Mq σKq σBq σTq γbq : ℝ) := p_iCStep.le.trans h_iCStep
  have h_iCSum :
      iCSum n cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ)
          ≤ (iCSumQ n cRq Mq σKq σBq σTq γbq : ℝ) := by
    unfold iCSum iCSumQ; push_cast; gcongr
  have m_iCSum : (0 : ℝ) ≤ (iCSumQ n cRq Mq σKq σBq σTq γbq : ℝ) := p_iCSum.le.trans h_iCSum
  have h_iCStar :
      iCStar n (τ:ℝ) cR (Mq:ℝ) (σKq:ℝ) (σBq:ℝ) (σTq:ℝ) (γbq:ℝ) (μq:ℝ) (νq:ℝ)
          ≤ (iCStarQ n τ cRq Mq σKq σBq σTq γbq μq νq : ℝ) := by
    have h4 : (2 : ℝ) ^ (2 * (2 * (τ : ℝ))) = (2 : ℝ) ^ (2 * (2 * τ)) := by
      rw [← Real.rpow_natCast]; push_cast; ring_nf
    unfold iCStar iCStarQ; rw [h4]; push_cast; gcongr
  have m_iCStar :
      (0 : ℝ) ≤ (iCStarQ n τ cRq Mq σKq σBq σTq γbq μq νq : ℝ) := p_iCStar.le.trans h_iCStar
  exact ⟨h_iCDT, h_iCDTb, h_iRateD, h_iRateB, h_iRateT, h_iCStep, h_iCSum, h_iCStar⟩

end KAM.CertificateSharp
