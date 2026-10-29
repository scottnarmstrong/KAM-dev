/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.WrapperTube

/-!
# `stepP:p11:wr-tube` (P11A-P10)

Real points of `Ξ_ε` with actions in `[-1,1]` lie in the circular tube of radius `ζ_*`.
-/

@[expose] public noncomputable section
open Set
namespace KAM.Planetary

section TubeMain

variable {n : ℕ}

theorem p11_sq_aux {a u d : ℝ} (h : |a - u| ≤ d) : a ^ 2 ≤ 2*u ^ 2 + 2*d ^ 2 := by
  have h1 : (a - u) ^ 2 ≤ d ^ 2 := by
    rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) h 2
  nlinarith [sq_nonneg (a - 2*u)]

theorem p11_tube_sq {a b a' b' u1 u2 ε d : ℝ} (hu : u1 ^ 2 + u2 ^ 2 ≤ 3*ε)
    (h1 : |a - u1| ≤ d) (h2 : |b - u2| ≤ d) (ha : a = a') (hb : b = b') :
    a' ^ 2 + b' ^ 2 ≤ 6*ε + 4*d^2 := by
  subst ha hb
  have := p11_sq_aux h1
  have := p11_sq_aux h2
  linarith

theorem p11_tube_lambda {vJ uJ wJ yJ J0 zc ε dJ δ Lam : ℝ} (hz : |zc| ≤ 1) (hε : 0 ≤ ε)
    (h1 : |vJ - uJ| ≤ dJ) (h2 : uJ = wJ) (h3 : |wJ - (J0 + ε*zc)| ≤ ε) (h4 : yJ = J0 + ε*zc)
    (hR : 2*ε + dJ ≤ 7*Real.pi*δ/4) (hn : |J0/(2*Real.pi) - Lam| < δ/8) (hδ : 0 ≤ δ) :
    |vJ/(2*Real.pi) - Lam| ≤ δ := by
  subst h2 h4
  have hz' := abs_le.1 hz
  have hε' : |ε*zc| ≤ ε := by rw [abs_mul, abs_of_nonneg hε]; nlinarith [abs_nonneg zc]
  have he : |vJ - J0| ≤ 7*Real.pi*δ/4 := by
    calc |vJ - J0| = |(vJ - uJ) + (uJ - (J0 + ε*zc)) + ε*zc| := by ring_nf
      _ ≤ |vJ - uJ| + |uJ - (J0 + ε*zc)| + |ε*zc| := by
        refine (abs_add_le _ _).trans ?_
        gcongr
        exact abs_add_le _ _
      _ ≤ _ := by linarith
  have e : vJ/(2*Real.pi) - Lam = (J0/(2*Real.pi) - Lam) + (vJ - J0)/(2*Real.pi) := by ring
  rw [e]
  have : |(vJ - J0)/(2*Real.pi)| ≤ 7*δ/8 := by
    rw [abs_div, abs_of_pos (by positivity : (0:ℝ) < 2*Real.pi), div_le_iff₀ (by positivity)]
    nlinarith
  exact (abs_add_le _ _).trans (by linarith)

end TubeMain

end KAM.Planetary

end
