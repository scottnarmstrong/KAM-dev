/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Tactic.NormNum
public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.Positivity

/-!
# Secular box: closed rational certificate

Blueprint P, Part 14 (`bpP:p14:sb-numerics`): every numerical check N1–N7 of the secular box and the
unused source chain, as one closed conjunction of rational facts discharged by `norm_num`.
-/

public section
namespace KAM.Planetary

theorem sb_numerics :
    (29/100 : ℝ) ≤ 476/1591 ∧ (476/1591 : ℝ) ≤ 31/100 ∧
    (3 : ℝ)*1591 = 4773 ∧ (4773/5000000 : ℝ)*(476/1591) = 357/1250000 ∧
    (87/100 : ℝ)^2 < 103/20 ∧ (21/4 : ℝ) < (23/10)^2 ∧
    (87/100 : ℝ)^2 < (29/100)^2*(189/20) ∧
    (31/100 : ℝ)^2*(193/20) < (97/100)^2 ∧
    (99819/100000 : ℝ)^2 < 1-(3/50)^2 ∧
    (49877/50000 : ℝ)^2 < 1-(7/100)^2 ∧
    (23/10 : ℝ)*(181/100000)+(97/100)*(123/50000) = 16373/2500000 ∧
    (16373/2500000 : ℝ)/(87/100) < 19/2500 ∧
    (1 : ℝ)-(2481/2500)^2 = 94639/6250000 ∧
    (94639/6250000 : ℝ) < (3/20)^2 ∧
    (51/10 : ℝ) < 103/20 ∧ (21/4 : ℝ) < 53/10 ∧
    (47/5 : ℝ) < 189/20 ∧ (193/20 : ℝ) < 97/10 ∧
    (50 : ℝ)*(16373/2500000) < 87/100 ∧
    (1 : ℝ)-(49/50)^2 = 99/2500 ∧ (99/2500 : ℝ) < (1/5)^2 ∧
    (53/10 : ℝ)*(6/5) < (47/5)*(4/5) ∧
    (103/20 : ℝ)*(17/20) = 1751/400 ∧ (193/20 : ℝ)*(23/20) = 4439/400 ∧
    (189/20 : ℝ)*(17/20)-(21/4)*(23/20) = 399/200 ∧
    (21/4 : ℝ)*(23/20) = 483/80 ∧ (483/80 : ℝ) ≤ 4439/400 ∧
    (1751/400 : ℝ) ≤ (189/20)*(17/20) ∧ (399/200 : ℝ) ≤ 1751/400 ∧
    (4439/400 : ℝ)+(483/80) ≤ 4439/200 ∧
    (1 : ℝ)-(3/20)^2 < (989/1000)^2 ∧
    (87/100 : ℝ)*(11/1000) = 957/100000 ∧
    (16373/2500000 : ℝ) < 957/100000 := by
  norm_num

end KAM.Planetary
