/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailAcc

/-!
# The slot tables dominate the hats (T2-CONF, N9 (C))

`sjsuHat j n m ≤ sjsuGT K j m` (and the `Du`, `P` versions) for `n ≤ K ≤ 18`, `m ≤ 10`, in three
kernel checks by range of `K`.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsu_tab_ok_lo : ∀ K < 7, ∀ n < K + 1, ∀ j : Fin 3, ∀ m < 11,
    sjsuHat j n m ≤ sjsuGT K j m ∧ sjsuHatDu j n m ≤ sjsuGTD K j m ∧
      sjsuHatP j n m ≤ sjsuGTP K j m := by
  decide +kernel

theorem sjsu_tab_ok_mid : ∀ K < 13, 7 ≤ K → ∀ n < K + 1, ∀ j : Fin 3, ∀ m < 11,
    sjsuHat j n m ≤ sjsuGT K j m ∧ sjsuHatDu j n m ≤ sjsuGTD K j m ∧
      sjsuHatP j n m ≤ sjsuGTP K j m := by
  decide +kernel

theorem sjsu_tab_ok_hi : ∀ K < 19, 13 ≤ K → ∀ n < K + 1, ∀ j : Fin 3, ∀ m < 11,
    sjsuHat j n m ≤ sjsuGT K j m ∧ sjsuHatDu j n m ≤ sjsuGTD K j m ∧
      sjsuHatP j n m ≤ sjsuGTP K j m := by
  decide +kernel

theorem sjsu_tab_ok : ∀ K < 19, ∀ n < K + 1, ∀ j : Fin 3, ∀ m < 11,
    sjsuHat j n m ≤ sjsuGT K j m ∧ sjsuHatDu j n m ≤ sjsuGTD K j m ∧
      sjsuHatP j n m ≤ sjsuGTP K j m := by
  intro K hK
  rcases Nat.lt_or_ge K 7 with h | h
  · exact sjsu_tab_ok_lo K h
  rcases Nat.lt_or_ge K 13 with h' | h'
  · exact sjsu_tab_ok_mid K h' h
  · exact sjsu_tab_ok_hi K hK h'

end KAM.EffectiveStability.SJSU

end
