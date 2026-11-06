/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Tdat0
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Tdat1
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Tdat2
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.Bdat
public import KAM.EffectiveStability.SJSU.Ham.HtBridgeInst.HwGroups

/-!
# N7's Horner sums are N5a's Taylor coefficients for SJSU (T2-CONF, N5a-2)

`sjsuHD_Ht_eq_hCoef`: for N7's ledger data `sjsuHD` (`KAM.EffectiveStability.SJSU.Ledger.H.HData`),
`sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m = hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m)`, the Taylor
coefficient `h_m = Σ_n T_n Π_j binom(n_j/2, m_j) B_j^{n_j/2 - m_j}` of N5a's tube Hamiltonian
`sjsuHTilde sjsuB`. The data equalities are kernel checks:
* `sjsuTdat n = pDense 9 (tTerms sjsuE sjsuN sjsuHwAll n)` for every group (blocks of 8, in
  `HtBridgeInst.Tdat0`–`Tdat2`);
* `sjsuBdat j = scatter 61² 0 (bPairs 30 sjsuEccModes sjsuEccIbar j)` (`HtBridgeInst.Bdat`);
* every row exponent of `H_w` is a group of `sjsuNs` (`HtBridgeInst.HwGroups`); the groups are
  distinct and bounded by 18 (`HtBridgeInst.Groups`).
-/

@[expose] public noncomputable section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

theorem sjsuTdat_blocks : ∀ k < 90, ((sjsuNs.drop (8 * k)).take 8).all tdatOk = true := by
  intro k hk
  by_cases h₀ : k < 30
  · exact sjsuTdat_blocks0 k (Nat.zero_le k) h₀
  by_cases h₁ : k < 60
  · exact sjsuTdat_blocks1 k (by omega) h₁
  · exact sjsuTdat_blocks2 k (by omega) hk

theorem sjsuTdat_eq {n : ℕ × ℕ × ℕ} (hn : n ∈ sjsuNs) :
    sjsuTdat n = pDense 9 (tTerms sjsuE sjsuN sjsuHwAll n) := by
  have h := all_of_blocks (c := 8) (K := 90) tdatOk sjsuNs (by norm_num) sjsuNs_length
    sjsuTdat_blocks n hn
  unfold tdatOk at h
  exact eq_of_listBEq h

/-! The true functions of N7's ledger, unfolded by `simp` (a `rfl` check would let the unifier
evaluate the dense data). -/

theorem sjsuHD_Tt_eq (n : ℕ × ℕ × ℕ) : sjsuHD.Tt n = denseCos 9 (sjsuTdat n) := by
  simp only [HData.Tt, sjsuHD]

theorem sjsuHD_Bt_eq (j : Fin 3) : sjsuHD.Bt j = denseCos 30 (sjsuBdat j) := by
  simp only [HData.Bt, sjsuHD]

/-- **The bridge for SJSU**: N7's Horner sum is N5a's Taylor coefficient. -/
theorem sjsuHD_Ht_eq_hCoef (m : ℕ × ℕ × ℕ) (φ : Fin 2 → ℝ) :
    sjsuHD.Ht sjsuHD.Tt sjsuHD.Pt m φ = hCoef sjsuE sjsuN sjsuHwAll sjsuB (ofTriple m) φ := by
  refine HData.Ht_eq_hCoef sjsuHD sjsuE sjsuN sjsuHwAll sjsuB sjsuNs_nodup sjsuNs_bound
    (fun n hn => ?_) (fun j => ?_) sjsuB_pos sjsuHwAll_groups m φ
  · rw [sjsuHD_Tt_eq, sjsuTdat_eq hn, sjsuTn_eq_denseCos]
  · rw [sjsuHD_Bt_eq, eq_of_listBEq (sjsuBdat_check j), sjsuB_eq_denseCos]

end KAM.EffectiveStability.SJSU

end
