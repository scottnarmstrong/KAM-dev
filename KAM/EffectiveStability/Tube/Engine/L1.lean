/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.Tube.Engine.Lit
public import KAM.EffectiveStability.Tube.Trig.Packed

/-!
# The packed `ℓ¹` norm (T2-CONF, N7)

`l1P w N l D` computes `Σ_i |d_i|` for the `N` signed slots of a packed integer `D` without decoding
them: one load check (`loadOk`, slots in `[-2^l, 2^l)`), the packed absolute values (`packAbs`),
one multiplication by the all-ones packing `Σ_{i<N} 2^(w i)`, and a read of digit `N - 1` (the dot
product with the all-ones vector, `dot_extract`). The no-overflow condition is `N 2^l < 2^w`.

`l1P_eq`: if `l1Ok w N l D` and `D = packSum w cs` for a list of `N` slots with `2 |c| < 2^w`, then
`l1P w N l D = l1 cs`.
-/

@[expose] public section

namespace KAM.EffectiveStability.Tube

open Finset KAM.Certificate KAM.CertificateSharp.Packed

/-- The packed `ℓ¹` norm (kernel form). -/
def l1P (w N l : ℕ) (D : ℤ) : ℕ :=
  ((packAbs w N l D * periodic w N 1) >>> (w * (N - 1))) &&& (2 ^ w - 1)

/-- The guard of `l1P`: the load check and the no-overflow condition. -/
def l1Ok (w N l : ℕ) (D : ℤ) : Bool :=
  decide (0 < N) && decide (l + 2 ≤ w) && decide (N * 2 ^ l < 2 ^ w) && loadOk w N l D

theorem getD_map_natAbs (l : List ℤ) (i : ℕ) :
    ((l.map Int.natAbs).map (fun n : ℕ => (n : ℤ))).getD i 0 = |l.getD i 0| := by
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[i]? <;> simp

/-- **The packed `ℓ¹` norm is the `ℓ¹` norm of the slots.** -/
theorem l1P_eq {w N l : ℕ} {D : ℤ} (h : l1Ok w N l D = true) {cs : List ℤ}
    (hD : packSum w cs = D) (hlen : cs.length = N) (hcs : SlotsBounded w cs) :
    (l1P w N l D : ℤ) = l1 cs := by
  simp only [l1Ok, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨hN, hlw⟩, hov⟩, hload⟩ := h
  have hw : 0 < w := by omega
  obtain ⟨ds, hdl, hdb, hdD⟩ := loadOk_sound hload
  have h2 : (2 : ℤ) ^ (l + 2) ≤ 2 ^ w := pow_le_pow_right₀ (by norm_num) hlw
  have hpl : (0 : ℤ) < 2 ^ l := by positivity
  -- the loaded slots are the given slots
  have hds : ds = cs := by
    refine packSum_injective (fun c hc => ?_) hcs (by rw [hdl, hlen]) (hdD.trans hD.symm)
    have := hdb c hc
    have hc' : |c| ≤ 2 ^ l := abs_le.mpr ⟨this.1, this.2.le⟩
    rw [pow_add] at h2
    norm_num at h2
    linarith
  subst hds
  -- packed absolute values, then the dot product with the all-ones vector
  have habs := packAbs_spec hlw hdl hdb
  set a : List ℤ := (ds.map Int.natAbs).map (↑) with ha
  set v : List ℤ := List.replicate N (1 : ℤ) with hv
  have hX : ((packAbs w N l D * periodic w N 1 : ℕ) : ℤ) = packSum w a * packSum w v := by
    rw [← hdD, habs]
    push_cast
    rw [natPack_cast, periodic_cast hw]
    rfl
  have ha0 : ∀ x ∈ a, 0 ≤ x := fun x hx => by
    obtain ⟨n, -, rfl⟩ := List.mem_map.mp hx; exact Nat.cast_nonneg n
  have hv0 : ∀ x ∈ v, 0 ≤ x := fun x hx => by
    rw [hv, List.mem_replicate] at hx; rw [hx.2]; norm_num
  have hal : a.length = N := by simp [ha, hdl]
  have hl1a : l1 a = l1 ds := by
    rw [l1_eq, l1_eq, hal, hdl]
    refine sum_congr rfl fun i hi => ?_
    rw [ha, getD_map_natAbs, abs_abs]
  have hl1le : l1 ds ≤ N * 2 ^ l := by
    rw [l1_eq, hdl]
    calc ∑ i ∈ range N, |ds.getD i 0| ≤ ∑ _i ∈ range N, (2 : ℤ) ^ l := by
          refine sum_le_sum fun i hi => ?_
          have hi' : i < ds.length := by rw [hdl]; exact mem_range.mp hi
          have hm : ds.getD i 0 ∈ ds := by
            rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi']
            exact List.getElem_mem _
          have := hdb _ hm
          rw [abs_le]; constructor <;> linarith [this.1, this.2]
      _ = N * 2 ^ l := by simp
  have hmaxv : maxAbs v ≤ 1 := maxAbs_le fun c hc => by
    rw [hv, List.mem_replicate] at hc; rw [hc.2]; norm_num
  have hbound : ∀ c ∈ listConv a v, c < 2 ^ w := by
    intro c hc
    obtain ⟨m, hm, rfl⟩ := List.getElem_of_mem hc
    have := abs_listConv_getD_le a v m
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm, Option.getD_some] at this
    have h1 : l1 a * (maxAbs v : ℤ) ≤ l1 a := by
      have := l1_nonneg a
      have : (maxAbs v : ℤ) ≤ 1 := by exact_mod_cast hmaxv
      nlinarith
    have hov' : ((N * 2 ^ l : ℕ) : ℤ) < ((2 ^ w : ℕ) : ℤ) := by exact_mod_cast hov
    push_cast at hov'
    linarith [le_abs_self (listConv a v)[m]]
  have hdot := dot_extract ha0 hv0 hbound hX (N - 1)
  -- the conv entry `N - 1` is the sum of `a`
  have hae : a ≠ [] := by rw [← List.length_pos_iff, hal]; exact hN
  have hve : v ≠ [] := by rw [← List.length_pos_iff, hv, List.length_replicate]; exact hN
  have hentry : (listConv a v).getD (N - 1) 0 = l1 a := by
    rw [listConv_getD hae hve (by rw [hal, hv, List.length_replicate]; omega), l1_eq, hal,
      Nat.sub_add_cancel hN]
    refine sum_congr rfl fun p hp => ?_
    have hp' := mem_range.mp hp
    have hv1 : v.getD (N - 1 - p) 0 = 1 := by
      rw [hv, List.getD_eq_getElem?_getD, List.getElem?_replicate]
      simp only [show N - 1 - p < N by omega, ite_true, Option.getD_some]
    rw [hv1, mul_one, abs_of_nonneg (getD_nonneg ha0 p)]
  unfold l1P
  rw [hdot, hentry, ← hl1a, Int.toNat_of_nonneg (l1_nonneg a)]

end KAM.EffectiveStability.Tube

end
