/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.CertificateSharp.Packed.Enc

/-!
# The zero mode of a packed model

* `slotAt w p Z`: the balanced digit of slot `p` of a packed signed integer: two balanced residues
  (`Int.bmod`), one subtraction, one exact division. `slotAt_packSum`: on slots with `2|c| < 2^w` it
  is the slot (`packSum_append`, `two_abs_packSum_lt`).
* `torusAverage_slotSum`: the real-torus average of a slot Fourier sum is the slot of the zero key
  (`keyOf_eq_zero_slot`: on a box slot, only the zero key's slot carries the zero key).
* `PEnc.average`: the average of a packed model's function is its zero-key slot, scaled, up to the
  model's radius.
-/

@[expose] public noncomputable section

namespace KAM.CertificateSharp.Packed

open KAM KAM.Certificate KAM.Certificate.CertArith

/-- The balanced digit of slot `p` (width `w`) of a packed signed integer. -/
def slotAt (w p : ℕ) (Z : ℤ) : ℤ :=
  (Z.bmod (2 ^ (w * (p + 1))) - Z.bmod (2 ^ (w * p))) / (2 : ℤ) ^ (w * p)

theorem packSum_append (w : ℕ) :
    ∀ a b : List ℤ, packSum w (a ++ b) = packSum w a + 2 ^ (w * a.length) * packSum w b
  | [], b => by simp [packSum_nil]
  | c :: a, b => by
    rw [List.cons_append, packSum_cons, packSum_cons, packSum_append w a b, List.length_cons]
    ring

theorem two_abs_packSum_lt {w : ℕ} :
    ∀ {a : List ℤ}, (∀ c ∈ a, 2 * |c| < 2 ^ w) → 2 * |packSum w a| < 2 ^ (w * a.length)
  | [], _ => by simp [packSum_nil]
  | c :: a, h => by
    have ih := two_abs_packSum_lt (a := a) fun d hd => h d (by simp [hd])
    have hc := h c (by simp)
    rw [packSum_cons, List.length_cons]
    have hpos : (0 : ℤ) < 2 ^ w := by positivity
    have h1 : |c + 2 ^ w * packSum w a| ≤ |c| + 2 ^ w * |packSum w a| := by
      refine (abs_add_le _ _).trans (le_of_eq ?_)
      rw [abs_mul, abs_of_pos hpos]
    have hpow : (2 : ℤ) ^ (w * (a.length + 1)) = 2 ^ w * 2 ^ (w * a.length) := by ring
    rw [hpow]
    have h2 : 2 ^ w * (2 * |packSum w a|) ≤ 2 ^ w * (2 ^ (w * a.length) - 1) :=
      mul_le_mul_of_nonneg_left (by omega) hpos.le
    nlinarith

/-- The balanced residue of a packed integer modulo `2^(w k)` is the packing of its first `k`
slots. -/
theorem bmod_packSum {w : ℕ} {d : List ℤ} (hd : ∀ c ∈ d, 2 * |c| < 2 ^ w) {k : ℕ}
    (hk : k ≤ d.length) : (packSum w d).bmod (2 ^ (w * k)) = packSum w (d.take k) := by
  have hsplit := packSum_append w (d.take k) (d.drop k)
  rw [List.take_append_drop, List.length_take, min_eq_left hk] at hsplit
  have hb := two_abs_packSum_lt (w := w) (a := d.take k) fun c hc => hd c (List.mem_of_mem_take hc)
  rw [List.length_take, min_eq_left hk] at hb
  rw [Int.bmod_eq_iff (by positivity)]
  push_cast
  set M : ℤ := 2 ^ (w * k)
  set x := packSum w (d.take k)
  have hl := neg_abs_le x
  have hu := le_abs_self x
  refine ⟨by omega, by omega, ⟨-packSum w (d.drop k), by rw [hsplit]; ring⟩⟩

/-- **Digit extraction**: `slotAt` reads slot `p` of a packing of slots below `2^(w-1)`. -/
theorem slotAt_packSum {w : ℕ} {d : List ℤ} (hd : ∀ c ∈ d, 2 * |c| < 2 ^ w) {p : ℕ}
    (hp : p < d.length) : slotAt w p (packSum w d) = d.getD p 0 := by
  unfold slotAt
  rw [bmod_packSum hd hp.le, bmod_packSum hd (by omega : p + 1 ≤ d.length), List.take_add_one,
    List.getElem?_eq_getElem hp, Option.toList_some, packSum_append, List.length_take,
    min_eq_left hp.le, packSum_cons, packSum_nil, List.getD_eq_getElem?_getD,
    List.getElem?_eq_getElem hp, Option.getD_some, mul_zero, add_zero, add_sub_cancel_left]
  exact Int.mul_ediv_cancel_left _ (by positivity)

/-- On a box slot, the zero key is carried only by the slot of the zero key. -/
theorem keyOf_eq_zero_slot {L : PackLayout} (hw : layoutWf L = true) {n : ℕ}
    (hn : L.dims.length = n) {p0 : ℕ} (hp : L.slot (List.replicate n 0) = some p0) {i : ℕ}
    (hi : InBox L i) (hk : certKeyFun n (keyOf L i) = 0) : i = p0 := by
  obtain ⟨u, hul, hult, rfl⟩ := hi
  obtain ⟨-, -, rfl⟩ := PackLayout.slot_eq_some hp
  have hkey := keyOf_packDot hw hul hult
  congr 1
  apply List.ext_getElem
  · simp [hul, PackLayout.keyOffsets]
  · intro j h1 h2
    have hj : j < n := by rw [← hn, ← hul]; exact h1
    have hz := congrFun hk ⟨j, hj⟩
    simp only [certKeyFun, Pi.zero_apply] at hz
    rw [hkey, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (hn ▸ hj),
      Option.map_some, Option.getD_some] at hz
    have h3 := (PackLayout.keyOffsets_toNat_getD L (List.replicate n 0) j)
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2, Option.getD_some,
      ite_eq_left (hn ▸ hj : j < L.dims.length)] at h3
    have hu : u[j] = u.getD j 0 := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h1, Option.getD_some]
    have hr0 : (List.replicate n (0 : ℤ)).getD j 0 = 0 := by
      simp [List.getD_eq_getElem?_getD, hj]
    rw [h3, hu, hr0]
    omega

/-- **The average of a slot Fourier sum** is the slot of the zero key. -/
theorem torusAverage_slotSum {L : PackLayout} (hw : layoutWf L = true) {n : ℕ}
    (hn : L.dims.length = n) {p0 : ℕ} (hp : L.slot (List.replicate n 0) = some p0) {B : ℕ}
    {Z : ℤ} {d : List ℤ} (hs : SRep L B Z d) :
    torusAverage (fun x : Fin n → ℝ => slotSum L n d fun j => (x j : ℂ)) = d.getD p0 0 := by
  have hemb : Continuous fun x : Fin n → ℝ => fun j => (x j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hc : ∀ i, Continuous fun x : Fin n → ℝ =>
      (d.getD i 0 : ℂ) * character (certKeyFun n (keyOf L i)) fun j => (x j : ℂ) :=
    fun i => continuous_const.mul ((differentiable_character _).continuous.comp hemb)
  have hch : ∀ m : Fin n → ℤ, (∫ x in Set.pi Set.univ (fun _ : Fin n => Set.Icc (0 : ℝ) 1),
      character m fun j => (x j : ℂ)) = if m = 0 then 1 else 0 := fun m => by
    have := torusAverage_character m
    rwa [torusAverage] at this
  unfold slotSum
  rw [torusAverage, MeasureTheory.integral_finsetSum _ fun i _ =>
    integrableOn_unitCube_of_continuous (hc i)]
  simp only [MeasureTheory.integral_const_mul, hch]
  have hp0 : p0 < d.length := hs.len ▸ PackLayout.slot_lt_denseLen hp
  rw [Finset.sum_eq_single p0]
  · have hk0 : certKeyFun n (keyOf L p0) = 0 := by
      rw [(keyOf_slot hw hp).1]
      funext j
      simp [certKeyFun, List.getD_eq_getElem?_getD]
    simp [hk0]
  · intro i _ hi
    by_cases hz : d.getD i 0 = 0
    · rw [hz]
      simp
    · have hk : certKeyFun n (keyOf L i) ≠ 0 := fun hk =>
        hi (keyOf_eq_zero_slot hw hn hp (hs.box i hz) hk)
      simp [hk]
  · intro h
    exact absurd (Finset.mem_range.mpr hp0) h

section Sound

variable {α : Type} [CertArith α]

/-- **The average of a packed model**: the zero-key slot at scale `2^e`, up to the radius. -/
theorem PEnc.average {L : PackLayout} (hw : layoutWf L = true) {n : ℕ} (hn : L.dims.length = n)
    {p0 : ℕ} (hp : L.slot (List.replicate n 0) = some p0) {A e : ℕ} (hA : 2 * A < 2 ^ L.width)
    {x : PC} {r nb : α} {ρ : ℝ} (hρ : 0 < ρ) {f : (Fin n → ℂ) → ℂ}
    (hf : ContinuousOn f (complexStrip n ρ)) (hx : PEnc L A e x r nb n ρ f) :
    ‖torusAverage (fun v : Fin n → ℝ => f fun j => (v j : ℂ)) -
        ((slotAt L.width p0 x.re : ℂ) + Complex.I * (slotAt L.width p0 x.im : ℂ)) / 2 ^ e‖ ≤
      val r := by
  obtain ⟨F, ⟨dr, di, hr, hi, hF⟩, hb⟩ := hx
  have hbd : ∀ {Z : ℤ} {d : List ℤ}, SRep L A Z d → ∀ c ∈ d, 2 * |c| < 2 ^ L.width := by
    intro Z d hs c hc
    have := hs.bound c hc
    have hA' : (2 * A : ℤ) < 2 ^ L.width := by exact_mod_cast hA
    omega
  have hp0 : ∀ {Z : ℤ} {d : List ℤ}, SRep L A Z d → p0 < d.length :=
    fun hs => hs.len ▸ PackLayout.slot_lt_denseLen hp
  have hre : slotAt L.width p0 x.re = dr.getD p0 0 := by
    rw [← hr.pack]; exact slotAt_packSum (hbd hr) (hp0 hr)
  have him : slotAt L.width p0 x.im = di.getD p0 0 := by
    rw [← hi.pack]; exact slotAt_packSum (hbd hi) (hp0 hi)
  have hemb : Continuous fun v : Fin n → ℝ => fun j => (v j : ℂ) :=
    continuous_pi fun j => Complex.continuous_ofReal.comp (continuous_apply j)
  have hcs : ∀ d : List ℤ, Continuous fun v : Fin n → ℝ => slotSum L n d fun j => (v j : ℂ) := by
    intro d
    unfold slotSum
    exact continuous_finsetSum _ fun i _ =>
      continuous_const.mul ((differentiable_character _).continuous.comp hemb)
  have hFeq : (fun v : Fin n → ℝ => F (fun j => (v j : ℂ)) / 2 ^ e) = fun v =>
      ((slotSum L n dr fun j => (v j : ℂ)) + Complex.I * slotSum L n di fun j => (v j : ℂ)) /
        2 ^ e := by
    funext v
    rw [hF]
  have hFc : Continuous fun v : Fin n → ℝ => F (fun j => (v j : ℂ)) / 2 ^ e := by
    rw [hFeq]
    exact ((hcs dr).add (continuous_const.mul (hcs di))).div_const _
  have hfc : Continuous fun v : Fin n → ℝ => f fun j => (v j : ℂ) :=
    hf.comp_continuous hemb fun v => ofReal_mem_complexStrip hρ v
  have havgF : torusAverage (fun v : Fin n → ℝ => F (fun j => (v j : ℂ)) / 2 ^ e) =
      ((dr.getD p0 0 : ℂ) + Complex.I * (di.getD p0 0 : ℂ)) / 2 ^ e := by
    rw [hFeq, torusAverage, MeasureTheory.integral_div, MeasureTheory.integral_add
      (integrableOn_unitCube_of_continuous (hcs dr))
      (integrableOn_unitCube_of_continuous (f := fun v : Fin n → ℝ =>
        Complex.I * slotSum L n di fun j => (v j : ℂ)) (continuous_const.mul (hcs di))),
      MeasureTheory.integral_const_mul, ← torusAverage, ← torusAverage,
      torusAverage_slotSum hw hn hp hr, torusAverage_slotSum hw hn hp hi]
  have hdiff : torusAverage (fun v : Fin n → ℝ => f fun j => (v j : ℂ)) -
      torusAverage (fun v : Fin n → ℝ => F (fun j => (v j : ℂ)) / 2 ^ e) =
      torusAverage (fun v : Fin n → ℝ => (f fun j => (v j : ℂ)) - F (fun j => (v j : ℂ)) / 2 ^ e) :=
    by
    rw [torusAverage, torusAverage, torusAverage, MeasureTheory.integral_sub
      (integrableOn_unitCube_of_continuous hfc) (integrableOn_unitCube_of_continuous hFc)]
  rw [hre, him, ← havgF, hdiff]
  exact norm_torusAverage_le fun v _ => (hb _ (ofReal_mem_complexStrip hρ v)).1

end Sound

end KAM.CertificateSharp.Packed
