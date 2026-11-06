/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.EffectiveStability.SJSU.Check.TailAcc
public import KAM.EffectiveStability.SJSU.Ham.HtBridge

/-!
# Row weights of `H_w` over common denominators (T2-CONF, N9 (C))

`sjsuRowW`, `sjsuRowWp` (rational row weights), their integer forms `sjsuRowWZ`, `sjsuRowWpZ` over
the degree-`d` denominator `sjsuDen d` (`sjsuRowW_eq`), and `sjsu_block_le`: integer block sums
(N6's balanced `treeSumQ`: a `List.sum` of 3,025 rows exceeds the kernel's depth) give the
rational block bounds.
-/

@[expose] public section

namespace KAM.EffectiveStability.SJSU

open KAM.EffectiveStability.Tube

/-- The row weight `|c| Π_j hi_j^{n_j}` of a row of `H_w`, in `ℚ`. -/
def sjsuRowW (e : (Mon × Mon) × ℤ) : ℚ :=
  |rowCoefQ sjsuE sjsuN e| * ∏ j, sjsuTailHi j ^ rowExp e j

/-- The row weight `|c| (|k₀| + |k₁|) Π_j hi_j^{n_j}`, in `ℚ`. -/
def sjsuRowWp (e : (Mon × Mon) × ℤ) : ℚ :=
  |rowCoefQ sjsuE sjsuN e| * (|((rowMode e).1 : ℚ)| + |((rowMode e).2 : ℚ)|) *
    ∏ j, sjsuTailHi j ^ rowExp e j

/-! ### The row weights in integers

On the block of degree `d` the denominators are common: `|rowCoefQ| = |c| / (10^E N^{2d})` and, with
`hi_j = M_j / 10^6`, `Π_j hi_j^{n_j} = Π_j M_j^{n_j} / 10^{12 d}`. The kernel sums the integers
`|c| Π_j M_j^{n_j}` (power tables, N6's balanced `treeSumQ`: a `List.sum` of 3,025 rows exceeds the
kernel's depth) and compares once. -/

/-- `19150^k`, `k ≤ 18`. -/
def sjsuPw0 : List ℕ := [
  1,
  19150,
  366722500,
  7022735875000,
  134485392006250000,
  2575395256919687500000,
  49318819170012015625000000,
  944455387105730099218750000000,
  18086320663074731400039062500000000,
  346353040697881106310748046875000000000,
  6632660729364423185850825097656250000000000,
  127015452967328704009043300620117187500000000000,
  2432345924324344681773179206875244140625000000000000,
  46579424450811200655956381811660925292968750000000000000,
  891995978233034492561564711693306719360351562500000000000000,
  17081722983162610532553964228926823675750732421875000000000000000,
  327114995127563991698408414983948673390626525878906250000000000000000,
  6264252156692850441024521146942617095430497970581054687500000000000000000,
  119960428800668085945619579963951117377494036136627197265625000000000000000000]

/-- `26980^k`, `k ≤ 18`. -/
def sjsuPw1 : List ℕ := [
  1,
  26980,
  727920400,
  19639292392000,
  529868108736160000,
  14295841573701596800000,
  385701805658469081664000000,
  10406234716665495823294720000000,
  280760212655635077312491545600000000,
  7574910537449034385891021900288000000000,
  204371086300374947731339770869770240000000000,
  5513931908384116089791547018066401075200000000000,
  148765882888203452102575938547431501008896000000000000,
  4013703520323729137727498822009701897220014080000000000000,
  108289720978334212135887918217821757186995979878400000000000000,
  2921656671995457043426256033516831008905151537119232000000000000000,
  78826297010437431031640387784284100620260988471476879360000000000000000,
  2126733493341601889233657662419985034734641468960446205132800000000000000000,
  57379269650356418971524083732091196237140626832552838614482944000000000000000000]

/-- `5813^k`, `k ≤ 18`. -/
def sjsuPw2 : List ℕ := [
  1,
  5813,
  33790969,
  196426902797,
  1141829585958961,
  6637455383179440293,
  38583528142422086423209,
  224286049091899588378113917,
  1303774803371212307241976199521,
  7578842931996857141997607647815573,
  44055813963697730566432093256751925849,
  256096446570974907782669758101498944960237,
  1488688643917077138940659303844013367053857681,
  8653747087089969408662052533245249702684074699653,
  50304231817253992172552511375754636521702526229082889,
  292418499553697456499047748627261702100656784969658833757,
  1699828737905643314628964562770272274311117891028626800629441,
  9881104453445504587938171003383592730570528300549407592058940533,
  57438860187878718169684588042668824542806481011093706332638621318329]

theorem sjsuPw_ok : ∀ k < 19, sjsuPw0.getD k 0 = 19150 ^ k ∧ sjsuPw1.getD k 0 = 26980 ^ k ∧
    sjsuPw2.getD k 0 = 5813 ^ k := by
  decide +kernel

theorem sjsuTailHi_eq : sjsuTailHi = ![19150 / 10 ^ 6, 26980 / 10 ^ 6, 5813 / 10 ^ 6] := by
  funext j; fin_cases j <;> simp [sjsuTailHi] <;> norm_num

/-- `|c| Π_j M_j^{n_j}`. -/
def sjsuRowWZ (e : (Mon × Mon) × ℤ) : ℕ :=
  e.2.natAbs * sjsuPw0.getD (e.1.1.1 + e.1.2.1) 0 * sjsuPw1.getD (e.1.1.2.1 + e.1.2.2.1) 0 *
    sjsuPw2.getD (e.1.1.2.2 + e.1.2.2.2) 0

/-- `|c| (|k₀| + |k₁|) Π_j M_j^{n_j}`. -/
def sjsuRowWpZ (e : (Mon × Mon) × ℤ) : ℕ :=
  sjsuRowWZ e * ((rowMode e).1.natAbs + (rowMode e).2.natAbs)

/-- The common denominator of the degree-`d` block. -/
def sjsuDen (d : ℕ) : ℚ := 10 ^ sjsuE * (sjsuN : ℚ) ^ (2 * d) * 10 ^ (12 * d)

theorem sjsuDen_pos (d : ℕ) : 0 < sjsuDen d := by
  unfold sjsuDen; have : (0 : ℚ) < sjsuN := by norm_num [sjsuN]
  positivity

/-- **The row weights over the common denominator.** -/
theorem sjsuRowW_eq {e : (Mon × Mon) × ℤ} {d : ℕ} (hd : d ≤ 9) (hb : Mon.deg e.1.1 = d)
    (hb' : Mon.deg e.1.2 = d) :
    sjsuRowW e = (sjsuRowWZ e : ℚ) / sjsuDen d ∧
      sjsuRowWp e = (sjsuRowWpZ e : ℚ) / sjsuDen d := by
  simp only [Mon.deg] at hb hb'
  have h0 : e.1.1.1 + e.1.2.1 < 19 := by omega
  have h1 : e.1.1.2.1 + e.1.2.2.1 < 19 := by omega
  have h2 : e.1.1.2.2 + e.1.2.2.2 < 19 := by omega
  have p0 := (sjsuPw_ok _ h0).1
  have p1 := (sjsuPw_ok _ h1).2.1
  have p2 := (sjsuPw_ok _ h2).2.2
  have hN : (0 : ℚ) < sjsuN := by norm_num [sjsuN]
  have hna : ∀ n : ℤ, ((n.natAbs : ℕ) : ℚ) = |(n : ℚ)| := fun n => by
    rw [← Int.cast_natCast, Int.natCast_natAbs, Int.cast_abs]
  have hdeg : Mon.deg e.1.1 + Mon.deg e.1.2 = 2 * d := by simp only [Mon.deg]; omega
  have hsum : (e.1.1.1 + e.1.2.1) + (e.1.1.2.1 + e.1.2.2.1) + (e.1.1.2.2 + e.1.2.2.2) = 2 * d := by
    omega
  have hW : sjsuRowW e = (sjsuRowWZ e : ℚ) / sjsuDen d := by
    rw [sjsuRowW, sjsuRowWZ, rowCoefQ, hdeg, sjsuTailHi_eq, p0, p1, p2, sjsuDen, abs_div,
      Fin.prod_univ_three]
    simp only [rowExp, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
      Matrix.head_cons, Matrix.tail_cons]
    rw [abs_of_pos (mul_pos (pow_pos (by norm_num) _) (pow_pos hN _)), ← hsum]
    push_cast
    rw [hna]
    simp only [div_pow, pow_add]
    field_simp
    rw [show 12 * d = 6 * (e.1.1.1 + e.1.2.1) + 6 * (e.1.1.2.1 + e.1.2.2.1) +
      6 * (e.1.1.2.2 + e.1.2.2.2) by omega]
    simp only [pow_add, pow_mul]
    ring
  refine ⟨hW, ?_⟩
  rw [sjsuRowWp, sjsuRowWpZ]
  have : sjsuRowWp e = sjsuRowW e * (|((rowMode e).1 : ℚ)| + |((rowMode e).2 : ℚ)|) := by
    rw [sjsuRowWp, sjsuRowW]; ring
  rw [← sjsuRowWp, this, hW]
  push_cast
  rw [hna, hna]
  ring

theorem list_sum_div_const {α : Type*} (l : List α) (F : α → ℚ) (c : ℚ) :
    (l.map fun e => F e / c).sum = (l.map F).sum / c := by
  simp only [div_eq_mul_inv]; exact List.sum_map_mul_right _ _ _

/-- The block sums from the integer sums. -/
theorem sjsu_block_le {d : ℕ} (hd : d ≤ 9)
    (hdeg : ∀ e ∈ sjsuHw d, Mon.deg e.1.1 = d ∧ Mon.deg e.1.2 = d)
    {W Wp : ℚ} (hZ : treeSumQ 64 ((sjsuHw d).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)) ≤ W * sjsuDen d)
    (hZp : treeSumQ 64 ((sjsuHw d).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)) ≤ Wp * sjsuDen d) :
    ((sjsuHw d).map sjsuRowW).sum ≤ W ∧ ((sjsuHw d).map sjsuRowWp).sum ≤ Wp := by
  rw [treeSumQ_eq] at hZ hZp
  have hD := sjsuDen_pos d
  have e1 : ((sjsuHw d).map sjsuRowW).sum =
      ((sjsuHw d).map fun e => ((sjsuRowWZ e : ℕ) : ℚ)).sum / sjsuDen d := by
    rw [← list_sum_div_const]
    exact congrArg List.sum (List.map_congr_left fun e he =>
      (sjsuRowW_eq hd (hdeg e he).1 (hdeg e he).2).1)
  have e2 : ((sjsuHw d).map sjsuRowWp).sum =
      ((sjsuHw d).map fun e => ((sjsuRowWpZ e : ℕ) : ℚ)).sum / sjsuDen d := by
    rw [← list_sum_div_const]
    exact congrArg List.sum (List.map_congr_left fun e he =>
      (sjsuRowW_eq hd (hdeg e he).1 (hdeg e he).2).2)
  rw [e1, e2, div_le_iff₀ hD, div_le_iff₀ hD]
  exact ⟨hZ, hZp⟩

end KAM.EffectiveStability.SJSU

end
