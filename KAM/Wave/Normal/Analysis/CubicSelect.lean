/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib.Topology.Algebra.InfiniteSum.Real
public import Mathlib.Analysis.Normed.Ring.InfiniteSum
public import KAM.Wave.Normal.Analysis.SelectionRule
public import KAM.Wave.Normal.Analysis.EvenMajorant

/-!
# Selection-rule majorant by a triple convolution
(blueprint `bpW:w0n:cubic-bound`, step `stepW:w0n:selection`)

Infrastructure used by several nodes; the dependency graph is still being built.

For nonnegative, even, summable `x y z : ℤ → ℝ`, the sum over `(i, j, k) ∈ ℕ+³` weighted by the
number `N(i,j,k;l) = #{ε ∈ {±1}³ : l = ε₁ i + ε₂ j + ε₃ k}` of selection-rule patterns satisfies
`Σ_{ijk} N · x_i y_j z_k ≤ ((x * y) * z)_l`
(`KAM.Wave.wave_selection_sum_le`): the map `(ε, i, j, k) ↦ (ε₃ k, ε₂ j, ε₁ i)` is injective into
`ℤ³` and `x`, `y`, `z` are even.
-/

@[expose] public noncomputable section

namespace KAM.Wave

lemma wave_summable_triple {ι κ μ : Type*} {f : ι → ℝ} {g : κ → ℝ} {h : μ → ℝ}
    (hf : Summable fun i => |f i|) (hg : Summable fun i => |g i|) (hh : Summable fun i => |h i|) :
    Summable (fun t : ι × κ × μ => f t.1 * (g t.2.1 * h t.2.2)) ∧
      Summable (fun t : ι × κ × μ => |f t.1 * (g t.2.1 * h t.2.2)|) := by
  have hf' : Summable fun i => ‖f i‖ := hf
  have hg' : Summable fun i => ‖g i‖ := hg
  have hh' : Summable fun i => ‖h i‖ := hh
  have h2n : Summable fun p : κ × μ => ‖g p.1 * h p.2‖ := by
    refine (hg'.mul_norm hh').congr fun p => ?_
    simp
  have h3n : Summable fun t : ι × κ × μ => ‖f t.1 * (g t.2.1 * h t.2.2)‖ := by
    refine (hf'.mul_norm h2n).congr fun p => ?_
    simp
  exact ⟨(summable_mul_of_summable_norm hf' h2n), h3n⟩

lemma waveSign_mul_inj {b b' : Bool} {n n' : ℕ+}
    (h : waveSign b * ((n : ℕ) : ℤ) = waveSign b' * ((n' : ℕ) : ℤ)) : b = b' ∧ n = n' := by
  have hn := n.pos
  have hn' := n'.pos
  cases b <;> cases b' <;>
    simp only [waveSign, boolSign, Bool.false_eq_true, ite_true, ite_false] at h
  · exact ⟨rfl, PNat.coe_injective (by omega)⟩
  · omega
  · omega
  · exact ⟨rfl, PNat.coe_injective (by omega)⟩

/-- The embedding `(ε, (i, j, k)) ↦ (ε₃ k, ε₂ j, ε₁ i)` into `ℤ³`. -/
def waveSignedEmb (p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+)) : ℤ × ℤ × ℤ :=
  (waveSign p.1.2.2 * ((p.2.2.2 : ℕ) : ℤ), waveSign p.1.2.1 * ((p.2.2.1 : ℕ) : ℤ),
    waveSign p.1.1 * ((p.2.1 : ℕ) : ℤ))

lemma waveSignedEmb_injective : Function.Injective waveSignedEmb := by
  rintro ⟨⟨e1, e2, e3⟩, i, j, k⟩ ⟨⟨f1, f2, f3⟩, i', j', k'⟩ h
  simp only [waveSignedEmb, Prod.mk.injEq] at h
  obtain ⟨h3, h2, h1⟩ := h
  obtain ⟨a1, b1⟩ := waveSign_mul_inj h1
  obtain ⟨a2, b2⟩ := waveSign_mul_inj h2
  obtain ⟨a3, b3⟩ := waveSign_mul_inj h3
  subst a1 a2 a3 b1 b2 b3
  rfl

lemma even_apply_waveSign {x : ℤ → ℝ} (hxe : ∀ i, x (-i) = x i) (b : Bool) (n : ℤ) :
    x (waveSign b * n) = x n := by
  cases b
  · simp [waveSign, boolSign, hxe]
  · simp [waveSign, boolSign]

theorem wave_selection_sum_le {x y z : ℤ → ℝ}
    (hx0 : ∀ i, 0 ≤ x i) (hy0 : ∀ i, 0 ≤ y i) (hz0 : ∀ i, 0 ≤ z i)
    (hxe : ∀ i, x (-i) = x i) (hye : ∀ i, y (-i) = y i) (hze : ∀ i, z (-i) = z i)
    (hx1 : Summable x) (hy1 : Summable y) (hz1 : Summable z) (l : ℕ+) :
    Summable (fun t : ℕ+ × ℕ+ × ℕ+ =>
      (∑ ε : Bool × Bool × Bool,
        (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)) *
        (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)))) ∧
    ∑' t : ℕ+ × ℕ+ × ℕ+,
      (∑ ε : Bool × Bool × Bool,
        (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)) *
        (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)))
      ≤ w0aConv (w0aConv x y) z ((l : ℕ) : ℤ) := by
  have hx1' : Summable fun i => |x i| := hx1.abs
  have hy1' : Summable fun i => |y i| := hy1.abs
  have hz1' : Summable fun i => |z i| := hz1.abs
  have inj : Function.Injective (fun n : ℕ+ => ((n : ℕ) : ℤ)) := fun a b h => by
    have h' : ((a : ℕ) : ℤ) = ((b : ℕ) : ℤ) := h
    exact PNat.coe_injective (by exact_mod_cast h')
  have hxp : Summable fun n : ℕ+ => |x ((n : ℕ) : ℤ)| := hx1'.comp_injective inj
  have hyp : Summable fun n : ℕ+ => |y ((n : ℕ) : ℤ)| := hy1'.comp_injective inj
  have hzp : Summable fun n : ℕ+ => |z ((n : ℕ) : ℤ)| := hz1'.comp_injective inj
  have hP := (wave_summable_triple hxp hyp hzp).1
  -- the terms for a fixed sign pattern
  set F : (Bool × Bool × Bool) → ℕ+ × ℕ+ × ℕ+ → ℝ := fun ε t =>
    (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0) *
        (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ))) with hF
  have hPnn : ∀ t : ℕ+ × ℕ+ × ℕ+, 0 ≤ x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) :
      ℤ)) :=
    fun t => mul_nonneg (hx0 _) (mul_nonneg (hy0 _) (hz0 _))
  have hFnn : ∀ ε t, 0 ≤ F ε t := fun ε t => by
    simp only [hF]
    split_ifs
    · rw [one_mul]; exact hPnn t
    · rw [zero_mul]
  have hFle : ∀ ε t, F ε t ≤ x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)) :=
    fun ε t => by
      simp only [hF]
      split_ifs
      · rw [one_mul]
      · rw [zero_mul]; exact hPnn t
  have hFsum : ∀ ε, Summable (F ε) := fun ε =>
    Summable.of_nonneg_of_le (hFnn ε) (hFle ε) hP
  have hN : ∀ t : ℕ+ × ℕ+ × ℕ+,
      (∑ ε : Bool × Bool × Bool,
        (if ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ) then (1 : ℝ) else 0)) *
        (x ((t.1 : ℕ) : ℤ) * (y ((t.2.1 : ℕ) : ℤ) * z ((t.2.2 : ℕ) : ℤ)))
      = ∑ ε : Bool × Bool × Bool, F ε t := fun t => by
    simp only [hF, Finset.sum_mul]
  simp only [hN]
  refine ⟨summable_sum fun ε _ => hFsum ε, ?_⟩
  rw [Summable.tsum_finsetSum (s := Finset.univ) (fun ε _ => hFsum ε)]
  -- reindex into `ℤ³`
  set G : ℤ × ℤ × ℤ → ℝ := fun p =>
    if p.2.2 = ((l : ℕ) : ℤ) - p.1 - p.2.1 then x p.2.2 * (y p.2.1 * z p.1) else 0 with hG
  have hG0 : ∀ p, 0 ≤ G p := fun p => by
    simp only [hG]
    split_ifs
    · exact mul_nonneg (hx0 _) (mul_nonneg (hy0 _) (hz0 _))
    · exact le_rfl
  have hGsum : Summable G := by
    refine Summable.of_nonneg_of_le hG0 (fun p => ?_)
      (wave_summable_triple hz1' hy1' hx1').1
    simp only [hG]
    split_ifs
    · exact le_of_eq (by ring)
    · exact mul_nonneg (hz0 _) (mul_nonneg (hy0 _) (hx0 _))
  have hFG : ∀ ε t, F ε t = G (waveSignedEmb (ε, t)) := by
    intro ε t
    simp only [hF, hG, waveSignedEmb]
    rw [even_apply_waveSign hxe, even_apply_waveSign hye, even_apply_waveSign hze]
    have hiff : (((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ)) ↔
        (waveSign ε.1 * ((t.1 : ℕ) : ℤ) = ((l : ℕ) : ℤ) - waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ)
          - waveSign ε.2.1 * ((t.2.1 : ℕ) : ℤ)) := by omega
    by_cases hc : ((l : ℕ) : ℤ) = waveSign ε.1 * ((t.1 : ℕ) : ℤ) + waveSign ε.2.1 * ((t.2.1 : ℕ) :
        ℤ)
          + waveSign ε.2.2 * ((t.2.2 : ℕ) : ℤ)
    · rw [if_pos hc, if_pos (hiff.1 hc)]; ring
    · rw [if_neg hc, if_neg (fun h => hc (hiff.2 h))]; ring
  have hFG' : ∀ ε, ∑' t, F ε t = ∑' t, G (waveSignedEmb (ε, t)) := fun ε => tsum_congr (hFG ε)
  simp only [hFG']
  have hGc : Summable fun p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+) => G (waveSignedEmb p) :=
    hGsum.comp_injective waveSignedEmb_injective
  have hprod : ∑' p : (Bool × Bool × Bool) × (ℕ+ × ℕ+ × ℕ+), G (waveSignedEmb p)
      = ∑ ε : Bool × Bool × Bool, ∑' t, G (waveSignedEmb (ε, t)) := by
    rw [hGc.tsum_prod' (fun ε => hGc.prod_factor ε), tsum_fintype]
  rw [← hprod]
  refine (tsum_comp_le_tsum_of_inj hGsum hG0 waveSignedEmb_injective).trans (le_of_eq ?_)
  have hG' : ∀ c b : ℤ, ∑' a : ℤ, G (c, b, a) = x (((l : ℕ) : ℤ) - c - b) * (y b * z c) := by
    intro c b
    rw [tsum_eq_single (((l : ℕ) : ℤ) - c - b) (fun a ha => by simp [hG, ha])]
    simp [hG]
  rw [hGsum.tsum_prod]
  unfold w0aConv
  refine tsum_congr fun c => ?_
  rw [(hGsum.prod_factor c).tsum_prod]
  simp only [hG']
  rw [← tsum_mul_right]
  refine tsum_congr fun b => ?_
  ring

end KAM.Wave

end
