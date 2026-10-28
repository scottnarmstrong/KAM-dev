/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.ODE.Continuation
public import KAM.ODE.Maximal
public import KAM.ODE.UniformPeriodic
public import KAM.Nekhoroshev.Partial.Setting

/-!
# Continuation with independent periodic and transverse coordinates (`bpN:p11:continuation`)

A `C¹` field on `ℝⁿ × U` (`U ⊆ ℝᴺ` open), `ℤⁿ`-periodic in the first factor, has uniform data on
`ℝⁿ × K` for every compact `K ⊆ U`; hence a maximal solution whose transverse part stays in such a
`K` near the right end of its interval has `T₊ = ∞`.  This is the proof of
`KAM.ODE.gen_continuation_periodic` with the transverse dimension `N` independent of `n`.
-/

@[expose] public noncomputable section

open Set Metric
open scoped NNReal ContDiff

namespace KAM.Nekhoroshev

variable {n N : ℕ}

/-- Uniform data on `ℝⁿ × K` for an angle-periodic field with independent transverse dimension
(`stepN:p11:ct-data`). -/
private theorem uniform_data_periodic {U : Set (Fin N → ℝ)}
    {F : (Fin n → ℝ) × (Fin N → ℝ) → (Fin n → ℝ) × (Fin N → ℝ)} (hU : IsOpen U)
    (hF : ContDiffOn ℝ 1 F (univ ×ˢ U))
    (hper : ∀ ℓ : Fin n → ℤ, ∀ z ∈ (univ : Set (Fin n → ℝ)) ×ˢ U,
      F (z.1 + (fun i => (ℓ i : ℝ)), z.2) = F z)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U) :
    ∃ (δ M : ℝ) (L : ℝ≥0), δ ≤ 1 ∧
      KAM.ODE.UniformData F (univ ×ˢ U) (univ ×ˢ K) δ M L := by
  obtain ⟨δ₀, hδ₀, hsub⟩ := hK.exists_cthickening_subset_open hU hKU
  have hδpos : 0 < min δ₀ 1 := lt_min hδ₀ one_pos
  have hδ1 : min δ₀ 1 ≤ 1 := min_le_right _ _
  set δ := min δ₀ 1 with hδ
  have hT : cthickening δ K ⊆ U := (cthickening_mono (min_le_left _ _) K).trans hsub
  have hTc : IsCompact (cthickening δ K) := hK.cthickening
  have hCc : IsCompact (Icc (-1 : Fin n → ℝ) 2 ×ˢ cthickening δ K) := isCompact_Icc.prod hTc
  have hCW : Icc (-1 : Fin n → ℝ) 2 ×ˢ cthickening δ K ⊆ univ ×ˢ U :=
    fun p hp => ⟨mem_univ _, hT hp.2⟩
  obtain ⟨⟨M, hM0, hM⟩, L, hL⟩ := KAM.ODE.gen_lip (isOpen_univ.prod hU) hF hCc hCW
  have key : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ K, ∀ y ∈ closedBall x δ,
      (y.1 - (fun i => ((⌊x.1 i⌋ : ℤ) : ℝ)), y.2) ∈
        Icc (-1 : Fin n → ℝ) 2 ×ˢ cthickening δ K ∧ y.2 ∈ cthickening δ K := by
    intro x hx y hy
    rw [mem_closedBall_iff_norm, Prod.norm_def] at hy
    have h2 : y.2 ∈ cthickening δ K := by
      apply closedBall_subset_cthickening hx.2 δ
      rw [mem_closedBall_iff_norm]
      exact (le_max_right _ _).trans hy
    have h1 : ∀ i, |y.1 i - x.1 i| ≤ δ := fun i => by
      have := norm_le_pi_norm (y.1 - x.1) i
      simp only [Pi.sub_apply, Real.norm_eq_abs] at this
      exact this.trans ((le_max_left _ _).trans hy)
    refine ⟨⟨⟨Pi.le_def.2 fun i => ?_, Pi.le_def.2 fun i => ?_⟩, h2⟩, h2⟩
    · have := abs_le.1 ((h1 i).trans hδ1)
      have h3 := Int.floor_le (x.1 i)
      simp only [Pi.sub_apply, Pi.neg_apply, Pi.one_apply]
      linarith [this.1]
    · have := abs_le.1 ((h1 i).trans hδ1)
      have h3 := Int.lt_floor_add_one (x.1 i)
      simp only [Pi.sub_apply, Pi.ofNat_apply]
      linarith [this.2]
  have hshift : ∀ x ∈ (univ : Set (Fin n → ℝ)) ×ˢ K, ∀ y ∈ closedBall x δ,
      F y = F (y.1 - (fun i => ((⌊x.1 i⌋ : ℤ) : ℝ)), y.2) := by
    intro x hx y hy
    have hy' := (key x hx y hy).1
    have := hper (fun i => ⌊x.1 i⌋) _ (hCW hy')
    simpa using this
  have hdist : ∀ x : (Fin n → ℝ) × (Fin N → ℝ), ∀ a b : (Fin n → ℝ) × (Fin N → ℝ),
      edist (a.1 - (fun i => ((⌊x.1 i⌋ : ℤ) : ℝ)), a.2) (b.1 - (fun i => ((⌊x.1 i⌋ : ℤ) : ℝ)), b.2)
        = edist a b := fun x a b => by
    simp [Prod.edist_eq, edist_sub_right]
  refine ⟨δ, M, L, hδ1, hδpos, hM0, fun x hx y hy => ⟨mem_univ _, hT ?_⟩, fun x hx y hy => ?_,
    fun x hx => ?_⟩
  · exact (key x hx y hy).2
  · rw [hshift x hx y hy]
    exact hM _ (key x hx y hy).1
  · intro a ha b hb
    rw [hshift x hx a ha, hshift x hx b hb]
    have := hL (key x hx a ha).1 (key x hx b hb).1
    rwa [hdist] at this

theorem continuation {U : Set (Fin N → ℝ)} (hU : IsOpen U)
    {F : (Fin n → ℝ) × (Fin N → ℝ) → (Fin n → ℝ) × (Fin N → ℝ)}
    (hF : ContDiffOn ℝ 1 F (univ ×ˢ U))
    (hper : ∀ ℓ : Fin n → ℤ, ∀ z ∈ (univ : Set (Fin n → ℝ)) ×ˢ U,
      F (z.1+(fun i => (ℓ i:ℝ)),z.2) = F z)
    {z0 : (Fin n → ℝ) × (Fin N → ℝ)} {Tm Tp : EReal} {z : ℝ → (Fin n → ℝ) × (Fin N → ℝ)}
    (hz : KAM.ODE.IsMaximalSolution F (univ ×ˢ U) z0 Tm Tp z)
    {K : Set (Fin N → ℝ)} (hK : IsCompact K) (hKU : K ⊆ U)
    (hconf : ∃ t0 : ℝ, 0 ≤ t0 ∧ (t0:EReal) < Tp ∧
      ∀ t : ℝ, t0 ≤ t → (t:EReal) < Tp → (z t).2 ∈ K) : Tp = ⊤ := by
  obtain ⟨δ, M, L, -, hΦ⟩ := uniform_data_periodic hU hF hper hK hKU
  refine (KAM.ODE.gen_continuation (isOpen_univ.prod hU) hF hz hΦ).1 ?_
  obtain ⟨t0, h0, h1, h2⟩ := hconf
  exact ⟨t0, h0, h1, fun t ht htT => ⟨mem_univ _, h2 t ht htT⟩⟩

end KAM.Nekhoroshev

end
