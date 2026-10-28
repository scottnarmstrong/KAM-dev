/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.LimitMap
public import KAM.Planetary.TwoScale.StepConst
public import KAM.Planetary.TwoScale.MeasureTorus

/-!
# Two-scale KAM: applicability of the measure helpers (design finding N2, package P23-21)

`actionsMeas_of_limit` and `torusMeas_of_limit` build the bundles `ActionsMeas`/`TorusMeas` from
the exact clause shapes of `two_scale_kam` for the limit action map `i` and the limit map `Φ`
(block displacements, defect Lipschitz constants, rescaled displacement of `Φ`), using only
`KamHyp`. `ko_eq` identifies `K_Ω = ⋃ ω ∈ Ω, range (K ω)` with `Φ(ℝⁿ × D_*)` from the clause
`I₀ : Ω → D₀`. `meas_torus_final` is the resulting clause of `two_scale_kam`, with exact constant
`complementConstant`. `meas_of_iterative` is the joint check: on the witnesses of one application
of `iterative`, `limit_actions_of_steps` and `limit_phi_real_of_steps` feed these constructors.
-/

@[expose] public noncomputable section

open Set Metric Real Filter Topology MeasureTheory

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

variable {a b : ℕ} {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
  {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)}

theorem KamHyp.kam_small_n (H : KamHyp D sbar p h f) :
    8192 * ((a + b : ℕ) : ℝ) * eHat p < 1 := by
  have h0 := H.eHat_nonneg
  have hk : 2 ^ 13 * ((a + b : ℕ) : ℝ) ≤ kamConstant (a + b) p.τ := le_max_left _ _
  have := H.small
  nlinarith [mul_le_mul_of_nonneg_right hk h0]

theorem KamHyp.mbar_div_le (H : KamHyp D sbar p h f) :
    p.Mbar₁ / p.Mbar ≤ 1 ∧ p.Mbar₂ / p.Mbar ≤ 1 ∧ p.Mhat / p.M ≤ 1 := by
  have hp := H.positive
  have hn := H.normalized
  exact ⟨(div_le_one hp.2.2.2.2.2.2.1).2 hn.2.1, (div_le_one hp.2.2.2.2.2.2.1).2 hn.2.2,
    (div_le_one hp.2.2.2.2.1).2 hn.1⟩

/-- `ActionsMeas` for the limit action map, from the clauses of `two_scale_kam`. -/
theorem actionsMeas_of_limit (H : KamHyp D sbar p h f) {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)}
    (hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    (hlip : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖) :
    ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p) := by
  have he := H.eHat_nonneg
  have hR := H.R_pos
  obtain ⟨m1, m2, -⟩ := H.mbar_div_le
  have hk := H.kam_small_n
  have hERnn : 0 ≤ eHat p * rhoHat p := by positivity
  refine ⟨inter_subset_left, he, mul_pos (eHat_pos H) hR, fun I hI => ?_, fun I hI J hJ => ?_, ?_⟩
  · obtain ⟨b1, b2⟩ := hblk I hI
    refine norm_le_of_blocks (by positivity) (b1.trans ?_) (b2.trans ?_)
    · calc _ = (p.Mbar₁ / p.Mbar) * (20 * (eHat p * rhoHat p)) := by ring
        _ ≤ 1 * (20 * (eHat p * rhoHat p)) := by gcongr
        _ = _ := by ring
    · calc _ = (p.Mbar₂ / p.Mbar) * (20 * (eHat p * rhoHat p)) := by ring
        _ ≤ 1 * (20 * (eHat p * rhoHat p)) := by gcongr
        _ = _ := by ring
  · have := hlip I hI J hJ
    rw [Nat.cast_add]; exact this
  · rw [Nat.cast_add] at hk ⊢
    nlinarith

/-- `TorusMeas` for the limit map, from the clauses of `two_scale_kam` and the rescaled
displacement of `limit_phi_real_of_steps`. -/
theorem torusMeas_of_limit (H : KamHyp D sbar p h f)
    {i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φ : Phase (a + b) → Phase (a + b)}
    (hacts : ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p))
    (hlip : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
        768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y))
    (hsup : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ‖firstBlock (b := b) ((Φ x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φ x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
      2 * π * ‖(Φ x - x).1‖ ≤ 3 / 2 * eHat p * p.s) :
    TorusMeas D (dioBase D h p) i Φ (eHat p) (rhoHat p) p.s := by
  have he := H.eHat_nonneg
  have hR := H.R_pos
  have hs := H.positive.2.1
  obtain ⟨-, -, m3⟩ := H.mbar_div_le
  have hk := H.kam_small_n
  have hn : (0 : ℝ) ≤ ((a + b : ℕ) : ℝ) := Nat.cast_nonneg _
  refine ⟨hacts, hR, hs, ?_, (H.eHat_lt_small).le.trans (by norm_num), ?_, ?_, fun x hx => ?_⟩
  · have := H.widths; linarith [this.1, this.2]
  · intro x hx y hy
    have := hlip x hx y hy
    rw [Nat.cast_add]; exact this
  · nlinarith
  · obtain ⟨s1, s2, s3⟩ := hsup x hx
    unfold limitmap_data
    refine max_le ?_ ?_
    · rw [mul_div_assoc', div_le_iff₀ hs]
      nlinarith
    · rw [div_le_iff₀ hR]
      have hv : ‖(Φ x - x).2‖ ≤ 3 / 2 * eHat p * rhoHat p := by
        refine norm_le_of_blocks (by positivity) (s1.trans ?_) s2
        calc _ = (p.Mhat / p.M) * (3 / 2 * (eHat p * rhoHat p)) := by ring
          _ ≤ 1 * (3 / 2 * (eHat p * rhoHat p)) := by gcongr
          _ = _ := by ring
      nlinarith

/-- `K_Ω = ⋃ ω ∈ Ω, range (K ω)` equals `Φ(ℝⁿ × D_*)` when `ω ↦ I₀ ω` maps `Ω` onto `D₀`. -/
theorem ko_eq {n : ℕ} {Ω D₀ : Set (Fin n → ℝ)} {I₀ i : (Fin n → ℝ) → (Fin n → ℝ)}
    {Φ : Phase n → Phase n} {K : (Fin n → ℝ) → (Fin n → ℝ) → Phase n}
    (hK : ∀ ω ∈ Ω, ∀ θ, K ω θ = Φ (θ, i (I₀ ω)))
    (hI : ∀ ω ∈ Ω, I₀ ω ∈ D₀) (hsurj : ∀ I ∈ D₀, ∃ ω ∈ Ω, I₀ ω = I) :
    (⋃ ω ∈ Ω, range (K ω)) = Φ '' (univ ×ˢ (i '' D₀)) := by
  ext y
  simp only [mem_iUnion, mem_range, mem_image, mem_prod, mem_univ, true_and]
  constructor
  · rintro ⟨ω, hω, θ, rfl⟩
    exact ⟨(θ, i (I₀ ω)), ⟨I₀ ω, hI ω hω, rfl⟩, (hK ω hω θ).symm⟩
  · rintro ⟨⟨θ, J⟩, ⟨I, hI', rfl⟩, rfl⟩
    obtain ⟨ω, hω, rfl⟩ := hsurj I hI'
    exact ⟨ω, hω, θ, hK ω hω θ⟩

/-- The clause `I₀ : Ω → D₀` of `two_scale_kam` makes `I₀` surjective onto `D₀ = dioBase`. -/
theorem exists_omega {I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)}
    (hI₀ : ∀ ω ∈ omegaSet D h p, I₀ ω ∈ dioBase D h p ∧ realFreq h (I₀ ω) = ω ∧
      ∀ I ∈ dioBase D h p, realFreq h I = ω → I = I₀ ω) :
    ∀ I ∈ dioBase D h p, ∃ ω ∈ omegaSet D h p, I₀ ω = I := by
  intro I hI
  refine ⟨realFreq h I, ⟨⟨I, hI.1, rfl⟩, hI.2⟩, ?_⟩
  exact ((hI₀ _ ⟨⟨I, hI.1, rfl⟩, hI.2⟩).2.2 I hI rfl).symm

/-- **`bpP:p3:meas-torus`**, in the exact shape of the last clause of `two_scale_kam`: with
`D₀ = dioBase D h p`, `Ω = omegaSet D h p`, `r = 32 Ê ρ̂` and `K_Ω = ⋃ ω ∈ Ω, range (K ω)`, the
complement of `K_Ω` in the angle cell over `realTube D r` has measure at most
`complementConstant (a + b) · (meas(D ∖ D₀) + meas(realTube D r ∖ D))`. Private conditional
helper on the clause data of the same witnesses `i, I₀, Φ, K`. -/
theorem meas_torus_final (H : KamHyp D sbar p h f)
    {i I₀ : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ)} {Φ : Phase (a + b) → Phase (a + b)}
    {K : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ) → Phase (a + b)}
    (hblk : ∀ I ∈ dioBase D h p,
      ‖firstBlock (b := b) (i I - I)‖ ≤ 20 * (p.Mbar₁ / p.Mbar) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) (i I - I)‖ ≤ 20 * (p.Mbar₂ / p.Mbar) * eHat p * rhoHat p)
    (hlipI : ∀ I ∈ dioBase D h p, ∀ J ∈ dioBase D h p,
      ‖(i I - I) - (i J - J)‖ ≤ 2560 * (a + b) * eHat p * ‖I - J‖)
    (hlipΦ : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ∀ y ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      limitmap_data (rhoHat p) p.s ((Φ x - x) - (Φ y - y)) ≤
        768 * (a + b) * eHat p * limitmap_data (rhoHat p) p.s (x - y))
    (hsup : ∀ x ∈ (univ ×ˢ (i '' dioBase D h p) : Set (Phase (a + b))),
      ‖firstBlock (b := b) ((Φ x - x).2)‖ ≤ 3 / 2 * (p.Mhat / p.M) * eHat p * rhoHat p ∧
      ‖lastBlock (a := a) ((Φ x - x).2)‖ ≤ 3 / 2 * eHat p * rhoHat p ∧
      2 * π * ‖(Φ x - x).1‖ ≤ 3 / 2 * eHat p * p.s)
    (hI₀ : ∀ ω ∈ omegaSet D h p, I₀ ω ∈ dioBase D h p ∧ realFreq h (I₀ ω) = ω ∧
      ∀ I ∈ dioBase D h p, realFreq h I = ω → I = I₀ ω)
    (hK : ∀ ω ∈ omegaSet D h p, ∀ θ, K ω θ = Φ (θ, i (I₀ ω))) :
    volume (((univ ×ˢ realTube D (32 * eHat p * rhoHat p) : Set (Phase (a + b))) \
        ⋃ ω ∈ omegaSet D h p, range (K ω)) ∩ {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
      ENNReal.ofReal (complementConstant (a + b)) *
        (volume (D \ dioBase D h p) + volume (realTube D (32 * eHat p * rhoHat p) \ D)) := by
  have hA := actionsMeas_of_limit H hblk hlipI
  have hT := torusMeas_of_limit H hA hlipΦ hsup
  rw [ko_eq hK (fun ω hω => (hI₀ ω hω).1) (exists_omega hI₀)]
  exact hT.meas_torus_of_limit

/-- Joint applicability check (design finding N2): on the witnesses of one application of
`iterative`, `limit_actions_of_steps` and `limit_phi_real_of_steps` supply the clause data of
`meas_torus_final` (with `D_* = ǐ(D₀)`) and both measure helpers apply. -/
theorem meas_of_iterative (H : KamHyp D sbar p h f) :
    ∃ (Ds : ℕ → Set (Fin (a + b) → ℝ)) (hs : ℕ → (Fin (a + b) → ℂ) → ℂ)
      (fs : ℕ → CHam (a + b)) (Ψ Φ : ℕ → CPhase (a + b) → CPhase (a + b))
      (is : ℕ → (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      Ds 0 = dioBase D h p ∧
      ∃ i : (Fin (a + b) → ℝ) → (Fin (a + b) → ℝ),
        TendstoUniformlyOn (actionChain is) i atTop (Ds 0) ∧
        ∃ Φinf : Phase (a + b) → Phase (a + b),
          TendstoUniformlyOn (fun j => psiR (Φ j)) Φinf atTop (univ ×ˢ (i '' Ds 0)) ∧
          ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p) ∧
          TorusMeas D (dioBase D h p) i Φinf (eHat p) (rhoHat p) p.s ∧
          volume (D \ i '' dioBase D h p) ≤ volume (D \ dioBase D h p) +
            ENNReal.ofReal ((4 / 3 : ℝ) ^ (a + b)) *
              (volume (D \ dioBase D h p) +
                volume (realTube D (32 * eHat p * rhoHat p) \ D)) ∧
          volume (((univ ×ˢ realTube D (32 * eHat p * rhoHat p) : Set (Phase (a + b))) \
              Φinf '' (univ ×ˢ (i '' dioBase D h p))) ∩
              {z : Phase (a + b) | ∀ j, z.1 j ∈ Ico (0 : ℝ) 1}) ≤
            ENNReal.ofReal (complementConstant (a + b)) *
              (volume (D \ dioBase D h p) +
                volume (realTube D (32 * eHat p * rhoHat p) \ D)) := by
  obtain ⟨Ds, hs, fs, Ψ, Φ, is, h0, S, P⟩ := iterative_steps H
  obtain ⟨i, hconv, -, hbd, -, hloc, hLip, -, -, -, -⟩ := limit_actions_of_steps S
  have hD : ∀ j, i '' Ds 0 ⊆ realTube (Ds j) ((seq p j).ρ / 2) := by
    rintro j _ ⟨I, hI, rfl⟩
    exact hloc I hI j
  obtain ⟨Φinf, hU, hL, hlam, -, -, -, hsup⟩ := P.limit_phi_real_of_steps hD
  have hbd' := h0 ▸ hbd
  have hLip' := h0 ▸ hLip
  have hL' := h0 ▸ hL
  have hsup' := h0 ▸ hsup
  have hA : ActionsMeas D (dioBase D h p) i (eHat p) (rhoHat p) :=
    actionsMeas_of_limit H (fun I hI => ⟨(hbd' I hI).1, (hbd' I hI).2.1⟩)
      (fun I hI J hJ => hLip' I hI J hJ)
  have hT : TorusMeas D (dioBase D h p) i Φinf (eHat p) (rhoHat p) p.s :=
    torusMeas_of_limit H hA (fun x hx y hy => by
      have := hL' x hx y hy
      rwa [Nat.cast_add] at this) hsup'
  exact ⟨Ds, hs, fs, Ψ, Φ, is, h0, i, hconv, Φinf, hU, hA, hT,
    (meas_actions_of_limit hA).2, hT.meas_torus_of_limit⟩

#print axioms meas_actions_of_limit
#print axioms TorusMeas.meas_torus_of_limit
#print axioms meas_torus_final
#print axioms meas_of_iterative

end KAM.Planetary

end
