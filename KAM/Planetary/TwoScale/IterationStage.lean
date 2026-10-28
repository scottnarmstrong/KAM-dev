/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Planetary.TwoScale.Step
public import KAM.Planetary.TwoScale.IterationReal

/-!
# Two-scale KAM iteration: one stage (`stepP:p3:it-ind`, `it-step`)

A `Stage` packages the data `(Dⱼ, hⱼ, fⱼ, Φⱼ)` of the `j`-th stage of the iteration. `StageInv`
is the invariant carried along the induction (the hypothesis bundle for the scales `seq p j`, the
Diophantine frequency set, and the maps-to / reality / lattice / symplectic properties of `Φⱼ` on
its own domain), and `StepRel` records how one application of `step` produces stage `j + 1` with
`Φ_{j+1} = Φⱼ ∘ Ψ_{j+1}`. `stage_step` is the inductive step; the base case is `stage_zero`.
Design package P23-16.
-/

@[expose] public noncomputable section

open Set Metric Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

theorem seq_succ (p : ScaleData) (j : ℕ) : seq p (j + 1) = nextScale (seq p j) := rfl

theorem seq_γ₁ (p : ScaleData) (j : ℕ) : (seq p j).γ₁ = p.γ₁ := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem seq_γ₂ (p : ScaleData) (j : ℕ) : (seq p j).γ₂ = p.γ₂ := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem seq_τ (p : ScaleData) (j : ℕ) : (seq p j).τ = p.τ := by
  induction j with
  | zero => rfl
  | succ j ih => exact ih

theorem seq_ratio₁ (p : ScaleData) (j : ℕ) :
    (seq p j).Mbar₁ / (seq p j).Mbar = p.Mbar₁ / p.Mbar := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]; exact mul_div_mul_left _ _ two_ne_zero

theorem seq_ratio₂ (p : ScaleData) (j : ℕ) :
    (seq p j).Mbar₂ / (seq p j).Mbar = p.Mbar₂ / p.Mbar := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]; exact mul_div_mul_left _ _ two_ne_zero

theorem seq_ratio_hat (p : ScaleData) (j : ℕ) :
    (seq p j).Mhat / (seq p j).M = p.Mhat / p.M := by
  induction j with
  | zero => rfl
  | succ j ih =>
    rw [← ih]; exact mul_div_mul_left _ _ two_ne_zero

/-- The data `(D, h, f, Φ)` of one stage of the iteration. -/
structure Stage (a b : ℕ) where
  D : Set (Fin (a + b) → ℝ)
  h : (Fin (a + b) → ℂ) → ℂ
  f : CHam (a + b)
  Φ : CPhase (a + b) → CPhase (a + b)

variable {a b : ℕ}

/-- The invariant of the `j`-th stage relative to the initial data `(D₀, h₀, f₀)`. -/
structure StageInv (D₀ : Set (Fin (a + b) → ℝ)) (sbar : ℝ) (p : ScaleData)
    (h₀ : (Fin (a + b) → ℂ) → ℂ) (f₀ : CHam (a + b)) (j : ℕ) (S : Stage a b) : Prop where
  hyp : KamHyp S.D sbar (seq p j) S.h S.f
  freq_eq : realFreq S.h '' S.D = realFreq h₀ '' dioBase D₀ h₀ p
  phase : PhaseProps S.Φ (coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s))
  maps : MapsTo S.Φ (coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s))
    (coefficientDom D₀ p.ρ (sbar + p.s))
  conj : ∀ z ∈ coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s),
    h₀ (S.Φ z).2 + f₀ (S.Φ z) = S.h z.2 + S.f z

/-- The relations between stage `j` and stage `j + 1` recorded by `iterative`. -/
structure StepRel (sbar : ℝ) (p : ScaleData) (j : ℕ) (S S' : Stage a b)
    (Ψ : CPhase (a + b) → CPhase (a + b))
    (is : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)) : Prop where
  comp : S'.Φ = S.Φ ∘ Ψ
  is_diff : DifferentiableOn ℂ is (KAM.actionNbhd S.D (rhoHat (seq p j) / 16))
  is_freq : ∀ I ∈ KAM.actionNbhd S.D (rhoHat (seq p j) / 16),
    freq S'.h (is I) = freq S.h I ∧
    ‖firstBlock (b := b) (is I - I)‖ ≤
      10 * (p.Mbar₁ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) (is I - I)‖ ≤
      10 * (p.Mbar₂ / p.Mbar) * eHat (seq p j) * rhoHat (seq p j)
  is_lip : ∀ I ∈ S.D, ∀ J ∈ S.D,
    ‖(is (KAM.realInclusion (a + b) I) - KAM.realInclusion (a + b) I) -
      (is (KAM.realInclusion (a + b) J) - KAM.realInclusion (a + b) J)‖ ≤
        640 * (a + b) * eHat (seq p j) * ‖I - J‖
  D_eq : S'.D = (fun I => fun k => (is (KAM.realInclusion (a + b) I) k).re) '' S.D
  tube : S'.D ⊆ realTube S.D (rhoHat (seq p j) / 16)
  maps_is : MapsTo is (realBase S.D) (realBase S'.D)
  psi : PhaseProps Ψ (coefficientDom S'.D (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12))
  psi_maps : MapsTo Ψ (coefficientDom S'.D (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12))
    (coefficientDom S.D (rhoHat (seq p j)) (sbar + (seq p j).s))
  psi_bd : ∀ z ∈ coefficientDom S'.D (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12),
    ‖firstBlock (b := b) ((Ψ z).2 - z.2)‖ ≤
      3 / 4 * (p.Mhat / p.M) * eHat (seq p j) * rhoHat (seq p j) ∧
    ‖lastBlock (a := a) ((Ψ z).2 - z.2)‖ ≤ 3 / 4 * eHat (seq p j) * rhoHat (seq p j) ∧
    2 * π * ‖(Ψ z).1 - z.1‖ ≤ 3 / 4 * eHat (seq p j) * (seq p j).s
  eHat_sq : eHat (seq p (j + 1)) < eHat (seq p j) ^ 2
  rho_lo : rhoHat (seq p j) / (2 * (24 : ℝ) ^ (p.τ + 1)) ≤ rhoHat (seq p (j + 1))
  rho_hi : rhoHat (seq p (j + 1)) ≤ rhoHat (seq p j) / 16
  cutoff_le : cutoff (seq p (j + 1)) ≤ 24 * cutoff (seq p j)

theorem PhaseProps.mono {n : ℕ} {Φ : CPhase n → CPhase n} {V V' : Set (CPhase n)}
    (h : PhaseProps Φ V) (hV : V' ⊆ V) : PhaseProps Φ V' where
  diff := h.diff.mono hV
  inj := h.inj.mono hV
  real x hx := h.real x (hV hx)
  per z hz k := h.per z (hV hz) k
  symp z hz u v := h.symp z (hV hz) u v

/-- The base stage: the restriction to the Diophantine base set, with `Φ₀ = id`. -/
theorem stage_zero {D : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h : (Fin (a + b) → ℂ) → ℂ} {f : CHam (a + b)} (H : KamHyp D sbar p h f) :
    StageInv D sbar p h f 0 ⟨dioBase D h p, h, f, id⟩ where
  hyp := H.restrict Set.inter_subset_left
  freq_eq := rfl
  phase := PhaseProps.id _
  maps := fun _ hz => coefficientDom_mono (fun _ ⟨J, hJ, hI⟩ => ⟨J, hJ.1, hI⟩) le_rfl hz
  conj _ _ := rfl

/-- The inductive step: one application of `step`. -/
theorem stage_step {D₀ : Set (Fin (a + b) → ℝ)} {sbar : ℝ} {p : ScaleData}
    {h₀ : (Fin (a + b) → ℂ) → ℂ} {f₀ : CHam (a + b)} (j : ℕ) (S : Stage a b)
    (hS : StageInv D₀ sbar p h₀ f₀ j S) :
    ∃ (S' : Stage a b) (Ψ : CPhase (a + b) → CPhase (a + b))
      (is : (Fin (a + b) → ℂ) → (Fin (a + b) → ℂ)),
      StageInv D₀ sbar p h₀ f₀ (j + 1) S' ∧ StepRel sbar p j S S' Ψ is := by
  have H := hS.hyp
  have hR := H.R_pos
  have hs := H.positive.2.1
  have hD : ∀ I ∈ S.D, realFreq S.h I ∈
      twoScaleDiophantine a b (seq p j).γ₁ (seq p j).γ₂ (seq p j).τ := by
    intro I hI
    have hmem : realFreq S.h I ∈ realFreq h₀ '' dioBase D₀ h₀ p := hS.freq_eq ▸ ⟨I, hI, rfl⟩
    obtain ⟨J, ⟨-, hJ⟩, hJe⟩ := hmem
    rw [seq_γ₁, seq_γ₂, seq_τ, ← hJe]; exact hJ
  obtain ⟨Ψ, g, fs, Dp, ihat, hall⟩ := step H hD
  dsimp only at hall
  obtain ⟨hK, hT, hN, hΨd, hΨi, hΨm, hΨs, hΨp, hΨr, hgd, hgb, hcj, hinj, hess, hfr, hid, hih,
    hDpeq, hlip, hΨb, hrho, hcut, he1, he2⟩ := hall
  have hV'Vb : coefficientDom Dp (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12) ⊆
      coefficientDom S.D (rhoHat (seq p j) / 2) (sbar + (seq p j).s / 6) :=
    coefficientDom_mono (hN.trans (actionNbhd_mono (by linarith))) (by linarith)
  have hWsub : coefficientDom S.D (rhoHat (seq p j)) (sbar + (seq p j).s) ⊆
      coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s) :=
    coefficientDom_mono (actionNbhd_mono H.R_le_ρ) le_rfl
  have hmΨ : MapsTo Ψ (coefficientDom S.D (rhoHat (seq p j) / 2) (sbar + (seq p j).s / 6))
      (coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s)) := fun z hz => hWsub (hΨm hz)
  have hPΨ : PhaseProps Ψ (coefficientDom S.D (rhoHat (seq p j) / 2) (sbar + (seq p j).s / 6)) :=
    ⟨hΨd, hΨi, hΨr, hΨp, hΨs⟩
  have hPc := PhaseProps.comp (isOpen_coefficientDom _ _ _) (isOpen_coefficientDom _ _ _)
    hV'Vb hmΨ hPΨ hS.phase
  have hmV : MapsTo Ψ (coefficientDom Dp (rhoHat (seq p j) / 16) (sbar + (seq p j).s / 12))
      (coefficientDom S.D (seq p j).ρ (sbar + (seq p j).s)) := fun z hz => hmΨ (hV'Vb hz)
  have hih' : ∀ I ∈ KAM.actionNbhd S.D (rhoHat (seq p j) / 16),
      freq (fun J => S.h J + g J) (ihat I) = freq S.h I ∧
      ‖firstBlock (b := b) (ihat I - I)‖ ≤
        10 * ((seq p j).Mbar₁ / (seq p j).Mbar) * eHat (seq p j) * rhoHat (seq p j) ∧
      ‖lastBlock (a := a) (ihat I - I)‖ ≤
        10 * ((seq p j).Mbar₂ / (seq p j).Mbar) * eHat (seq p j) * rhoHat (seq p j) :=
    fun I hI => let ⟨_, h1, h2, h3⟩ := hih I hI; ⟨h1, h2, h3⟩
  refine ⟨⟨Dp, fun I => S.h I + g I, fs, S.Φ ∘ Ψ⟩, Ψ, ihat, ⟨hK, ?_, hPc, ?_, ?_⟩, ?_⟩
  · show realFreq (fun I => S.h I + g I) '' Dp = _
    rw [hfr]; exact hS.freq_eq
  · exact fun z hz => hS.maps (hmV hz)
  · intro z hz
    have e := hS.conj (Ψ z) (hmV hz)
    show h₀ (S.Φ (Ψ z)).2 + f₀ (S.Φ (Ψ z)) = S.h z.2 + g z.2 + fs z
    rw [e, hcj z hz]
  · have hreal : ∀ I ∈ S.D, ∀ i, (ihat (KAM.realInclusion (a + b) I) i).im = 0 :=
      fun I hI i => H.ihat_real_of hK hDpeq hih' hI i
    refine ⟨rfl, hid, fun I hI => ?_, hlip, hDpeq, hT, ?_, hPΨ.mono hV'Vb,
      fun z hz => hΨm (hV'Vb hz), fun z hz => ?_, he2, ?_, hK.R_le_ρ, hcut⟩
    · obtain ⟨-, h1, h2, h3⟩ := hih I hI
      rw [seq_ratio₁] at h2
      rw [seq_ratio₂] at h3
      exact ⟨h1, h2, h3⟩
    · rintro x ⟨I, hI, rfl⟩
      have hq : KAM.realInclusion (a + b) (fun j => (ihat (KAM.realInclusion (a + b) I) j).re) =
          ihat (KAM.realInclusion (a + b) I) := by
        ext i
        apply Complex.ext
        · simp [KAM.realInclusion_apply]
        · simp [KAM.realInclusion_apply, hreal I hI i]
      refine ⟨_, ?_, hq⟩
      rw [hDpeq]; exact ⟨I, hI, rfl⟩
    · have := hΨb z (hV'Vb hz)
      rwa [seq_ratio_hat] at this
    · have := hrho
      rw [seq_τ] at this
      exact this

end KAM.Planetary

end
