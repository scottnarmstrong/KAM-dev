/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Averaging.OscillatorStep
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# P Part 2: reality of the oscillator step (`bpP:p2:osc-iter`, conditional reality)

`osc_generator_real` recovers the reality of the generator `oscGen` and of the zero mode from
conclusion 10 of `homological_param`, applied at every real flat parameter on a small ball; the
real append/unpack bridge identifies the real points of the oscillator domain with the real flat
parameters. `osc_iter_reality` then transports reality to `gp`, to `fp` on `V` and to the step
map `Ψ` (via `OscFlowHyp.real_flow`). Design `docs/tracks/P/design/P23-LEAN-DESIGN.md`,
package P23-13i.
-/

@[expose] public noncomputable section

open Set Metric MeasureTheory Real

namespace KAM.Planetary

open KAM.Weighted KAM.Canonical KAM.NormalForm

section Bridge

variable {n m : ℕ}

/-- The real flat parameter of a real phase point. -/
def oscRealFlat (x : Phase (n + m)) : Fin (n + (m + m)) → ℝ :=
  Fin.append (firstBlock (b := m) x.2)
    (Fin.append (lastBlock (a := n) x.2) (lastBlock (a := n) x.1))

theorem oscPack_real (x : Phase (n + m)) :
    oscPack (m := m) (KAM.realInclusion₂ (n + m) x) =
      (KAM.realInclusion n (firstBlock (b := m) x.1),
        KAM.realInclusion (n + (m + m)) (oscRealFlat x)) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · simp [oscPack, firstBlock]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oscPack, oscRealFlat, firstBlock, Fin.append_left]
    · refine Fin.addCases (fun k => ?_) (fun k => ?_) j
      · simp [oscPack, oscRealFlat, lastBlock, Fin.append_left, Fin.append_right]
      · simp only [oscPack, oscRealFlat, lastBlock, Fin.append_right, KAM.realInclusion_apply]
        rfl

/-- The real phase point with angle-block `θ` and flat parameter `y`. -/
def oscRealUnpack (θ : Fin n → ℝ) (y : Fin (n + (m + m)) → ℝ) : Phase (n + m) :=
  (Fin.append θ (lastBlock (a := m) (lastBlock (a := n) y)),
    Fin.append (firstBlock (b := m + m) y) (firstBlock (b := m) (lastBlock (a := n) y)))

theorem oscUnpack_real (θ : Fin n → ℝ) (y : Fin (n + (m + m)) → ℝ) :
    oscUnpack (m := m) (KAM.realInclusion n θ, KAM.realInclusion (n + (m + m)) y) =
      KAM.realInclusion₂ (n + m) (oscRealUnpack θ y) := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oscUnpack, oscRealUnpack, Fin.append_left]
    · simp [oscUnpack, oscRealUnpack, lastBlock, Fin.append_right]
  · refine Fin.addCases (fun j => ?_) (fun j => ?_) i
    · simp [oscUnpack, oscRealUnpack, firstBlock, Fin.append_left]
    · simp [oscUnpack, oscRealUnpack, firstBlock, lastBlock, Fin.append_right]

end Bridge

section Freq

variable {n : ℕ}

/-- The frequency of a function real on real points is real at real points of an open set. -/
theorem freq_real {h : (Fin n → ℂ) → ℂ} {U : Set (Fin n → ℂ)} (hU : IsOpen U)
    (hh : DifferentiableOn ℂ h U)
    (hreal : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ U → (h (KAM.realInclusion n I)).im = 0)
    {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ U) (i : Fin n) :
    (freq h (KAM.realInclusion n I) i).im = 0 := by
  set e : Fin n → ℝ := Pi.single i 1 with he
  set γ : ℝ → Fin n → ℂ := fun t => KAM.realInclusion n (I + t • e) with hγ
  have hγd : HasDerivAt γ (KAM.realInclusion n e) 0 := by
    have h1 : HasDerivAt (fun t : ℝ => I + t • e) e 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).smul_const e).const_add I
    exact (KAM.realInclusion n).hasFDerivAt.comp_hasDerivAt 0 h1
  have hγ0 : γ 0 = KAM.realInclusion n I := by simp [hγ]
  have hd : HasFDerivAt h (fderiv ℂ h (KAM.realInclusion n I)) (γ 0) := by
    rw [hγ0]
    exact (hh.differentiableAt (hU.mem_nhds hI)).hasFDerivAt
  have hc : HasDerivAt (h ∘ γ) (fderiv ℂ h (KAM.realInclusion n I) (KAM.realInclusion n e)) 0 :=
    (hd.restrictScalars ℝ).comp_hasDerivAt 0 hγd
  have hi : HasDerivAt (fun t => (h (γ t)).im)
      (fderiv ℂ h (KAM.realInclusion n I) (KAM.realInclusion n e)).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt 0 hc
  have hev : (fun t => (h (γ t)).im) =ᶠ[nhds 0] fun _ => 0 := by
    have hcont : Continuous γ := (KAM.realInclusion n).continuous.comp (by fun_prop)
    have hmem : ∀ᶠ t in nhds (0 : ℝ), γ t ∈ U :=
      hcont.continuousAt.eventually_mem (by rw [hγ0]; exact hU.mem_nhds hI)
    filter_upwards [hmem] with t ht
    exact hreal _ ht
  have h0 := hi.unique ((hasDerivAt_const (0 : ℝ) (0 : ℝ)).congr_of_eventuallyEq hev)
  have he' : KAM.realInclusion n e = Pi.single i 1 := by
    ext j; by_cases hj : j = i <;> simp [he, hj]
  rw [he'] at h0
  exact h0

end Freq

section Generator

variable {n m : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S K α δ : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : CHam (n + m)}

/-- Reality of `h` itself on real actions of the tube, from reality of `h ∘ firstBlock ∘ snd`. -/
theorem h_real_of_realOn (hrp : 0 < rp) (hrq : 0 < rq) (hS : 0 < S)
    (hrh : RealOn (oscDom (m := m) D r rp rq S) (fun z => h (firstBlock (b := m) z.2)))
    {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ KAM.actionNbhd D r) :
    (h (KAM.realInclusion n I)).im = 0 := by
  have hx : KAM.realInclusion₂ (n + m)
      ((0 : Fin (n + m) → ℝ), (Fin.append I (0 : Fin m → ℝ) : Fin (n + m) → ℝ)) ∈
        oscDom (m := m) D r rp rq S := by
    rw [mem_oscDom_iff]
    have e1 : firstBlock (b := m) (KAM.realInclusion (n + m)
        (Fin.append I (0 : Fin m → ℝ) : Fin (n + m) → ℝ)) = KAM.realInclusion n I := by
      funext i; simp [firstBlock, Fin.append_left]
    refine ⟨fun i => by simpa using hS, ?_, ?_, ?_⟩
    · simpa [e1] using hI
    · have : lastBlock (a := n) (KAM.realInclusion (n + m)
          (Fin.append I (0 : Fin m → ℝ) : Fin (n + m) → ℝ)) = 0 := by
        funext i; simp [lastBlock, Fin.append_right]
      simpa [this] using hrp
    · have : lastBlock (a := n) (KAM.realInclusion₂ (n + m)
          ((0 : Fin (n + m) → ℝ), (Fin.append I (0 : Fin m → ℝ) : Fin (n + m) → ℝ))).1 = 0 := by
        funext i; simp [lastBlock]
      rw [this]; simpa using hrq
  have := hrh _ hx
  have e1 : firstBlock (b := m) (KAM.realInclusion (n + m)
      (Fin.append I (0 : Fin m → ℝ) : Fin (n + m) → ℝ)) = KAM.realInclusion n I := by
    funext i; simp [firstBlock, Fin.append_left]
  simpa [e1] using this

/-- Local reality of the generator and of the zero mode near any flat parameter. -/
theorem osc_real_local (hrp : 0 < rp) (hrq : 0 < rq) (hS : 0 < S) (hK : 0 ≤ K) (hα : 0 < α)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hb : oscBound D r rp rq S f δ)
    (hrh : RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)))
    (hrf : RealOn (oscDom D r rp rq S) f)
    {x0 : Fin (n + (m + m)) → ℂ} (hx0 : x0 ∈ oscParams (m := m) D r rp rq) :
    ∃ ε : ℝ, 0 < ε ∧ ball x0 ε ⊆ oscParams (m := m) D r rp rq ∧
      ∀ (θ : Fin n → ℝ) (y : Fin (n + (m + m)) → ℝ),
        (KAM.realInclusion n θ, KAM.realInclusion (n + (m + m)) y) ∈
          Dom n ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε S →
        (homGenParam K {0} (oscFreq n m h) (oscFunction f)
          (KAM.realInclusion n θ, KAM.realInclusion (n + (m + m)) y)).im = 0 ∧
        (modeAverage (oscFunction f)
          (KAM.realInclusion n θ, KAM.realInclusion (n + (m + m)) y)).im = 0 := by
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.1 (isOpen_oscParams (m := m) D r rp rq) x0 hx0
  refine ⟨ε, hε, hball, ?_⟩
  have hF := hf.flat
  have hc : InClass ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) :=
    hF.inClass hball le_rfl
  have hb' : WBound ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε S (oscFunction f) δ := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact hb I (hball hI)
  have hω : DifferentiableOn ℂ (oscFreq n m h)
      (polyNbhd ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε) := by
    intro I hI
    rw [polyNbhd_singleton] at hI
    exact (differentiableAt_oscFreq hh (hball hI).1).differentiableWithinAt
  have hdir : ∀ I ∈ polyNbhd ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε, ∀ k ∈ zBall n K \ {0},
      α / 1 ≤ ‖dotC k (oscFreq n m h I)‖ := by
    intro I hI k hk
    rw [polyNbhd_singleton] at hI
    rw [div_one]
    exact hdiv _ (hball hI).1 k hk
  obtain ⟨-, -, -, -, -, c6, -, -, -, c10⟩ :=
    homological_param (ω := oscFreq n m h) (q := 1) le_rfl hα hS hK hω hdir hc hb'
  have hrealF : RealOnParam (Dom n ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε S) (oscFunction f) := by
    rintro ⟨θ, y⟩ hmem
    have hmem' : oscUnpack (m := m) (KAM.realInclusion n θ, KAM.realInclusion (n + (m + m)) y) ∈
        oscDom (m := m) D r rp rq S := by
      show oscPack (m := m) (oscUnpack (KAM.realInclusion n θ,
        KAM.realInclusion (n + (m + m)) y)) ∈
          KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq
      rw [oscPack_oscUnpack]
      exact ⟨hmem.1, hball (by rw [← polyNbhd_singleton]; exact hmem.2)⟩
    rw [oscUnpack_real] at hmem'
    have := hrf _ hmem'
    simpa [oscFunction, oscUnpack_real] using this
  have hrealω : ∀ I : Fin (n + (m + m)) → ℝ,
      KAM.realInclusion (n + (m + m)) I ∈ polyNbhd ({x0} : Set (Fin (n + (m + m)) → ℂ)) ε →
        ∀ i, (oscFreq n m h (KAM.realInclusion (n + (m + m)) I) i).im = 0 := by
    intro I hI i
    rw [polyNbhd_singleton] at hI
    have hI1 := (hball hI).1
    have e : firstBlock (b := m + m) (KAM.realInclusion (n + (m + m)) I) =
        KAM.realInclusion n (firstBlock (b := m + m) I) := rfl
    rw [e] at hI1
    exact freq_real (isOpen_actionNbhd D r) hh
      (fun I' hI' => h_real_of_realOn hrp hrq hS hrh hI') hI1 i
  obtain ⟨c10a, c10b⟩ := c10 (by simp) hrealF hrealω
  have e0 : ({0} : Set (Fin n → ℤ)) ∩ zBall n K = {0} :=
    Set.inter_eq_left.2 (by
      intro k hk
      rw [Set.mem_singleton_iff] at hk
      subst hk
      simpa [zBall, KAM.Fourier.modeSize] using hK)
  intro θ y hmem
  refine ⟨c10a (θ, y) hmem, ?_⟩
  have h6 := c6 _ hmem
  rw [e0, ← modeAverage_eq_projMode] at h6
  rw [← h6]
  exact c10b (θ, y) hmem

end Generator

/-- Reality of the oscillator generator and of the zero mode (from conclusion 10 of
`homological_param` on local parameter balls). -/
theorem osc_generator_real {n m : ℕ} {D : Set (Fin n → ℝ)}
    {r rp rq S K α δ : ℝ} {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)}
    (hwidths : 0 < r ∧ 0 < rp ∧ 0 < rq ∧ 0 < S) (hK : 0 ≤ K) (hα : 0 < α)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hb : oscBound D r rp rq S f δ)
    (hrh : RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)))
    (hrf : RealOn (oscDom D r rp rq S) f) :
    RealOn (oscDom D r rp rq S) (oscGen K h f) ∧
    RealOn (oscDom D r rp rq S) (fun z => coeff (oscFunction f) (oscPack z).2 0) := by
  obtain ⟨hr, hrp, hrq, hS⟩ := hwidths
  have key : ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ oscDom D r rp rq S →
      (oscGen K h f (KAM.realInclusion₂ (n + m) x)).im = 0 ∧
      (coeff (oscFunction f) (oscPack (KAM.realInclusion₂ (n + m) x)).2 0).im = 0 := by
    intro x hx
    have hpk := oscPack_real (m := m) x
    have hmem : oscPack (m := m) (KAM.realInclusion₂ (n + m) x) ∈
        KAM.complexStrip n S ×ˢ oscParams (m := m) D r rp rq := hx
    rw [hpk] at hmem
    obtain ⟨ε, hε, hball, hreal⟩ :=
      osc_real_local hrp hrq hS hK hα hh hdiv hf hb hrh hrf hmem.2
    have hDom : (KAM.realInclusion n (firstBlock (b := m) x.1),
        KAM.realInclusion (n + (m + m)) (oscRealFlat x)) ∈
        Dom n ({KAM.realInclusion (n + (m + m)) (oscRealFlat x)} :
          Set (Fin (n + (m + m)) → ℂ)) ε S :=
      ⟨hmem.1, by rw [polyNbhd_singleton]; exact mem_ball_self hε⟩
    obtain ⟨a, b⟩ := hreal _ _ hDom
    have eg : oscGen K h f (KAM.realInclusion₂ (n + m) x) =
        homGenParam K {0} (oscFreq n m h) (oscFunction f)
          (oscPack (m := m) (KAM.realInclusion₂ (n + m) x)) := by
      have := oscFunction_oscGen K h f (oscPack (m := m) (KAM.realInclusion₂ (n + m) x))
      simp only [oscFunction, Function.comp, s_osc_data] at this
      exact this
    rw [eg, hpk]
    exact ⟨a, b⟩
  exact ⟨fun x hx => (key x hx).1, fun x hx => (key x hx).2⟩

set_option linter.unusedVariables false in
/-- Conditional reality of the step: generator, `gp`, `fp` on `V`, and the step map. -/
theorem osc_iter_reality {n m J : ℕ} {D : Set (Fin n → ℝ)} {r rp rq S ρ ρp ρq σ K α δ : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : CHam (n + m)} {gj : Fin J → CHam (n + m)}
    {rj rpj rqj Sj Mj : Fin J → ℝ}
    (hn : 1 ≤ n) (hm : 1 ≤ m) (hα : 0 < α) (hK : 0 ≤ K)
    (hwidths : 0 < ρ ∧ 2 * ρ < r ∧ 0 < ρp ∧ 2 * ρp < rp ∧
      0 < ρq ∧ 2 * ρq < rq ∧ 0 < σ ∧ 2 * σ < S)
    (hh : DifferentiableOn ℂ h (KAM.actionNbhd D r))
    (hdiv : DivisorBound (KAM.actionNbhd D r) K {0} h α)
    (hf : oscClass D r rp rq S f) (hδ : oscBound D r rp rq S f δ)
    (hδpos : 0 ≤ δ) (hsmall : δ ≤ (2 * π * α) * min (ρ * σ) (ρp * ρq) / (16 * (1 + (m : ℝ))))
    (hg : ∀ j, oscClass D (rj j) (rpj j) (rqj j) (Sj j) (gj j) ∧
      oscBound D (rj j) (rpj j) (rqj j) (Sj j) (gj j) (Mj j) ∧
      r ≤ rj j ∧ rp ≤ rpj j ∧ rq ≤ rqj j ∧ S ≤ Sj j) :
    let Ψ := oscStepMap D r rp rq S ρ ρp ρq σ K h f
    let g := fun z => ∑ j, gj j z
    let gp := fun z => g z + coeff (oscFunction f) (oscPack z).2 0
    let fp := fun z => h (firstBlock (b := m) (Ψ z).2) + g (Ψ z) + f (Ψ z) -
      h (firstBlock (b := m) z.2) - gp z
    let d := min (ρ * σ) (ρp * ρq)
    let Rsum := ∑ j, max (max (ρ / (rj j - r + ρ)) (σ / (Sj j - S + σ)))
      (max (ρp / (rpj j - rp + ρp)) (ρq / (rqj j - rq + ρq))) * Mj j
    let φ := oscGen K h f
    let O := oscDom (m := m) D (r - ρ) (rp - ρp) (rq - ρq) (S - σ)
    let U := oscDom (m := m) D (r - 3 * ρ / 2) (rp - 3 * ρp / 2)
      (rq - 3 * ρq / 2) (S - 3 * σ / 2)
    let u := δ / (2 * π * α * d)
    let V := oscDom (m := m) D (r - 2 * ρ) (rp - 2 * ρp) (rq - 2 * ρq) (S - 2 * σ)
    (RealOn (oscDom D r rp rq S) (fun z => h (firstBlock (b := m) z.2)) →
      RealOn (oscDom D r rp rq S) g → RealOn (oscDom D r rp rq S) f →
      RealOn (oscDom D r rp rq S) φ ∧ RealOn (oscDom D r rp rq S) gp ∧
      RealOn V fp ∧
      ∀ x : Phase (n + m), KAM.realInclusion₂ (n + m) x ∈ U →
        Ψ (KAM.realInclusion₂ (n + m) x) ∈ range (KAM.realInclusion₂ (n + m))) := by
  intro Ψ g gp fp d Rsum φ O U u V hrh hrg hrf
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := hwidths
  have hφ := osc_generator_real (m := m) (D := D) (r := r) (rp := rp) (rq := rq) (S := S)
    (K := K) (α := α) (δ := δ) (h := h) (f := f)
    ⟨by linarith, by linarith, by linarith, by linarith⟩ hK hα hh hdiv hf hδ hrh hrf
  have hgp : RealOn (oscDom D r rp rq S) gp := by
    intro x hx
    show (g _ + coeff (oscFunction f) (oscPack _).2 0).im = 0
    rw [Complex.add_im, hrg x hx, hφ.2 x hx, add_zero]
  have H := osc_flowHyp (m := m) (D := D) (r := r) (rp := rp) (rq := rq) (S := S) (ρ := ρ)
    (ρp := ρp) (ρq := ρq) (σ := σ) (K := K) (α := α) (δ := δ) (h := h) (f := f)
    hα hK ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ hh hdiv hf hδ hδpos hsmall
  have hreal := H.real_flow hφ.1
  refine ⟨hφ.1, hgp, ?_, hreal⟩
  intro x hx
  have hU : KAM.realInclusion₂ (n + m) x ∈ U :=
    oscDom_mono (by linarith) (by linarith) (by linarith) (by linarith) hx
  obtain ⟨x', hx'⟩ := hreal x hU
  have hΨ : Ψ (KAM.realInclusion₂ (n + m) x) = KAM.realInclusion₂ (n + m) x' := hx'.symm
  have hmaps := H.mapsTo_flow hU
  have hO : KAM.realInclusion₂ (n + m) x' ∈ oscDom D r rp rq S := by
    have : Ψ (KAM.realInclusion₂ (n + m) x) ∈ O := hmaps
    rw [hΨ] at this
    exact oscDom_mono (by linarith) (by linarith) (by linarith) (by linarith) this
  have hz : KAM.realInclusion₂ (n + m) x ∈ oscDom D r rp rq S :=
    oscDom_mono (by linarith) (by linarith) (by linarith) (by linarith) hx
  show (h (firstBlock (b := m) (Ψ (KAM.realInclusion₂ (n + m) x)).2) +
    g (Ψ (KAM.realInclusion₂ (n + m) x)) + f (Ψ (KAM.realInclusion₂ (n + m) x)) -
    h (firstBlock (b := m) (KAM.realInclusion₂ (n + m) x).2) -
    gp (KAM.realInclusion₂ (n + m) x)).im = 0
  rw [hΨ]
  have a1 := hrh x' hO
  have a2 := hrg x' hO
  have a3 := hrf x' hO
  have a4 := hrh x hz
  have a5 := hgp x hz
  simp only [Complex.sub_im, Complex.add_im]
  rw [a1, a2, a3, a4, a5]
  simp

end KAM.Planetary

end
