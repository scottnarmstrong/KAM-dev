/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Iso.Charts.Apply
import KAM.Head.Parameters
import KAM.Strip.Bridges
import Mathlib.Analysis.Normed.Operator.Prod

/-!
# Part 3 (local charts): uniform constants and the invariant tori on both sides

Package I3-5 of `docs/tracks/I/design/PART123-LEAN-DESIGN.md`, nodes `bpI:p3:uniform` and
`bpI:p3:tori`. `n = 2`, `τ = 2`.

* `uniform` (`bpI:p3:uniform`, existence form over a finite family): a common `C_K` and `ε₁`.
* `tori` (`bpI:p3:tori`, audit fix F2): the cover by the patches of `cover`; before the
  perturbation quantifiers, for every patch, its centre in `closure B'`, `p.W ⊆ 𝒰_c`, the chart
  identity `p.m = m_c` and the two rays fixed per patch and sign; then, for `ε < ε₁`, the two tori
  (T1)-(T7) whose frequencies lie on exactly those rays. It assembles `cover`, `patch_rays`,
  `apply` (per patch and sign, a finite choice of the constants), `uniform`, `points`, and the
  Cauchy estimate `KAM.cauchy_strip` for (T4).
* `part3_tori_of`: the projection of `tori` to Part 5's generic interface (`ChartCover`,
  `ToriExistence`), forgetting the charts and rays.

Part 3 applies I-G1 and G3 only through the premises `IG1Statement` and `G3Statement`.
-/

public section

open scoped Matrix.Norms.Operator
open Matrix Set Metric Topology

namespace KAM.Iso.Charts

open KAM KAM.Torus KAM.Iso.Confinement
open KAM.Head (unperturbedTorus muParam Fconst Mconst)

variable {B : Set (Fin 2 → ℝ)} {s₀ r₀ : ℝ} {h : (Fin 2 → ℂ) → ℂ} {B' : Set (Fin 2 → ℝ)} {η : ℝ}

/-- `bpI:p3:uniform` (existence form over a finite family; only bounds are used downstream). -/
theorem uniform {ι : Type*} (P : Finset ι) (CK0 ε0 : ι → ℝ) (hCK : ∀ i ∈ P, 0 < CK0 i)
    (hε : ∀ i ∈ P, 0 < ε0 i) {a b : ℝ} (ha : 0 < a) (hb : 0 < b) :
    ∃ C_K ε₁ : ℝ, 0 < C_K ∧ 0 < ε₁ ∧ ε₁ ≤ 1 ∧ ε₁ ≤ a ∧ ε₁ ≤ b / (2 * C_K) ∧
      ∀ i ∈ P, CK0 i ≤ C_K ∧ ε₁ ≤ ε0 i := by
  classical
  have _ := hCK
  obtain ⟨M, hM⟩ := (P.image CK0).exists_le
  obtain ⟨N, hN⟩ := (P.image fun i => (ε0 i)⁻¹).exists_le
  have hCKpos : 0 < max M 1 := lt_max_of_lt_right one_pos
  have hNpos : 0 < max N 1 := lt_max_of_lt_right one_pos
  refine ⟨max M 1, min (min 1 (min a (b / (2 * max M 1)))) (max N 1)⁻¹, hCKpos,
    lt_min (lt_min one_pos (lt_min ha (by positivity))) (inv_pos.2 hNpos),
    (min_le_left _ _).trans (min_le_left _ _),
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_left _ _)),
    (min_le_left _ _).trans ((min_le_right _ _).trans (min_le_right _ _)), fun i hi => ?_⟩
  refine ⟨(hM _ (Finset.mem_image_of_mem _ hi)).trans (le_max_left _ _),
    (min_le_right _ _).trans ?_⟩
  have h1 : (ε0 i)⁻¹ ≤ max N 1 :=
    (hN _ (Finset.mem_image_of_mem _ hi)).trans (le_max_left _ _)
  calc (max N 1)⁻¹ ≤ ((ε0 i)⁻¹)⁻¹ := inv_anti₀ (inv_pos.2 (hε i hi)) h1
    _ = ε0 i := inv_inv _

/-! ### The output of `apply`, packaged -/

/-- (O1)–(O6) of the application of I-G1 at the flat torus `K⁰(I)` of `h + f`, `ω = s ω*`,
`e = F₁ε`, `E₀ = E`: the last conjunct of `apply` for a given pair `(K_∞, s_∞)`. -/
@[expose] def ApplyOut (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε E : ℝ)
    (ωs I : Fin 2 → ℝ) (s γ C₂ C₃ : ℝ)
    (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ) : Prop :=
  1 < sinf ∧ sinf < sigmaOmegaConst h B B' ∧
    DifferentiableOn ℂ Kinf (complexStrip 2 (rhoInf s₀)) ∧
    IsPrimaryOnStrip Kinf (rhoInf s₀) ∧ IsRealOnReals Kinf ∧
    (∀ θ ∈ complexStrip 2 (rhoInf s₀), invarianceError (totalH h f) Kinf (sinf • ωs) θ = 0) ∧
    (∀ θ ∈ complexStrip 2 (rhoInf s₀), totalH h f (Kinf θ) = (E : ℂ)) ∧
    (∀ θ ∈ complexStrip 2 (rhoInf s₀),
      Metric.ball (Kinf θ) (muParam s₀ r₀ / 2) ⊆ fractD B s₀ r₀ ∧
      ‖fderiv ℂ Kinf θ‖ ≤ sigmaKConst s₀ r₀ - muParam s₀ r₀ / 2 ∧
      ‖Kinf θ - unperturbedTorus I θ‖ ≤
        C₂ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)) ∧
    ‖sinf • ωs - s • ωs‖ ≤ C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)

/-- The local application of `apply` at the constants `C₁ C₂ C₃` of a patch with centre `c` and a
ray `(γ, ω*, m)`: for every admissible `f, ε` and every energy `E` in the window, a pair
`(K_∞, s_∞)` with the output `ApplyOut` at `I = Ψ(E, m)`, `s = ‖∇h(I)‖/‖ω*‖`. -/
@[expose] def ApplyLocal (B : Set (Fin 2 → ℝ)) (s₀ r₀ : ℝ) (h : (Fin 2 → ℂ) → ℂ)
    (B' : Set (Fin 2 → ℝ)) (c : Fin 2 → ℝ) (δE : ℝ) (Ψ : ℝ × ℝ → Fin 2 → ℝ) (γ m : ℝ)
    (ωs : Fin 2 → ℝ) (C₁ C₂ C₃ : ℝ) : Prop :=
  ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε ≤ 1 →
    ε ≤ epsT h B B' s₀ r₀ → ε < γ ^ 4 * rhoIso s₀ ^ 8 / (C₁ * Fconst 2 s₀ r₀ 1) →
    ∀ E : ℝ, |E - realPart h c| ≤ δE →
    ∃ (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (sinf : ℝ),
      ApplyOut B s₀ r₀ h B' f ε E ωs (Ψ (E, m)) (‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖) γ C₂ C₃
        Kinf sinf

/-- The constants of `apply` with their local application, as `ApplyLocal` (the unfolded
conclusion of `apply`, without the frozen body). -/
theorem applyLocal_exists (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    (hG1 : IG1Statement) {δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)}
    {Ψ : ℝ × ℝ → Fin 2 → ℝ} (hp : IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc) {γ m : ℝ}
    {ωs : Fin 2 → ℝ} (hray : IsRay h B B' c γ ωs m) (hm : |m| < δm) :
    ∃ C₁ C₂ C₃ : ℝ, 0 < C₁ ∧ 0 < C₂ ∧ 0 < C₃ ∧ ApplyLocal B s₀ r₀ h B' c δE Ψ γ m ωs C₁ C₂ C₃ := by
  obtain ⟨C₁, C₂, C₃, h₁, h₂, h₃, -, H⟩ := apply hd hne hG1 hp hray hm
  exact ⟨C₁, C₂, C₃, h₁, h₂, h₃, H⟩

/-! ### Elementary facts for the assembly -/

/-- The inclusion `ι : ℝ² → ℂ²` is an isometry for the max norms. -/
theorem norm_toC (v : Fin 2 → ℝ) : ‖toC v‖ = ‖v‖ := by
  refine le_antisymm ((pi_norm_le_iff_of_nonneg (norm_nonneg v)).2 fun i => ?_)
    ((pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_)
  · simpa using norm_le_pi_norm v i
  · simpa using norm_le_pi_norm (toC v) i

/-- Cauchy estimates for (T4): if `K` is holomorphic on `T_ρ` and `‖K - (θ, ι I)‖ ≤ A` there, the
derivatives of `u = K₁ - θ` and `v = K₂ - ι I` are at most `4 A/ρ` on `T_{ρ/2}`. -/
theorem du_dv_bound {K : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)} {I : Fin 2 → ℝ} {ρ A : ℝ}
    (hρ : 0 < ρ) (hK : DifferentiableOn ℂ K (complexStrip 2 ρ))
    (hA : ∀ θ ∈ complexStrip 2 ρ, ‖K θ - (θ, toC I)‖ ≤ A) :
    (∀ θ ∈ complexStrip 2 (ρ / 2), ‖fderiv ℂ (fun θ => (K θ).1 - θ) θ‖ ≤ 4 * A / ρ) ∧
    ∀ θ ∈ complexStrip 2 (ρ / 2), ‖fderiv ℂ (fun θ => (K θ).2 - toC I) θ‖ ≤ 4 * A / ρ := by
  set u : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ) := fun θ => K θ - (θ, toC I) with hu
  have hud : DifferentiableOn ℂ u (complexStrip 2 ρ) :=
    hK.sub (differentiable_id.prodMk (differentiable_const _)).differentiableOn
  have hC := (cauchy_strip hud (A := A) hA (δ := ρ / 2) (by positivity)).2
  have hρ2 : ρ - ρ / 2 = ρ / 2 := by ring
  rw [hρ2] at hC
  have hbound : ∀ θ ∈ complexStrip 2 (ρ / 2), ‖fderiv ℂ u θ‖ ≤ 4 * A / ρ := by
    intro θ hθ
    refine (hC θ hθ).trans (le_of_eq ?_)
    push_cast
    field_simp
    ring
  have hat : ∀ θ ∈ complexStrip 2 (ρ / 2), HasFDerivAt u (fderiv ℂ u θ) θ := by
    intro θ hθ
    have hθ' : θ ∈ complexStrip 2 ρ :=
      KAM.Head.complexStrip_mono (by linarith) hθ
    exact ((hud.differentiableAt ((KAM.isOpen_complexStrip 2 ρ).mem_nhds hθ'))).hasFDerivAt
  refine ⟨fun θ hθ => ?_, fun θ hθ => ?_⟩
  · have h1 := (hat θ hθ).fst
    have h2 : (fun θ => (K θ).1 - θ) = fun θ => (u θ).1 := by
      funext x; simp [hu]
    rw [h2, h1.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_fst_le ℂ _ _)).trans
        (hbound θ hθ))
  · have h1 := (hat θ hθ).snd
    have h2 : (fun θ => (K θ).2 - toC I) = fun θ => (u θ).2 := by
      funext x; simp [hu]
    rw [h2, h1.fderiv]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_of_le_one_left (norm_nonneg _) (ContinuousLinearMap.norm_snd_le ℂ _ _)).trans
        (hbound θ hθ))

theorem toC_sub (a b : Fin 2 → ℝ) : toC (a - b) = toC a - toC b := by
  ext i; simp [toC]

/-- (T1)–(T7) for one sign from the output `ApplyOut` of `apply` at `I = Ψ(E, m)`: the closeness
constants `C₂ F₁/(γ²ρ⁴)`, `C₃ F₁/(γ²ρ⁴)` are at most `C_K`, `C_K ε < η₁/2`. -/
theorem toriSide_of_applyOut (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    {δE δm ρc : ℝ} {c : Fin 2 → ℝ} {W : Set (Fin 2 → ℝ)} {Ψ : ℝ × ℝ → Fin 2 → ℝ}
    (hp : IsPatch h B r₀ B' (eta1 η B B') c W Ψ δE δm ρc) {γ m : ℝ} {ωs : Fin 2 → ℝ}
    (hray : IsRay h B B' c γ ωs m) (hm : |m| < δm) {C₂ C₃ C_K ε : ℝ}
    (hCK : Fconst 2 s₀ r₀ 1 * max C₂ C₃ / (γ ^ 2 * rhoIso s₀ ^ 4) ≤ C_K) (hε0 : 0 ≤ ε)
    {f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ} {I₀ : Fin 2 → ℝ} (hI₀ : I₀ ∈ closure B')
    (hI₀c : ‖I₀ - c‖ < ρc) {E : ℝ} (hE : |E - realPart h c| ≤ δE)
    (hεK : C_K * ε < eta1 η B B' / 2) {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {sinf : ℝ}
    (hout : ApplyOut B s₀ r₀ h B' f ε E ωs (Ψ (E, m))
      (‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖) γ C₂ C₃ Kinf sinf) :
    ToriSide B s₀ r₀ h B' η (eta1 η B B') f ε C_K E I₀ Ψ m Kinf (Ψ (E, m)) (sinf • ωs) := by
  have hs := hd.hs
  have hr := hd.hr
  obtain ⟨hs1, hs2, hdiff, hprim, hreal, hinv, hen, hk, hsc⟩ := hout
  obtain ⟨-, -, hIE, -, hpar, hsc2, hsc4, -, -, hIB, hnear, -⟩ := points hd hne hp hray hm hE
  have hρ : 0 < rhoInf s₀ := ApplyAux.rhoInf_pos hs
  have hF1 : 1 ≤ Fconst 2 s₀ r₀ 1 := ApplyAux.one_le_Fconst hs hr
  have hD : 0 < γ ^ 2 * rhoIso s₀ ^ 4 := by
    have := ApplyAux.rhoIso_pos hs
    have := hray.1
    positivity
  have hFε : 0 ≤ Fconst 2 s₀ r₀ 1 * ε := mul_nonneg (by linarith) hε0
  have hgen : ∀ C : ℝ, C ≤ max C₂ C₃ →
      C * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4) ≤ C_K * ε := by
    intro C hC
    calc C * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4)
        ≤ max C₂ C₃ * (Fconst 2 s₀ r₀ 1 * ε) / (γ ^ 2 * rhoIso s₀ ^ 4) := by gcongr
      _ = (Fconst 2 s₀ r₀ 1 * max C₂ C₃ / (γ ^ 2 * rhoIso s₀ ^ 4)) * ε := by ring
      _ ≤ C_K * ε := by gcongr
  have hclose : ∀ θ ∈ complexStrip 2 (rhoInf s₀), ‖Kinf θ - (θ, toC (Ψ (E, m)))‖ ≤ C_K * ε :=
    fun θ hθ => (hk θ hθ).2.2.trans (hgen C₂ (le_max_left _ _))
  obtain ⟨hdu, hdv⟩ := du_dv_bound hρ hdiff hclose
  refine
    { holo := hdiff, primary := hprim, real := hreal, invariant := hinv, energy := hen,
      close := hclose, du := fun θ hθ => ?_, dv := fun θ hθ => ?_, base := rfl, ray := ?_,
      level := hIE, near := ⟨hIB, hnear _ hI₀c⟩, action := ?_,
      margins := fun θ hθ => ⟨(hk θ hθ).1, (hk θ hθ).2.1⟩ }
  · rw [mul_assoc]; exact hdu θ hθ
  · rw [mul_assoc]; exact hdv θ hθ
  · refine ⟨γ, ωs, sinf, ‖frequencyMap h (Ψ (E, m))‖ / ‖ωs‖, hray.1, hray.2.1, rfl, hs1, hs2,
      hpar, hsc2, hsc4, ?_⟩
    rw [hpar]
    exact hsc.trans (hgen C₃ (le_max_right _ _))
  · intro x
    have hx : toC x ∈ complexStrip 2 (rhoInf s₀) := fun i => by simpa [toC] using hρ
    obtain ⟨z, hz⟩ := hreal x
    have hz' : Kinf (toC x) = (toC z.1, toC z.2) := hz
    have h2 : ‖(Kinf (toC x)).2 - toC (Ψ (E, m))‖ ≤ C_K * ε :=
      (norm_snd_le (Kinf (toC x) - (toC x, toC (Ψ (E, m))))).trans (hclose (toC x) hx)
    have hKJ : (Kinf (toC x)).2 = toC z.2 := by rw [hz']
    rw [hKJ, ← toC_sub, norm_toC] at h2
    have hη1 : eta1 η B B' ≤ η := min_le_left _ _
    have hη2 : eta1 η B B' ≤ dB B B' / 2 := min_le_right _ _
    have hnear' : ‖Ψ (E, m) - I₀‖ < eta1 η B B' / 2 := hnear _ hI₀c
    have h3 : ‖z.2 - I₀‖ < eta1 η B B' := by
      calc ‖z.2 - I₀‖ = ‖(z.2 - Ψ (E, m)) + (Ψ (E, m) - I₀)‖ := by rw [sub_add_sub_cancel]
        _ ≤ ‖z.2 - Ψ (E, m)‖ + ‖Ψ (E, m) - I₀‖ := norm_add_le _ _
        _ < eta1 η B B' := by linarith
    refine ⟨?_, z.2, ?_, hKJ⟩
    · rw [hKJ, ← toC_sub, norm_toC]
      linarith
    · refine Metric.mem_cthickening_of_dist_le _ I₀ _ _ hI₀ ?_
      rw [dist_eq_norm]
      linarith

/-! ### The patches, their rays and the constants of `tori` -/

/-- The data attached to the centres `c ∈ P` of a cover: rays of both signs and the constants of
`apply` for each of them (a finite choice, before `f, ε, E`). -/
theorem exists_ray_consts (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty)
    (hG1 : IG1Statement) (hG3 : G3Statement) (P : Finset (Fin 2 → ℝ))
    (W : (Fin 2 → ℝ) → Set (Fin 2 → ℝ)) (Ψ : (Fin 2 → ℝ) → ℝ × ℝ → Fin 2 → ℝ)
    (δE δm ρc : (Fin 2 → ℝ) → ℝ)
    (hP : ∀ c ∈ P, IsPatch h B r₀ B' (eta1 η B B') c (W c) (Ψ c) (δE c) (δm c) (ρc c)) :
    ∃ (γp γm mp mm : (Fin 2 → ℝ) → ℝ) (ωp ωm : (Fin 2 → ℝ) → Fin 2 → ℝ)
      (C₁p C₂p C₃p C₁m C₂m C₃m : (Fin 2 → ℝ) → ℝ), ∀ c ∈ P,
        IsRay h B B' c (γp c) (ωp c) (mp c) ∧ mp c ∈ Ioo (δm c / 2) (δm c) ∧
        IsRay h B B' c (γm c) (ωm c) (mm c) ∧ mm c ∈ Ioo (-δm c) (-(δm c / 2)) ∧
        0 < C₁p c ∧ 0 < C₂p c ∧ 0 < C₃p c ∧ 0 < C₁m c ∧ 0 < C₂m c ∧ 0 < C₃m c ∧
        ApplyLocal B s₀ r₀ h B' c (δE c) (Ψ c) (γp c) (mp c) (ωp c) (C₁p c) (C₂p c) (C₃p c) ∧
        ApplyLocal B s₀ r₀ h B' c (δE c) (Ψ c) (γm c) (mm c) (ωm c) (C₁m c) (C₂m c) (C₃m c) := by
  have hrays : ∀ c ∈ P, ∃ (γp γm mp mm : ℝ) (ωp ωm : Fin 2 → ℝ),
      IsRay h B B' c γp ωp mp ∧ mp ∈ Ioo (δm c / 2) (δm c) ∧
      IsRay h B B' c γm ωm mm ∧ mm ∈ Ioo (-δm c) (-(δm c / 2)) :=
    fun c hc => patch_rays hd hne hG3 (hP c hc)
  choose! γp γm mp mm ωp ωm hrp hmp hrm hmm using hrays
  have hAp : ∀ c ∈ P, ∃ C₁p C₂p C₃p C₁m C₂m C₃m : ℝ, 0 < C₁p ∧ 0 < C₂p ∧ 0 < C₃p ∧ 0 < C₁m ∧
      0 < C₂m ∧ 0 < C₃m ∧
      ApplyLocal B s₀ r₀ h B' c (δE c) (Ψ c) (γp c) (mp c) (ωp c) C₁p C₂p C₃p ∧
      ApplyLocal B s₀ r₀ h B' c (δE c) (Ψ c) (γm c) (mm c) (ωm c) C₁m C₂m C₃m := by
    intro c hc
    have hδ := (hP c hc).δm_pos
    obtain ⟨C₁p, C₂p, C₃p, h1p, h2p, h3p, hLp⟩ := applyLocal_exists hd hne hG1 (hP c hc)
      (hrp c hc) (abs_lt.2 ⟨by linarith [(hmp c hc).1], (hmp c hc).2⟩)
    obtain ⟨C₁m, C₂m, C₃m, h1m, h2m, h3m, hLm⟩ := applyLocal_exists hd hne hG1 (hP c hc)
      (hrm c hc) (abs_lt.2 ⟨(hmm c hc).1, by linarith [(hmm c hc).2]⟩)
    exact ⟨C₁p, C₂p, C₃p, C₁m, C₂m, C₃m, h1p, h2p, h3p, h1m, h2m, h3m, hLp, hLm⟩
  choose! C₁p C₂p C₃p C₁m C₂m C₃m h1p h2p h3p h1m h2m h3m hLp hLm using hAp
  exact ⟨γp, γm, mp, mm, ωp, ωm, C₁p, C₂p, C₃p, C₁m, C₂m, C₃m, fun c hc =>
    ⟨hrp c hc, hmp c hc, hrm c hc, hmm c hc, h1p c hc, h2p c hc, h3p c hc, h1m c hc, h2m c hc,
      h3m c hc, hLp c hc, hLm c hc⟩⟩

/-- `bpI:p3:tori` (with `uniform`; audit F2): the cover; OUTSIDE the `f, ε, I₀, E` quantifiers, for
each patch its centre in `closure B'`, the chart identity `p.m = m_c`, and its two fixed rays; then,
for `ε < ε₁`, the two tori (T1)–(T7), whose frequencies lie on exactly those rays. -/
theorem tori (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) (hG1 : IG1Statement)
    (hG3 : G3Statement) :
    ∃ (patches : Set (EnergyPatch (realPart h) B (eta1 η B B')))
      (γp γm : EnergyPatch (realPart h) B (eta1 η B B') → ℝ)
      (ωsp ωsm : EnergyPatch (realPart h) B (eta1 η B B') → Fin 2 → ℝ) (ε₁ C_K : ℝ),
      ChartCover B s₀ r₀ h B' η (eta1 η B B') (Fconst 2 s₀ r₀ 1) patches ∧
      (∀ p ∈ patches, p.c ∈ closure B' ∧ p.W ⊆ chartDom h B r₀ p.c ∧ p.m = chartM h p.c ∧
        IsRay h B B' p.c (γp p) (ωsp p) p.mPlus ∧ IsRay h B B' p.c (γm p) (ωsm p) p.mMinus) ∧
      0 < ε₁ ∧ ε₁ ≤ 1 ∧ 0 < C_K ∧
      ∀ (f : (Fin 2 → ℂ) × (Fin 2 → ℂ) → ℂ) (ε : ℝ), PerturbData B s₀ r₀ f ε → ε < ε₁ →
        ∀ I₀ ∈ closure B', ∀ E : ℝ, |E - realPart h I₀| ≤ ε →
          ∃ p ∈ patches, ‖I₀ - p.c‖ < p.ρc ∧ |p.m I₀| < p.δm / 4 ∧
            ∃ (Kp Km : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (Ip Im ωp ωm : Fin 2 → ℝ),
              (∃ sp sm : ℝ, 1 < sp ∧ sp < sigmaOmegaConst h B B' ∧ 1 < sm ∧
                sm < sigmaOmegaConst h B B' ∧ ωp = sp • ωsp p ∧ ωm = sm • ωsm p) ∧
              ToriSide B s₀ r₀ h B' η (eta1 η B B') f ε C_K E I₀ p.Ψ p.mPlus Kp Ip ωp ∧
              ToriSide B s₀ r₀ h B' η (eta1 η B B') f ε C_K E I₀ p.Ψ p.mMinus Km Im ωm := by
  classical
  have hs := hd.hs
  have hr := hd.hr
  obtain ⟨P, W, Ψ, δE, δm, ρc, hP, hcov⟩ := cover hd hne
  obtain ⟨γp, γm, mp, mm, ωp, ωm, C₁p, C₂p, C₃p, C₁m, C₂m, C₃m, hdata⟩ :=
    exists_ray_consts hd hne hG1 hG3 P W Ψ δE δm ρc hP
  have hF : 0 < Fconst 2 s₀ r₀ 1 := KAM.Head.Parameters.Fconst_pos 2 hs hr 1
  have hρ : 0 < rhoIso s₀ := ApplyAux.rhoIso_pos hs
  obtain ⟨hdB, -, -, -, -, -, hSh, -⟩ := compact hd hne
  have hη1 : 0 < eta1 η B B' := lt_min hd.hη (by linarith)
  have hepsT : 0 < epsT h B B' s₀ r₀ := by
    unfold epsT
    have := KAM.Head.Parameters.Fconst_pos 2 hs hr 2
    positivity
  -- positivity of the data entering `uniform`
  have hCKp : ∀ i ∈ (Finset.univ : Finset Bool) ×ˢ P, 0 < (cond i.1
      (Fconst 2 s₀ r₀ 1 * max (C₂p i.2) (C₃p i.2) / (γp i.2 ^ 2 * rhoIso s₀ ^ 4))
      (Fconst 2 s₀ r₀ 1 * max (C₂m i.2) (C₃m i.2) / (γm i.2 ^ 2 * rhoIso s₀ ^ 4)) : ℝ) := by
    rintro ⟨b, c⟩ hi
    obtain ⟨hrp, -, hrm, -, h1p, h2p, h3p, h1m, h2m, h3m, -, -⟩ :=
      hdata c (Finset.mem_product.1 hi).2
    cases b
    · exact div_pos (mul_pos hF (lt_max_of_lt_left h2m)) (by have := hrm.1; positivity)
    · exact div_pos (mul_pos hF (lt_max_of_lt_left h2p)) (by have := hrp.1; positivity)
  have hεp : ∀ i ∈ (Finset.univ : Finset Bool) ×ˢ P, 0 < (cond i.1
      (min (δE i.2 / 2) (γp i.2 ^ 4 * rhoIso s₀ ^ 8 / (C₁p i.2 * Fconst 2 s₀ r₀ 1)))
      (min (δE i.2 / 2) (γm i.2 ^ 4 * rhoIso s₀ ^ 8 / (C₁m i.2 * Fconst 2 s₀ r₀ 1))) : ℝ) := by
    rintro ⟨b, c⟩ hi
    have hc := (Finset.mem_product.1 hi).2
    obtain ⟨hrp, -, hrm, -, h1p, h2p, h3p, h1m, h2m, h3m, -, -⟩ := hdata c hc
    have hδE := (hP c hc).δE_pos
    cases b
    · exact lt_min (by linarith) (div_pos (by have := hrm.1; positivity) (mul_pos h1m hF))
    · exact lt_min (by linarith) (div_pos (by have := hrp.1; positivity) (mul_pos h1p hF))
  obtain ⟨C_K, ε₁, hCKpos, hε₁pos, hε₁1, hε₁T, hε₁η, hu⟩ := uniform _ _ _ hCKp hεp hepsT hη1
  -- the patches
  let toEP : ∀ c ∈ P, EnergyPatch (realPart h) B (eta1 η B B') := fun c hc =>
    (hP c hc).toEnergyPatch (mp c) (mm c) (hdata c hc).2.1 (hdata c hc).2.2.2.1
  refine ⟨Set.range (fun x : {c // c ∈ P} => toEP x.1 x.2), fun p => γp p.c, fun p => γm p.c,
    fun p => ωp p.c, fun p => ωm p.c, ε₁, C_K, ⟨Set.finite_range _, ?_, hη1, min_le_left _ _,
    hF, ?_⟩, ?_, hε₁pos, hε₁1, hCKpos, ?_⟩
  · intro x hx
    obtain ⟨c, hc, hxc⟩ := Set.mem_iUnion₂.1 (hcov hx)
    exact Set.mem_iUnion₂.2 ⟨toEP c hc, ⟨⟨c, hc⟩, rfl⟩, hxc⟩
  · intro f ε hf hε1 z hz
    exact ((hypothesis_d hd hf hε1).2.2.2.2.2.2 z hz).2.1
  · rintro p ⟨⟨c, hc⟩, rfl⟩
    obtain ⟨hrp, -, hrm, -⟩ := hdata c hc
    exact ⟨(hP c hc).c_mem, (hP c hc).W_dom, rfl, hrp, hrm⟩
  · intro f ε hf hεlt I₀ hI₀ E hE
    obtain ⟨c, hcP, hcb⟩ := Set.mem_iUnion₂.1 (hcov hI₀)
    obtain ⟨hrp, hmp, hrm, hmm, -, -, -, -, -, -, hLp, hLm⟩ := hdata c hcP
    have hε0 : 0 ≤ ε := hf.nonneg
    have hδ := (hP c hcP).δm_pos
    have hmabsp : |mp c| < δm c := abs_lt.2 ⟨by linarith [hmp.1], hmp.2⟩
    have hmabsm : |mm c| < δm c := abs_lt.2 ⟨hmm.1, by linarith [hmm.2]⟩
    have hmem : ∀ b : Bool, (b, c) ∈ (Finset.univ : Finset Bool) ×ˢ P := fun b =>
      Finset.mem_product.2 ⟨Finset.mem_univ _, hcP⟩
    have hCKp' : Fconst 2 s₀ r₀ 1 * max (C₂p c) (C₃p c) / (γp c ^ 2 * rhoIso s₀ ^ 4) ≤ C_K :=
      (hu (true, c) (hmem true)).1
    have hCKm' : Fconst 2 s₀ r₀ 1 * max (C₂m c) (C₃m c) / (γm c ^ 2 * rhoIso s₀ ^ 4) ≤ C_K :=
      (hu (false, c) (hmem false)).1
    have hεp' : ε₁ ≤ min (δE c / 2) (γp c ^ 4 * rhoIso s₀ ^ 8 / (C₁p c * Fconst 2 s₀ r₀ 1)) :=
      (hu (true, c) (hmem true)).2
    have hεm' : ε₁ ≤ min (δE c / 2) (γm c ^ 4 * rhoIso s₀ ^ 8 / (C₁m c * Fconst 2 s₀ r₀ 1)) :=
      (hu (false, c) (hmem false)).2
    -- the energy lies in the window of the patch
    have hE' : |E - realPart h c| ≤ δE c := by
      have h1 := (hP c hcP).ball_h I₀ hcb
      have h2 : ε < δE c / 2 := hεlt.trans_le (hεp'.trans (min_le_left _ _))
      calc |E - realPart h c| ≤ |E - realPart h I₀| + |realPart h I₀ - realPart h c| :=
            abs_sub_le _ _ _
        _ ≤ δE c := by linarith
    have hI₀c : ‖I₀ - c‖ < ρc c := mem_ball_iff_norm.1 hcb
    have hεK : C_K * ε < eta1 η B B' / 2 := by
      have := hεlt.trans_le hε₁η
      rw [lt_div_iff₀ (by positivity)] at this
      linarith
    obtain ⟨Kp, sp, hoP⟩ := hLp f ε hf (hεlt.le.trans hε₁1) (hεlt.le.trans hε₁T)
      (hεlt.trans_le (hεp'.trans (min_le_right _ _))) E hE'
    obtain ⟨Km, sm, hoM⟩ := hLm f ε hf (hεlt.le.trans hε₁1) (hεlt.le.trans hε₁T)
      (hεlt.trans_le (hεm'.trans (min_le_right _ _))) E hE'
    refine ⟨toEP c hcP, ⟨⟨c, hcP⟩, rfl⟩, hI₀c, (hP c hcP).ball_m I₀ hcb, Kp, Km,
      Ψ c (E, mp c), Ψ c (E, mm c), sp • ωp c, sm • ωm c,
      ⟨sp, sm, hoP.1, hoP.2.1, hoM.1, hoM.2.1, rfl, rfl⟩, ?_, ?_⟩
    · exact toriSide_of_applyOut hd hne (hP c hcP) hrp hmabsp hCKp' hε0 hI₀ hI₀c hE' hεK hoP
    · exact toriSide_of_applyOut hd hne (hP c hcP) hrm hmabsm hCKm' hε0 hI₀ hI₀c hE' hεK hoM

/-- The generic Part 5 interface (`part3_tori` of the Part 5 design) under the two premises: a
separately named projection of `tori` that forgets the charts and rays. Proof written out. -/
theorem part3_tori_of (hd : HeadData B s₀ r₀ h B' η) (hne : B'.Nonempty) (hG1 : IG1Statement)
    (hG3 : G3Statement) :
    ∃ (η₁ F₁ : ℝ) (patches : Set (EnergyPatch (realPart h) B η₁)) (ε₁ C_K : ℝ),
      ChartCover B s₀ r₀ h B' η η₁ F₁ patches ∧ ToriExistence B s₀ r₀ h B' η₁ patches ε₁ C_K := by
  obtain ⟨patches, _, _, _, _, ε₁, C_K, hcov, _, h1, h2, h3, H⟩ := tori hd hne hG1 hG3
  refine ⟨_, _, patches, ε₁, C_K, hcov, h1, h2, h3, fun f ε hf hε I₀ hI₀ E hE => ?_⟩
  obtain ⟨p, hp, hc, -, Kp, Km, Ip, Im, ωp, ωm, _, hsp, hsm⟩ := H f ε hf hε I₀ hI₀ E hE
  exact ⟨p, hp, hc, Kp, Km, Ip, Im, ωp, ωm, hsp.toTorusOutput, hsp.base, hsm.toTorusOutput,
    hsm.base⟩

end KAM.Iso.Charts
