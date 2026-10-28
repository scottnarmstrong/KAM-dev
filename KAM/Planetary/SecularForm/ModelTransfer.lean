/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.SecularForm.Analytic
public import KAM.Planetary.SecularForm.Momentum
public import KAM.Frozen.Planetary.Defs.HasSecularBirkhoffForm

/-!
# Secular form: transfer between the moving and the fixed model

Blueprint P, Part 8 (`bpP:p8:same-jets`, `#jets`, `#transfer`).  On the real polydisc the moving
and fixed secular functions differ by the action-only function `modelDelta` (`identification`), so
all slow jets of positive order agree (`same_jets`, `same_jets_on`).  The generic helper
`birkhoff_transfer` moves `HasSecularBirkhoffForm` across two perturbations whose averages differ
by an action-only function; `same_jets_transfer` discharges its premises by `identification`.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Real Function
open scoped BigOperators Topology Matrix.Norms.Elementwise
namespace KAM.Planetary
open KAM KAM.Kepler

namespace SecularForm
variable {n : ℕ}

theorem mem_slowDom_iff' (D : Data n) (x : Slow n) :
    x ∈ slowDom D ↔ ∀ i, 0 < x.2.1 i ∧ (x.1 i ^ 2 + x.2.2 i ^ 2) / 2 < x.2.1 i := by
  simp [slowDom, poincareProdDom, poincareDom, planetBlock_assemble, poincareGamma]

/-- The real polydisc lies in the chart domain. -/
theorem realDisc_subset_slowDom (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ}
    (hrho : r < rho D a) : realDisc D a r ⊆ slowDom D := by
  intro x hx
  rw [mem_slowDom_iff']
  intro i
  obtain ⟨h1, h2, h3⟩ := hx i
  change ‖((x.1 i : ℝ) : ℂ)‖ < r at h1
  change ‖((x.2.1 i : ℝ) : ℂ) - (action D a i : ℂ)‖ < r at h2
  change ‖((x.2.2 i : ℝ) : ℂ)‖ < r at h3
  rw [Complex.norm_real, Real.norm_eq_abs] at h1 h3
  have h2' : |x.2.1 i - action D a i| < r := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at h2; exact h2
  have hA := action_pos D ha i
  have hr1 := lt_of_lt_of_le hrho (rho_le_half D a i)
  have hr2 := lt_of_lt_of_le hrho (rho_le_sqrt D a i)
  have hr0 : 0 ≤ r := (abs_nonneg _).trans h1.le
  have hsq : r ^ 2 < action D a i / 256 := by
    have hs := Real.sq_sqrt hA.le
    nlinarith [Real.sqrt_nonneg (action D a i)]
  have hl := abs_lt.1 h2'
  refine ⟨by linarith, ?_⟩
  have hx1 : x.1 i ^ 2 < r ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h1 (abs_nonneg _) (by norm_num)
  have hx2 : x.2.2 i ^ 2 < r ^ 2 := by
    rw [← sq_abs]; exact pow_lt_pow_left₀ h3 (abs_nonneg _) (by norm_num)
  nlinarith

/-- Core jet statement at a point of the real polydisc: positive-order slow jets agree. -/
theorem jets_core (D : Data n) {a : Vec n} (ha : a ∈ axes n) {r : ℝ} (hrho : r < rho D a)
    (hint : ∀ x ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D false (assemble x.2.1 t x.2.2 x.1)) (cell n))
    (hr : 0 < r) {x : Slow n} (hx : x ∈ realDisc D a r) {k : ℕ} (hk : 0 < k) :
    iteratedFDeriv ℝ k (slowSecular D true x.2.1) (x.1, x.2.2) =
      iteratedFDeriv ℝ k (slowSecular D false x.2.1) (x.1, x.2.2) := by
  obtain ⟨k, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  let emb : Vec n × Vec n → Slow n := fun u => (u.1, x.2.1, u.2)
  have hemb : Continuous emb := by fun_prop
  have hopen : IsOpen (emb ⁻¹' realDisc D a r) := (isOpen_realDisc D a hr).preimage hemb
  have hmem : (x.1, x.2.2) ∈ emb ⁻¹' realDisc D a r := hx
  have hev : slowSecular D true x.2.1 =ᶠ[𝓝 (x.1, x.2.2)]
      fun u => slowSecular D false x.2.1 u + modelDelta D x.2.1 := by
    filter_upwards [hopen.mem_nhds hmem] with u hu
    have hu' : emb u ∈ realDisc D a r := hu
    exact (identification D (realDisc_subset_slowDom D ha hrho hu')).2.2.2 (hint _ hu')
  rw [(hev.iteratedFDeriv ℝ (k + 1)).self_of_nhds, iteratedFDeriv_succ_eq_comp_right,
    iteratedFDeriv_succ_eq_comp_right]
  have hf : (fun y => fderiv ℝ (fun u => slowSecular D false x.2.1 u + modelDelta D x.2.1) y) =
      fun y => fderiv ℝ (slowSecular D false x.2.1) y :=
    funext fun y => fderiv_add_const _
  simp only [comp_apply, hf]

theorem same_jets_on (D : Data n) {a : Vec n} (ha : a ∈ axes n) :
    ∃ r : ℝ, 0 < r ∧ r < rho D a ∧ ∀ x ∈ realDisc D a r, ∀ k : ℕ, 0 < k → ∀ l : ℕ,
      iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1,x.2.2)) x.2.1 =
      iteratedFDeriv ℝ l (fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1,x.2.2))
        x.2.1 := by
  obtain ⟨r, hr, hrho, -, h⟩ := perturbation_analytic D ha
  refine ⟨r, hr, hrho, fun x hx k hk l => ?_⟩
  have hint : ∀ y ∈ realDisc D a r,
      IntegrableOn (fun t => perturbation D false (assemble y.2.1 t y.2.2 y.1)) (cell n) :=
    fun y hy => (h false).2.2.2.2.2.2 y hy
  let emb : Vec n → Slow n := fun I => (x.1, I, x.2.2)
  have hemb : Continuous emb := by fun_prop
  have hopen : IsOpen (emb ⁻¹' realDisc D a r) := (isOpen_realDisc D a hr).preimage hemb
  have hev : (fun I => iteratedFDeriv ℝ k (slowSecular D true I) (x.1, x.2.2)) =ᶠ[𝓝 x.2.1]
      fun I => iteratedFDeriv ℝ k (slowSecular D false I) (x.1, x.2.2) := by
    filter_upwards [hopen.mem_nhds (show x.2.1 ∈ emb ⁻¹' realDisc D a r from hx)] with I hI
    exact jets_core D ha hrho hint hr (x := emb I) hI hk
  rw [(hev.iteratedFDeriv ℝ l).self_of_nhds]

theorem same_jets (D : Data n) {I : Vec n} (hI : I ∈ actionDomain D) (k : ℕ) (hk : 0 < k) :
    iteratedFDeriv ℝ k (slowSecular D true I) 0 = iteratedFDeriv ℝ k (slowSecular D false I) 0 := by
  obtain ⟨a, ha, rfl⟩ := hI
  obtain ⟨r, hr, hrho, -, h⟩ := perturbation_analytic D ha
  have hx : ((0 : Vec n), action D a, (0 : Vec n)) ∈ realDisc D a r := by
    refine fun i => ⟨?_, ?_, ?_⟩ <;> simp [inclusion, hr]
  exact jets_core D ha hrho (fun y hy => (h false).2.2.2.2.2.2 y hy) hr hx hk

/-- Generic transfer lemma with distinct name; source-specific discharge below. -/
theorem birkhoff_transfer {P Q : ℝ → Phase (n+n) → ℝ} {V : Set (Vec n)} {r0 μ0 : ℝ}
    {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n} {β : ℝ → Vec n → Mat n}
    {δ : Vec n → ℝ}
    (hInt : ∀ μ ∈ Icc 0 μ0, ∀ I ∈ V, ∀ p q : Vec n,
      (∀ j, p j^2+q j^2 < r0^2) →
      (IntegrableOn (fun t => P μ (assemble I t p q)) (cell n) ↔
       IntegrableOn (fun t => Q μ (assemble I t p q)) (cell n)))
    (hAvg : ∀ μ ∈ Icc 0 μ0, ∀ I ∈ V, ∀ p q : Vec n,
      (∀ j, p j^2+q j^2 < r0^2) →
      IntegrableOn (fun t => Q μ (assemble I t p q)) (cell n) →
      secularAverage P μ I p q = secularAverage Q μ I p q + δ I) :
    HasSecularBirkhoffForm P V r0 μ0 P0 Ω β ↔
      HasSecularBirkhoffForm Q V r0 μ0 (fun μ I => P0 μ I - δ I) Ω β := by
  constructor
  · intro h μ hμ I hI
    obtain ⟨hi, he⟩ := h μ hμ I hI
    refine ⟨fun p q hpq => (hInt μ hμ I hI p q hpq).1 (hi p q hpq), fun ε hε => ?_⟩
    obtain ⟨d, hd, hdr, hd'⟩ := he ε hε
    refine ⟨d, hd, hdr, fun p q hpq => ?_⟩
    have hlt : ∀ j, p j ^ 2 + q j ^ 2 < r0 ^ 2 := fun j =>
      (hpq j).trans_le (pow_le_pow_left₀ hd.le hdr 2)
    have hQ := (hInt μ hμ I hI p q hlt).1 (hi p q hlt)
    have := hd' p q hpq
    rw [hAvg μ hμ I hI p q hlt hQ] at this
    convert this using 2
    ring_nf
  · intro h μ hμ I hI
    obtain ⟨hi, he⟩ := h μ hμ I hI
    refine ⟨fun p q hpq => (hInt μ hμ I hI p q hpq).2 (hi p q hpq), fun ε hε => ?_⟩
    obtain ⟨d, hd, hdr, hd'⟩ := he ε hε
    refine ⟨d, hd, hdr, fun p q hpq => ?_⟩
    have hlt : ∀ j, p j ^ 2 + q j ^ 2 < r0 ^ 2 := fun j =>
      (hpq j).trans_le (pow_le_pow_left₀ hd.le hdr 2)
    have := hd' p q hpq
    rw [hAvg μ hμ I hI p q hlt (hi p q hlt)] at ⊢
    convert this using 2
    ring_nf

theorem same_jets_transfer (D : Data n) {V : Set (Vec n)} {r0 μ0 : ℝ}
    {P0 : ℝ → Vec n → ℝ} {Ω : ℝ → Vec n → Vec n} {β : ℝ → Vec n → Mat n}
    (hDom : ∀ I ∈ V, ∀ p q : Vec n, (∀ j, p j^2+q j^2 < r0^2) →
      (q,I,p) ∈ slowDom D) :
    HasSecularBirkhoffForm (fun _ => perturbation D true) V r0 μ0 P0 Ω β ↔
    HasSecularBirkhoffForm (fun _ => perturbation D false) V r0 μ0
      (fun μ I => P0 μ I - modelDelta D I) Ω β :=
  birkhoff_transfer (fun _ _ I hI p q hpq => (identification D (hDom I hI p q hpq)).2.2.1)
    (fun _ _ I hI p q hpq hQ => (identification D (hDom I hI p q hpq)).2.2.2 hQ)

end SecularForm
end KAM.Planetary

end
