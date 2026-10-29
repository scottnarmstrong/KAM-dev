/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import Mathlib
public import KAM.Planetary.Preparation.SlowDivisor
public import KAM.Planetary.Preparation.SlowRates
public import KAM.Planetary.Preparation.RectangularAverage

/-!
# Slow averaging: application of the rectangular averaging lemma (P11A-P7c, `as-concl`)

`p11_slow_conclude` applies `aniso_avg` with `a = b = n`, center the secular center, `r₁ = s₂`,
`r₂ = π ε`, `T = K₂`, `α₁ = (γ/4) K₂^{-τ}`, `α₂ = ε α₁` and
`E₀ = c₀ ε^{5/2} ℓ^{2τ+1}` (`ℓ = log (1/ε)`)
and repackages the conclusion into clauses 9-28 of `P11SlowSpecOf`, with the constants
`c ≥ c₀, …` of the spec as explicit lower bounds (so that the constants of `g₂` and of the
displacements do not depend on `c`). The inputs `h₀, f₂` are parametric in the P7b outputs.
-/

@[expose] public noncomputable section
open Set MeasureTheory Filter Metric
open scoped BigOperators Topology
namespace KAM.Planetary

section Conclude

variable {n : ℕ}

theorem p11Box_half_subset {a b : ℕ} (c : P11CVec (a+b)) {r1 r2 : ℝ} (hr1 : 0 ≤ r1) (hr2 : 0 ≤ r2) :
    p11Box c (r1/2) (r2/2) ⊆ p11Box c r1 r2 :=
  fun _ hI => ⟨fun i => (hI.1 i).trans_le (by linarith), fun i => (hI.2 i).trans_le (by linarith)⟩

/-- A phase-independent function with finite weighted norm is bounded by it. -/
theorem p11_norm_le_of_wbound {m : ℕ} {V : Set (P11CVec m)} {s M : ℝ} {φ : P11CVec m → ℂ}
    (h : p11WBound (n := m) V s (fun z => φ z.2) M) {I : P11CVec m} (hI : I ∈ V) :
    ‖φ I‖ ≤ M := by
  obtain ⟨hsum, hle⟩ := h I hI
  have hc : KAM.Weighted.coeff (fun z : P11CVec m × P11CVec m => φ z.2) I 0 = φ I := by
    unfold KAM.Weighted.coeff KAM.torusCoeffW
    simp only [KAM.character_zero]
    simp only [neg_zero, KAM.character_zero, one_smul]
    exact p11_torusAverage_const _
  have h0 := hsum.le_tsum 0 (fun j _ => mul_nonneg (norm_nonneg _)
    (Real.exp_pos _).le)
  rw [hc] at h0
  have hw : KAM.Weighted.modeWeight s (0 : Fin m → ℤ) = 1 := by
    simp [KAM.Weighted.modeWeight, KAM.Fourier.modeSize]
  rw [hw, mul_one] at h0
  exact h0.trans hle

theorem g_bound_arith {cf0 c N X Y G : ℝ} (hcf0 : 0 ≤ cf0) (hN : 0 ≤ N) (hX : 0 ≤ X)
    (hY : 1 ≤ Y) (hG : G ≤ N * (X * Y) + cf0 * X) (hc : cf0 + N ≤ c) : G ≤ c * X * Y := by
  have h1 : X ≤ X * Y := by nlinarith
  have h2 : 0 ≤ X * Y := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h1 hcf0, mul_le_mul_of_nonneg_right hc h2]

/-- `stepP:p11:as-concl`: the application of `aniso_avg` to `(h₀, f₂)` on the slow box `V₂`, with
the conclusions repackaged as clauses 9-28 of `P11SlowSpecOf` (clause 24 and clause 8 are
inputs).  Here `E₀ = c₀ ε^{5/2} ℓ^{2τ+1}` is the actual bound of `f₂` (clause 23 holds for any
`c ≥ c₀`), `‖f̂₂,₀‖ ≤ c_f ε³` on `V₂/2`, and `c` dominates the explicit constants of `g₂` and of
the displacements. -/
theorem p11_slow_conclude {D : P11Physical n} {C : P11SecularData n} (hC : P11SecularSpec D C)
    {nu eps c0 cf0 c : ℝ} {h0 : P11CVec (n+n) → ℂ} {f2 : P11Phase (n+n) → ℂ}
    (hnu : 1 ≤ nu) (hcf0 : 0 ≤ cf0) (heps : 0 < eps) (hepsE : eps ≤ Real.exp (-1))
    (hpe : Real.pi*eps ≤ p11s2 C nu eps) (hc0 : 0 ≤ c0)
    (hh0 : DifferentiableOn ℂ h0 (p11SlowBox C nu eps))
    (hf2 : DifferentiableOn ℂ f2 (KAM.complexStrip (n+n) (C.sigma/12) ×ˢ p11SlowBox C nu eps))
    (hper : ∀ z ∈ KAM.complexStrip (n+n) (C.sigma/12) ×ˢ p11SlowBox C nu eps,
      ∀ i : Fin (n+n), f2 (z.1+Pi.single i 1,z.2)=f2 z)
    (hreal_h : ∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ p11SlowBox C nu eps →
      (h0 (KAM.realInclusion (n+n) I)).im=0)
    (hreal_f : KAM.Canonical.RealOn
      (KAM.complexStrip (n+n) (C.sigma/12) ×ˢ p11SlowBox C nu eps) f2)
    (hb : p11WBound (p11SlowBox C nu eps) (C.sigma/12) f2
      (c0*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1)))
    (hf0 : ∀ I ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2),
      ‖KAM.Weighted.coeff f2 I 0‖ ≤ cf0*eps^3)
    (hdiv : ∀ I ∈ p11SlowBox C nu eps, ∀ k : Fin (n+n) → ℤ, k ≠ 0 →
      KAM.Fourier.modeSize k ≤ p11K2 C nu eps →
      (if (fun i : Fin n => k (Fin.castAdd n i))=0 then eps else 1)*
        C.gamma/4*p11K2 C nu eps^(-C.tau) ≤
        ‖p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1))‖)
    (hb2 : c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1) ≤
      (eps*C.gamma/4*p11K2 C nu eps^(-C.tau))*Real.pi*eps/(128*p11K2 C nu eps))
    (hcE : c0 ≤ c)
    (hcg : cf0+260*c0^2*(3*nu/(Real.pi*(C.sigma/12)))^C.tau/
      (Real.pi^2*C.gamma*(C.sigma/12)) ≤ c)
    (hcd1 : 6*c0*(3*nu/(Real.pi*(C.sigma/12)))^C.tau/(Real.pi*C.gamma*(C.sigma/12)) ≤ c)
    (hcd3 : 18*c0*(3*nu/(Real.pi*(C.sigma/12)))^C.tau/(Real.pi^2*C.gamma) ≤ c) :
    ∃ (Psi : P11Phase (n+n) → P11Phase (n+n)) (g2 : P11CVec (n+n) → ℂ)
      (f3 : P11Phase (n+n) → ℂ),
      let V := p11SlowBox C nu eps
      let Vh := p11Box (p11SlowCenter C eps) (p11s2 C nu eps/2) (Real.pi*eps/2)
      let s := C.sigma/12
      let E := c*eps^(5/2 : ℝ)*Real.log (1/eps)^(2*C.tau+1)
      DifferentiableOn ℂ h0 V ∧ DifferentiableOn ℂ g2 Vh ∧
      DifferentiableOn ℂ f2 (KAM.complexStrip (n+n) s ×ˢ V) ∧
      DifferentiableOn ℂ f3 (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
      KAM.Canonical.RealOn (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) f3 ∧
      KAM.Canonical.RealOn (KAM.complexStrip (n+n) s ×ˢ V) f2 ∧
      (∀ I : P11Vec (n+n), KAM.realInclusion (n+n) I ∈ Vh →
        (g2 (KAM.realInclusion (n+n) I)).im=0 ∧ (h0 (KAM.realInclusion (n+n) I)).im=0) ∧
      (∀ z : Phase (n+n), KAM.realInclusion₂ (n+n) z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh →
        ∀ i, ((Psi (KAM.realInclusion₂ (n+n) z)).1 i).im=0 ∧
          ((Psi (KAM.realInclusion₂ (n+n) z)).2 i).im=0) ∧
      (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ i : Fin (n+n),
        f3 (z.1+Pi.single i 1,z.2)=f3 z) ∧
      DifferentiableOn ℂ Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
      (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ u v,
        KAM.Canonical.symplFormC (fderiv ℂ Psi z u) (fderiv ℂ Psi z v)=
          KAM.Canonical.symplFormC u v) ∧
      (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh, ∀ k : Fin (n+n) → ℤ,
        Psi (z.1+(fun i => (k i : ℂ)),z.2)=Psi z+((fun i => (k i : ℂ)),0)) ∧
      InjOn Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) ∧
      MapsTo Psi (KAM.complexStrip (n+n) (s/6) ×ˢ Vh) (KAM.complexStrip (n+n) s ×ˢ V) ∧
      p11WBound V s f2 E ∧
      E ≤ (eps*C.gamma/4*p11K2 C nu eps^(-C.tau))*Real.pi*eps/(128*p11K2 C nu eps) ∧
      p11WBound Vh (s/6) f3 (eps^nu*E) ∧
      p11Bound Vh g2 (c*eps^3*Real.log (1/eps)^(5*C.tau+2)) ∧
      (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
        h0 (Psi z).2+f2 (Psi z)=h0 z.2+g2 z.2+f3 z) ∧
      (∀ z ∈ KAM.complexStrip (n+n) (s/6) ×ˢ Vh,
        ‖(fun i : Fin n => (Psi z).2 (Fin.natAdd n i)-z.2 (Fin.natAdd n i))‖ ≤
          c*eps^(3/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
        ‖(fun i : Fin n => (Psi z).2 (Fin.castAdd n i)-z.2 (Fin.castAdd n i))‖ ≤
          c*eps^(5/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1) ∧
        ‖(Psi z).1-z.1‖ ≤ c*eps^(1/2 : ℝ)*Real.log (1/eps)^(3*C.tau+1)) := by
  obtain ⟨hγ0, hτ0, hL1, hrC0, -, hσ0, hσ1, hrz0, -, -⟩ := fast_consts hC
  have hπ := Real.pi_pos
  have hl1 : 1 ≤ Real.log (1/eps) := log_inv_ge_one heps hepsE
  set l := Real.log (1/eps) with hldef
  have hl : 0 < l := by linarith
  set s := C.sigma/12 with hsdef
  have hs : 0 < s := by positivity
  set a : ℝ := 3*nu/(Real.pi*(C.sigma/12)) with hadef
  have ha : 0 < a := by positivity
  have hKdef : p11K2 C nu eps = a*l := rfl
  set K := p11K2 C nu eps with hK'
  have hK : 0 < K := by rw [hKdef]; positivity
  have heps1 : eps ≤ 1 := hepsE.trans (by rw [Real.exp_le_one_iff]; norm_num)
  have hs2 : 0 < p11s2 C nu eps := lt_of_lt_of_le (by positivity) hpe
  have hKt : 0 < K ^ (-C.tau) := Real.rpow_pos_of_pos hK _
  set α1 : ℝ := C.gamma/4*K^(-C.tau) with hα1
  have hα1pos : 0 < α1 := by positivity
  set α2 : ℝ := eps*α1 with hα2
  have hα2pos : 0 < α2 := by positivity
  set E0 : ℝ := c0*eps^(5/2 : ℝ)*l^(2*C.tau+1) with hE0
  set E : ℝ := c*eps^(5/2 : ℝ)*l^(2*C.tau+1) with hE
  have hbase : 0 ≤ eps^(5/2 : ℝ)*l^(2*C.tau+1) := by positivity
  have hE0E : E0 ≤ E := by
    rw [hE0, hE, mul_assoc, mul_assoc]
    exact mul_le_mul_of_nonneg_right hcE hbase
  have hE0nn : 0 ≤ E0 := by positivity
  have hmin : min (p11s2 C nu eps) (Real.pi*eps) = Real.pi*eps := min_eq_right hpe
  have hk6 : 6 ≤ 2*Real.pi*K*s := by
    have : 2*Real.pi*K*s = 6*nu*l := by
      rw [hKdef, hadef, hsdef]
      field_simp
      ring
    rw [this]; nlinarith
  have hsmall : E0 ≤ α2*min (p11s2 C nu eps) (Real.pi*eps)/(128*K) := by
    rw [hmin]
    refine hE0E.trans (hb2.trans (le_of_eq ?_))
    rw [hα2, hα1]; ring
  have hdiv' : ∀ I ∈ p11Box (p11SlowCenter C eps) (p11s2 C nu eps) (Real.pi*eps),
      ∀ k : Fin (n+n) → ℤ, k ≠ 0 → KAM.Fourier.modeSize k ≤ K →
      (if (fun i : Fin n => k (Fin.castAdd n i))=0 then α2 else α1) ≤
        ‖p11dotC k (fun i => fderiv ℂ h0 I (Pi.single i 1))‖ := by
    intro I hI k hk hkK
    have := hdiv I hI k hk hkK
    split_ifs at this ⊢
    · rw [hα2, hα1]; linarith
    · rw [hα1]; linarith
  obtain ⟨Psi, g, fs, hU⟩ := aniso_avg (a := n) (b := n) (c := p11SlowCenter C eps)
    (r1 := p11s2 C nu eps) (r2 := Real.pi*eps) (s := s) (T := K) (alpha1 := α1) (alpha2 := α2)
    (E := E0) hs2 (by positivity) hs hK hk6 hα2pos
    (by rw [hα2]; exact mul_le_of_le_one_left hα1pos.le heps1) hh0 hf2 hper hreal_h hreal_f hE0nn
    hb hsmall hdiv'
  refine ⟨Psi, g, fs, ?_⟩
  intro V Vh s' E'
  obtain ⟨c1, c2, c3, c4, c5, c6, c7, c8, c9, c10, c11, c12, c13, c14, c15, c16, c17⟩ := hU
  have hlog : Real.log eps = -l := by
    rw [hldef, one_div, Real.log_inv, neg_neg]
  have hexp : Real.exp (-2*Real.pi*K*s/6) = eps^nu := by
    have h6 : -2*Real.pi*K*s/6 = -(nu*l) := by
      have : 2*Real.pi*K*s = 6*nu*l := by
        rw [hKdef, hadef, hsdef]
        field_simp
        ring
      linarith
    rw [h6, Real.rpow_def_of_pos heps, hlog]
    congr 1; ring
  have hq := slow_g_quad (c0 := c0) (τ := C.tau) heps hl ha hγ0 hs
  have hr1 := slow_disp_rho (c0 := c0) (τ := C.tau) heps hl ha hγ0 hs
  have hr2 := slow_disp_J (c0 := c0) (τ := C.tau) heps hl ha hγ0 hs
  have hr3 := slow_disp_theta (c0 := c0) (τ := C.tau) heps hl ha hγ0
  rw [← hKdef] at hq hr1 hr2 hr3
  have hlpow : ∀ r : ℝ, 0 ≤ r → 1 ≤ l ^ r := fun r hr => Real.one_le_rpow hl1 hr
  refine ⟨hh0, c3, hf2, c4, c5, hreal_f, ?_, c9, c8, c1, c17, c7, c2, c10, ?_, hb2, ?_, ?_, c11,
    ?_⟩
  · intro I hI
    exact ⟨c6 I hI, hreal_h I (p11Box_half_subset _ hs2.le (by positivity) hI)⟩
  · exact fun I hI => ⟨(hb I hI).1, (hb I hI).2.trans hE0E⟩
  · intro I hI
    refine ⟨(c12 I hI).1, (c12 I hI).2.trans ?_⟩
    rw [hexp]
    exact mul_le_mul_of_nonneg_left hE0E (by positivity)
  · intro I hI
    have h1 := p11_norm_le_of_wbound (φ := fun I => g I - KAM.Weighted.coeff f2 I 0) c13 hI
    have h2 := hf0 I hI
    have h3 : ‖g I‖ ≤ ‖g I - KAM.Weighted.coeff f2 I 0‖ + ‖KAM.Weighted.coeff f2 I 0‖ := by
      have := norm_add_le (g I - KAM.Weighted.coeff f2 I 0) (KAM.Weighted.coeff f2 I 0)
      simpa using this
    rw [hmin] at h1
    have hqq : 130 * E0 ^ 2 / (2 * Real.pi * α2 * (Real.pi * eps) * s) =
        260 * c0 ^ 2 * a ^ C.tau / (Real.pi ^ 2 * C.gamma * s) *
          (eps ^ 3 * l ^ (5 * C.tau + 2)) := by
      rw [hα2, hα1, hE0]; exact hq
    rw [hqq] at h1
    have hb1 : 1 ≤ l ^ (5 * C.tau + 2) := hlpow _ (by linarith)
    have he3 : 0 ≤ eps ^ 3 := by positivity
    have hN : 0 ≤ 260 * c0 ^ 2 * a ^ C.tau / (Real.pi ^ 2 * C.gamma * s) := by positivity
    show ‖g I‖ ≤ c * eps ^ 3 * l ^ (5 * C.tau + 2)
    exact g_bound_arith hcf0 hN he3 hb1 (h3.trans (add_le_add h1 h2)) hcg
  · intro z hz
    obtain ⟨d1, d2⟩ := c15 z hz
    have d3 := c16 z hz
    rw [hmin] at d3
    have hρ : ‖(fun i : Fin n => (Psi z).2 (Fin.natAdd n i) - z.2 (Fin.natAdd n i))‖ ≤
        c * eps ^ (3 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by
      have h1 : ‖(fun i : Fin n => (Psi z).2 (Fin.natAdd n i) - z.2 (Fin.natAdd n i))‖ ≤
          3 * E0 / (2 * Real.pi * α2 * s) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [hα2, hα1, hE0] at h1
      rw [hr1] at h1
      refine h1.trans ?_
      have hX : 0 ≤ eps ^ (3 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hcd1 hX
      linarith
    have hJ : ‖(fun i : Fin n => (Psi z).2 (Fin.castAdd n i) - z.2 (Fin.castAdd n i))‖ ≤
        c * eps ^ (5 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by
      have h1 : ‖(fun i : Fin n => (Psi z).2 (Fin.castAdd n i) - z.2 (Fin.castAdd n i))‖ ≤
          3 * E0 / (2 * Real.pi * α1 * s) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      rw [hα1, hE0] at h1
      rw [hr2] at h1
      refine h1.trans ?_
      have hX : 0 ≤ eps ^ (5 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hcd1 hX
      linarith
    have hθ : ‖(Psi z).1 - z.1‖ ≤ c * eps ^ (1 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by
      have h1 : ‖(Psi z).1 - z.1‖ ≤ 9 * E0 / (2 * Real.pi * α2 * (Real.pi * eps)) := by
        refine d3.trans (le_of_eq ?_)
        rfl
      rw [hα2, hα1, hE0] at h1
      rw [hr3] at h1
      refine h1.trans ?_
      have hX : 0 ≤ eps ^ (1 / 2 : ℝ) * l ^ (3 * C.tau + 1) := by positivity
      have := mul_le_mul_of_nonneg_right hcd3 hX
      linarith
    exact ⟨hρ, hJ, hθ⟩

end Conclude

end KAM.Planetary

end
