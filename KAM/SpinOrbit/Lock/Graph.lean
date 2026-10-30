/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.SpinOrbit.Lock.Graph.Angle
public import KAM.SpinOrbit.Lock.Graph.Bridge
public import KAM.SpinOrbit.Graph.Cert
public import KAM.SpinOrbit.Graph.Rot
public import KAM.CertificateSharp.V2.RouteARefinedEngine

/-!
# From a passing lock certificate to the librational barrier (LOCK-GRAPH)

Design SO-LOCK §1.5, §3, §7. A lock certificate is a graph certificate (`SoGraphCert`: angle
`.1 0 = α` monotone in `θ₀`, action `.2 0 = I` in `[pLo, pHi]`) for the time-scaled client
`κ · lockHamExpr Ω cs`.

* `lockBarrier_of_exact_torus`: an exact torus `K∞` of `κ K` (holomorphic, primary, real on the
  reals, invariant at `s∞ ω*` with `s∞ ω*` Diophantine, mapping the strip into `Re I > 0`) with
  `∂_{θ₀} α ≥ m > 0` and `I ∈ [lo, hi]`, `lo > 0`, on the real torus is a `LockBarrier`. Proof:
  `invarianceError_const_mul` moves to `K` at the **unscaled** frequency `(s∞/κ) ω*`;
  `clock_frequency` with `lockHamExpr_clock` gives the clock `φ = θ₁ + c₀` and `(s∞/κ) ω*₁ = 1`;
  the real torus solves `X_K` (`hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt`), so its physical
  image solves `soField` (`lock_conjugacy`); the graph `I = P(α, φ)` comes from inverting the
  angle (`LockAngle`), and invariance from global uniqueness (`gen_uniqueness`), the polar
  angle of the physical image being `α` modulo one (`arg_lockW_lockToPhysicalR`).
* `lockBarrier_of_certified`: **engine-generic core**. Any certificate check whose soundness
  gives `CertifiedTorus` (plus the static check and the nonvanishing of the Hamiltonian on the
  certified domain, which every base check establishes) yields the barrier.
* `LockGraphCert`, `lockBarrier_of_certV2`: the signed statement for
  `checkTorusCertificateV2 routeAV2`, derived from the core.
-/

@[expose] public noncomputable section

open Real Filter Topology

namespace KAM.SpinOrbit.Lock

open KAM KAM.Certificate KAM.CertificateSharp KAM.CertificateSharp.V2 SoGraph

/-! ### The real torus -/

/-- The real phase point of the torus `K∞` at the real angles `(x, y)`. -/
def lockRealPt (Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)) (x y : ℝ) :
    (Fin 2 → ℝ) × (Fin 2 → ℝ) :=
  (fun i => ((Kinf (realPt x y)).1 i).re, fun i => ((Kinf (realPt x y)).2 i).re)

theorem lockRealPt_eq {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    (hreal : IsRealOnReals Kinf) (x y : ℝ) :
    Kinf (realPt x y) = ofRealPt (lockRealPt Kinf x y) := by
  obtain ⟨z, hz⟩ := hreal ![x, y]
  have hz' : Kinf (realPt x y) = _ := hz
  rw [lockRealPt, hz']
  refine Prod.ext ?_ ?_ <;> funext i <;> simp [ofRealPt]

/-- Derivative along a line of slope `(ν, 1)` at every time, from the derivative at time `0`. -/
theorem hasDerivAt_line_shift {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F D : ℝ → ℝ → E} {ν : ℝ} (h : ∀ x y, HasDerivAt (fun t => F (x + t * ν) (y + t)) (D x y) 0)
    (x y s : ℝ) :
    HasDerivAt (fun t => F (x + t * ν) (y + t)) (D (x + s * ν) (y + s)) s := by
  have h0 := h (x + s * ν) (y + s)
  rw [← sub_self s] at h0
  have := h0.comp_sub_const s s
  convert this using 2 with t
  congr 1 <;> ring

/-! ### The exact torus is a librational barrier -/

/-- **Exact torus of `κ K` ⇒ librational barrier.** `K∞` is an exact torus of the time-scaled
client `κ · lockHamExpr Ω cs` at `s∞ ω*` (`s∞ ω*` Diophantine), mapping the strip into
`Re I > 0`. With `∂_{θ₀} α ≥ m > 0` and `I ∈ [lo, hi]`, `0 < lo`, on the real torus, the real torus
is the invariant graph `I = P(α, φ)` of a `LockBarrier` around `lockCentre cs`. The invariance is
produced: the physical images of the torus orbits at the unscaled frequency `(s∞/κ) ω*` solve
`soField` (`lock_conjugacy`), and solutions are unique (`gen_uniqueness`). -/
theorem lockBarrier_of_exact_torus {Kinf : (Fin 2 → ℂ) → (Fin 2 → ℂ) × (Fin 2 → ℂ)}
    {ρ sinf γ τ m lo hi : ℝ} {Ω κ : ℚ} (hΩ : 0 < Ω) (hκ : 0 < κ) (cs : List ℚ)
    {ωstar : Fin 2 → ℝ} (hρ : 0 < ρ)
    (hholo : DifferentiableOn ℂ Kinf (complexStrip 2 ρ)) (hprim : IsPrimaryOnStrip Kinf ρ)
    (hreal : IsRealOnReals Kinf)
    (hinv : ∀ θ ∈ complexStrip 2 ρ,
      invarianceError (HamExpr.mul (.const κ) (lockHamExpr Ω cs)).eval Kinf (sinf • ωstar) θ = 0)
    (hKD : ∀ θ ∈ complexStrip 2 ρ, 0 < ((Kinf θ).2 0).re)
    (hγ : 0 < γ) (hdio : IsDiophantine γ τ (sinf • ωstar)) (hm : 0 < m)
    (hmono : ∀ x y : ℝ, m ≤ ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re)
    (hlo0 : 0 < lo) (hlo : ∀ x y : ℝ, lo ≤ ((Kinf (realPt x y)).2 0).re)
    (hhi : ∀ x y : ℝ, ((Kinf (realPt x y)).2 0).re ≤ hi) :
    Nonempty (LockBarrier (Ω : ℝ) (lockCentre cs) lo hi) := by
  have hΩr : (0 : ℝ) < Ω := by exact_mod_cast hΩ
  have hκr : (0 : ℝ) < κ := by exact_mod_cast hκ
  have hc3 : ContDiff ℝ 3 (lockCentre cs) := (lockCentre_contDiff cs).of_le le_top
  obtain ⟨hd0, -, hc2⟩ := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (2 + 1) (lockCentre cs) from hc3)
  obtain ⟨hd1, -, -⟩ := contDiff_succ_iff_deriv.mp
    (show ContDiff ℝ (1 + 1) (deriv (lockCentre cs)) from hc2)
  -- undo the time scale `κ`
  have hsm : (κ : ℝ)⁻¹ • (sinf • ωstar) = ((κ : ℝ)⁻¹ * sinf) • ωstar := smul_smul _ _ _
  have heval : (HamExpr.mul (.const κ) (lockHamExpr Ω cs)).eval =
      fun z => ((κ : ℝ) : ℂ) * (lockHamExpr Ω cs).eval z := by
    funext z
    simp [HamExpr.eval]
  have hinv' : ∀ θ ∈ complexStrip 2 ρ,
      invarianceError (lockHamExpr Ω cs).eval Kinf (((κ : ℝ)⁻¹ * sinf) • ωstar) θ = 0 := by
    intro θ hθ
    have h := hinv θ hθ
    rw [heval, invarianceError_const_mul hκr.ne', hsm] at h
    exact (smul_eq_zero.1 h).resolve_left (by exact_mod_cast hκr.ne')
  have hdio' : IsDiophantine ((κ : ℝ)⁻¹ * γ) τ (((κ : ℝ)⁻¹ * sinf) • ωstar) := by
    rw [← hsm]
    exact isDiophantine_smul_scale (inv_pos.2 hκr) hdio
  -- the clock
  obtain ⟨hone, c₀, hc₀⟩ := clock_frequency (D := lockCertRegion)
    (H := (lockHamExpr Ω cs).eval) (j := 1) hρ (fun z hz => lockHamExpr_clock Ω hΩ cs z hz)
    hKD hholo hprim hreal hinv' (mul_pos (inv_pos.2 hκr) hγ) hdio'
  set ν : ℝ := ((κ : ℝ)⁻¹ * sinf) * ωstar 0 with hν
  have hω : ((κ : ℝ)⁻¹ * sinf) • ωstar = ![ν, 1] := by
    funext i; fin_cases i <;> simp [hν, hone]
  have hcl : ∀ x y : ℝ, (lockRealPt Kinf x y).1 1 = y + c₀ := fun x y => by
    have h : (Kinf (realPt x y)).1 1 = ((![x, y] 1 + c₀ : ℝ) : ℂ) := hc₀ ![x, y]
    simp [lockRealPt, h]
  have hpos : ∀ x y : ℝ, 0 < (lockRealPt Kinf x y).2 0 := fun x y =>
    hlo0.trans_le (hlo x y)
  -- the real torus solves `X_K`, its physical image solves `soField`
  have hflow : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => Kinf (realPt (x + s * ν) (y + s)))
      (hamiltonianVectorFieldℂ (lockHamExpr Ω cs).eval (Kinf (realPt x y))) 0 := by
    intro x y
    have h := graphHasDerivAt_lineK hholo hρ ![x, y] ![ν, 1] 0
    have e := hinv' (realPt x y) (realPt_mem hρ x y)
    rw [invarianceError, hω, sub_eq_zero] at e
    have e2 : (fun i => ((![x, y] i + (0 : ℝ) * ![ν, 1] i : ℝ) : ℂ)) = realPt x y := by
      funext i; fin_cases i <;> simp [realPt]
    rw [e2, ← e] at h
    simpa only [realPt_line] using h
  have hrflow : ∀ x y : ℝ, HasDerivAt (fun s : ℝ => lockRealPt Kinf (x + s * ν) (y + s))
      (hamiltonianVectorField (lockHamiltonianR Ω (lockCentre cs)) (lockRealPt Kinf x y)) 0 := by
    intro x y
    have h := hflow x y
    rw [lockRealPt_eq hreal x y,
      hamiltonianVectorFieldℂ_lockHamExpr_ofRealPt hΩ cs _ (hpos x y)] at h
    refine HasDerivAt.prodMk (hasDerivAt_pi.2 fun i => ?_) (hasDerivAt_pi.2 fun i => ?_)
    · have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.1 h.fst i)
      simp only [ofRealPt, Complex.reCLM_apply, Complex.ofReal_re] at this
      exact this
    · have := Complex.reCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) (hasDerivAt_pi.1 h.snd i)
      simp only [ofRealPt, Complex.reCLM_apply, Complex.ofReal_re] at this
      exact this
  have hΦ : ∀ x y : ℝ,
      HasDerivAt
        (fun s : ℝ => lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf (x + s * ν) (y + s)))
        (soField (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y))) 0 := by
    intro x y
    rw [← lock_conjugacy hΩr _ hc3 _ (hpos x y)]
    exact (differentiableAt_lockToPhysicalR hΩr hd0 hd1 _ (hpos x y)).hasFDerivAt
      |>.comp_hasDerivAt_of_eq (0 : ℝ) (hrflow x y) (by simp)
  -- the angle graph
  have hper : ∀ (x y : ℝ) (k : Fin 2 → ℤ),
      Kinf (realPt x y + fun i => ((k i : ℤ) : ℂ)) =
        Kinf (realPt x y) + (fun i => ((k i : ℤ) : ℂ), 0) :=
    fun x y k => hprim _ (realPt_mem hρ x y) k
  have hcp : Continuous fun z : ℝ × ℝ => realPt z.1 z.2 :=
    continuous_pi fun i => by fin_cases i <;> simp [realPt] <;> fun_prop
  have hcK : Continuous fun z : ℝ × ℝ => Kinf (realPt z.1 z.2) :=
    hholo.continuousOn.comp_continuous hcp fun z => realPt_mem hρ _ _
  have e10 : ∀ x y : ℝ, realPt x y + (fun i => ((![1, 0] i : ℤ) : ℂ)) = realPt (x + 1) y :=
    fun x y => by funext i; fin_cases i <;> simp [realPt]
  have e01 : ∀ x y : ℝ, realPt x y + (fun i => ((![0, 1] i : ℤ) : ℂ)) = realPt x (y + 1) :=
    fun x y => by funext i; fin_cases i <;> simp [realPt]
  have T : LockAngle (realQ Kinf)
      (fun x y => ((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re) m :=
    { pos := hm
      cont := Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_fst.comp hcK))
      per₀ := fun x y => by
        have h := hper x y ![1, 0]
        rw [e10] at h
        simpa [realQ] using congrArg (fun u => (u.1 0).re) h
      per₁ := fun x y => by
        have h := hper x y ![0, 1]
        rw [e01] at h
        simpa [realQ] using congrArg (fun u => (u.1 0).re) h
      hasDeriv := fun x y => by
        have h := graphHasDerivAt_lineK hholo hρ ![0, y] ![1, 0] x
        simp only [realPt_zero_line] at h
        exact hasDerivAt_re_comp h
      mono := hmono }
  have hP₀ : ∀ x y, realP Kinf (x + 1) y = realP Kinf x y := fun x y => by
    have h := hper x y ![1, 0]
    rw [e10] at h
    simpa [realP] using congrArg (fun u => (u.2 0).re) h
  have hP₁ : ∀ x y, realP Kinf x (y + 1) = realP Kinf x y := fun x y => by
    have h := hper x y ![0, 1]
    rw [e01] at h
    simpa [realP] using congrArg (fun u => (u.2 0).re) h
  have hPc : Continuous fun z : ℝ × ℝ => realP Kinf z.1 z.2 :=
    Complex.continuous_re.comp ((continuous_apply 0).comp (continuous_snd.comp hcK))
  set P : ℝ → ℝ → ℝ := fun a φ => realP Kinf (T.lockInv a (φ - c₀)) (φ - c₀) with hPdef
  have hPint : ∀ (a φ : ℝ) (k : ℤ), P (a - k) φ = P a φ := by
    intro a φ k
    simp only [hPdef]
    rw [T.lockInv_sub_int]
    exact sub_int_of_periodic hP₀ _ _ k
  -- the polar angle and the action of the physical image of the real torus
  have hval : ∀ x y : ℝ,
      0 < libAction Ω (lockCentre cs) (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y)) ∧
        libAction Ω (lockCentre cs) (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y)) =
          P (Complex.arg (lockW Ω (lockCentre cs)
            (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y))) / (2 * π))
            (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y)).2.2 := by
    intro x y
    rw [libAction_lockToPhysicalR hΩr _ _ (hpos x y).le]
    refine ⟨hpos x y, ?_⟩
    obtain ⟨k, hk⟩ := arg_lockW_lockToPhysicalR hΩr (lockCentre cs) _ (hpos x y)
    rw [hk, hPint]
    simp only [hPdef, lockToPhysicalR, hcl, add_sub_cancel_right]
    rw [show (lockRealPt Kinf x y).1 0 = realQ Kinf x y from rfl, T.lockInv_apply]
    rfl
  refine ⟨⟨P, ?_, fun a φ => ?_, fun a φ => ?_, ?_, fun a φ => hlo _ _, fun a φ => hhi _ _,
    hlo0⟩⟩
  · exact hPc.comp (T.continuous_lockInv.comp (continuous_fst.prodMk
      (continuous_snd.sub continuous_const)) |>.prodMk (continuous_snd.sub continuous_const))
  · simp only [hPdef]
    rw [T.lockInv_add_one, hP₀]
  · simp only [hPdef]
    rw [show φ + 1 - c₀ = (φ - c₀) + 1 by ring, T.lockInv_add_one_right, hP₁]
  · -- invariance: the solution through a graph point is the physical image of a torus orbit
    intro J yy hJ hy t₁ ht₁ hS t ht
    obtain ⟨hS0, hS1⟩ := hS
    set x₀ := yy t₁ with hx₀
    set α₀ : ℝ := Complex.arg (lockW Ω (lockCentre cs) x₀) / (2 * π) with hα₀
    set b : ℝ := x₀.2.2 - c₀ with hb
    set a : ℝ := T.lockInv α₀ b with ha
    have hA : realQ Kinf a b = α₀ := T.lockInv_spec α₀ b
    have hI : realP Kinf a b = libAction Ω (lockCentre cs) x₀ := by
      rw [hS1]; rfl
    have h0 : lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf a b) = x₀ := by
      have hsurj := lockToPhysicalR_surj hΩr (lockCentre cs) x₀ hS0
      refine (lockToPhysicalR_congr ?_ ?_ ?_).trans hsurj
      · show realQ Kinf a b = _
        rw [hA, hα₀, lockW, add_comm]
        rfl
      · simp [hcl, hb]
      · exact hI
    set w : ℝ → ℝ × ℝ × ℝ := fun s =>
      lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf (a + (s - t₁) * ν) (b + (s - t₁)))
      with hw
    have hwd : ∀ s, HasDerivAt w (soField (w s)) s := by
      intro s
      have hs : HasDerivAt (fun s : ℝ => s - t₁) 1 s := (hasDerivAt_id s).sub_const t₁
      have := (hasDerivAt_line_shift
        (F := fun x y => lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y))
        (D := fun x y => soField (lockToPhysicalR Ω (lockCentre cs) (lockRealPt Kinf x y)))
        hΦ a b (s - t₁)).scomp s hs
      simpa [hw, Function.comp_def] using this
    have hsol : KAM.ODE.IsSolutionIn soField Set.univ J w :=
      fun s _ => ⟨Set.mem_univ _, hwd s⟩
    have hw0 : w t₁ = yy t₁ := by
      simp only [hw, sub_self, zero_mul, add_zero]
      exact h0
    have := KAM.ODE.gen_uniqueness isOpen_univ soField_contDiff.contDiffOn hJ ht₁ hy hsol
      hw0.symm ht
    rw [this]
    exact hval _ _

/-! ### From the certificate -/

/-- A lock certificate: a graph certificate (angle `.1 0 = α` monotone, action `.2 0 = I` in
`[pLo, pHi]`) for the time-scaled `κ · lockHamExpr Ω cs`. -/
structure LockGraphCert (α : Type) where
  graph : SoGraphCert α
  Ω : ℚ
  cs : List ℚ
  κ : ℚ

variable {α : Type} [CertArith α]

/-- The certified domain lies in `Re I > 0`: the first square root of `lockHamExpr` (in `X`) has
the operand `(1/Ω) I/π`, certified with positive real part. -/
theorem re_action_pos_of_nonvanishingOn {Ω κ : ℚ} (hΩ : 0 < Ω) {cs : List ℚ}
    {S : Set ((Fin 2 → ℂ) × (Fin 2 → ℂ))}
    (hnv : (HamExpr.mul (.const κ) (lockHamExpr Ω cs)).NonvanishingOn S) :
    ∀ z ∈ S, 0 < (z.2 0).re := by
  intro z hz
  have h := hnv.2
  simp only [lockHamExpr, lockAddAll_cons_cons, lockAddAll_singleton, HamExpr.NonvanishingOn]
    at h
  have hX : (lockXExpr Ω).NonvanishingOn S := h.2.2.2.1.1
  have h1 := hX.1.2 z hz
  simp only [HamExpr.eval] at h1
  have e : ((1 / Ω : ℚ) : ℂ) * z.2 0 / π = ((((1 / Ω : ℚ) : ℝ) / π : ℝ) : ℂ) * z.2 0 := by
    push_cast; ring
  rw [e, Complex.re_ofReal_mul] at h1
  have : (0 : ℝ) < ((1 / Ω : ℚ) : ℝ) / π := by
    have : (0 : ℝ) < ((1 / Ω : ℚ) : ℝ) := by exact_mod_cast (by positivity : (0 : ℚ) < 1 / Ω)
    exact div_pos this Real.pi_pos
  exact pos_of_mul_pos_right h1 this.le

/-- **Engine-generic core.** The black-box output `CertifiedTorus` of ANY sound certificate check,
the static check, the certified nonvanishing of the Hamiltonian on the certified domain, a passing
graph check, the `hham` tie to `κ · lockHamExpr Ω cs` and the positivity margin give the
librational barrier, with the band widened by `disp`. -/
theorem lockBarrier_of_certified [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hlo : 0 < (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    (hs : checkStatic g.graph.base = true)
    (hnv : g.graph.base.ham.NonvanishingOn g.graph.base.D)
    (hg : checkSoGraph g.graph = true) {ωstar : Fin 2 → ℝ}
    (hT : CertifiedTorus g.graph.base ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar) :
    Nonempty (LockBarrier (g.Ω : ℝ) (lockCentre g.cs)
      ((g.graph.pLo : ℝ) - g.graph.base.params.disp)
      ((g.graph.pHi : ℝ) + g.graph.base.params.disp)) := by
  have S := checkStatic_sound hs
  obtain ⟨hm, hmono, hlo', hhi'⟩ := checkSoGraph_sound S.hW S.hpe hg
  obtain ⟨Kinf, sinf, hs1, -, hholo, hprim, hreal, hinv, -, hball, -, hdisp, -⟩ := hT
  have hρ : (0 : ℝ) < g.graph.base.params.rhoInf := S.hρinf
  have hsinf : 0 < sinf := by linarith
  have hK : Differentiable ℂ g.graph.base.K := CertEmbedding.differentiable_eval 2 g.graph.base.emb
  set d : ℝ := (g.graph.base.params.disp : ℝ)
  have hpt : ∀ x y : ℝ, ‖Kinf (realPt x y) - g.graph.base.K (realPt x y)‖ ≤ d :=
    fun x y => hdisp _ (realPt_mem hρ x y)
  have hH : g.graph.base.H = (HamExpr.mul (.const g.κ) (lockHamExpr g.Ω g.cs)).eval := by
    rw [TorusCertificate.H, hham]
  rw [hH] at hinv
  have hD := re_action_pos_of_nonvanishingOn hΩ (hham ▸ hnv)
  have hKD : ∀ θ ∈ complexStrip 2 g.graph.base.params.rhoInf, 0 < ((Kinf θ).2 0).re :=
    fun θ hθ => hD _ (hball θ hθ (Metric.mem_ball_self (by have := S.hμ; positivity)))
  refine lockBarrier_of_exact_torus hΩ hκ g.cs hρ hholo hprim hreal hinv hKD
    (mul_pos hsinf (by exact_mod_cast S.hγ)) (isDiophantine_smul_scale hsinf hdio)
    (m := (g.graph.mono : ℝ) - d / g.graph.base.params.rhoInf) ?_ (fun x y => ?_) hlo
    (fun x y => ?_) (fun x y => ?_)
  · rw [sub_pos, div_lt_iff₀ hρ]; exact hm
  · have h := soGraph_deriv_transfer hρ hholo hK hdisp x y
    have h' : |((fderiv ℂ Kinf (realPt x y) (realPt 1 0)).1 0).re -
        ((fderiv ℂ g.graph.base.K (realPt x y) (realPt 1 0)).1 0).re| ≤
          d / g.graph.base.params.rhoInf := by
      rwa [le_div_iff₀ hρ]
    have := hmono x y
    have := (abs_le.1 h').1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.graph.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hlo' x y
    have := (abs_le.1 h).1
    linarith
  · have h := (Complex.abs_re_le_norm _).trans
      ((norm_snd_apply_sub_le (Kinf (realPt x y)) (g.graph.base.K (realPt x y))).trans (hpt x y))
    rw [Complex.sub_re] at h
    have := hhi' x y
    have := (abs_le.1 h).2
    linarith

/-- LOCK-GRAPH: a passing v2 certificate gives the physical librational barrier. -/
theorem lockBarrier_of_certV2 [LawfulCertArith α] (g : LockGraphCert α) (hΩ : 0 < g.Ω)
    (hκ : 0 < g.κ) (hham : g.graph.base.ham = .mul (.const g.κ) (lockHamExpr g.Ω g.cs))
    (hlo : 0 < (g.graph.pLo : ℝ) - g.graph.base.params.disp)
    {w : routeAV2.Wit} (hc : checkTorusCertificateV2 routeAV2 g.graph.base w = true)
    (hg : checkSoGraph g.graph = true) {ωstar : Fin 2 → ℝ}
    (hω : FreqEncloses 2 g.graph.base.freqBox ωstar)
    (hdio : IsDiophantine (g.graph.base.params.γ : ℝ) (g.graph.base.params.tau : ℝ) ωstar) :
    Nonempty (LockBarrier (g.Ω : ℝ) (lockCentre g.cs)
      ((g.graph.pLo : ℝ) - g.graph.base.params.disp)
      ((g.graph.pHi : ℝ) + g.graph.base.params.disp)) := by
  have hc' := hc
  simp only [checkTorusCertificateV2, checkV2With, landedBase, Bool.and_eq_true] at hc'
  have hs := hc'.1.1.1.1.1.1.1
  exact lockBarrier_of_certified g hΩ hκ hham hlo hs
    (checkHamBounds_sound hs hc'.1.1.1.1.1.1.2).1 hg
    (checkTorusCertificateV2_sound routeAV2 hc hω hdio) hdio

end KAM.SpinOrbit.Lock

end
