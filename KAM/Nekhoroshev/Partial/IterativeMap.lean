/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.CanonicalMap
public import KAM.Nekhoroshev.Partial.Homological
public import KAM.Nekhoroshev.Partial.Composition
import Mathlib.Tactic.DefEqTransformations
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Ring

/-!
# The Iterative Lemma on the extended phase space: the map (`bpN:p11:iterative`)

Part 11, package N11-H, first module. The source premises of `iterative` (without the
decomposition of `g`) are bundled in `NitHyp`; from them:

* step `it-gen`: `NitHyp.nit_hom` (the signed `hom` with `q = conjExp p`, `U = δ`, so
  `|φ|_{R,s} ≤ qδ/(2πα)`), `NitHyp.nit_V_le` (`η/2 = |φ|/(ρσ) ≤ 1/4`) and
  `NitHyp.nit_compose` (the `ExtCompose` data with `u`-domain `(R-ρ, s-σ)` inside `(R, s)`);
* step `it-map`: the inputs of the signed `canonical_map` (`NitHyp.nit_V_half`,
  `nit_phi_class`, `nit_phi_bound`), the displacement conversion `NitHyp.nit_disp` (clause (b)
  of the source, the slow bound through `(SL)_{ρ,σ}`) and `nit_injOn` (injectivity from the
  left inverse `X⁻¹_φ`);
* the homological equation in bracket form `NitHyp.nit_bracket_eq`
  (`{h, φ}_c = ξ - T_K f` on `𝒟_{R,s}`), through the antisymmetry `nit_extBracket_antisymm`;
* `NitHyp.nit_gp_bound` (`|g₊ - g| ≤ δ`), the class and reality of `h` lifted to `EC n k`
  (`nit_liftFast_class`, `nit_liftFast_real`), the reality of the frequency
  (`nit_freq_im`) and the class of a finite decomposition (`nit_sum_class`).

Design `docs/tracks/N/design/N11-LEAN-DESIGN.md` (Revision 2, F2 for `iterative`).
-/

@[expose] public noncomputable section

open Set Metric
open scoped BigOperators

namespace KAM.Nekhoroshev

open KAM.Weighted KAM.NormalForm

variable {n k : ℕ}

/-! ### Class helpers (independent base dimension) -/

section Generic

variable {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}

theorem nit_inClass_mono {r₀ s₀ : ℝ} {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ}
    (hu : InClass D r₀ s₀ u) (hr : r ≤ r₀) (hs : s ≤ s₀) : InClass D r s u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

theorem nit_inClass_add {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u)
    (hv : InClass D r s v) : InClass D r s (fun z => u z + v z) :=
  ⟨hu.differentiableOn.add hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

theorem nit_inClass_sub {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u)
    (hv : InClass D r s v) : InClass D r s (fun z => u z - v z) :=
  ⟨hu.differentiableOn.sub hv.differentiableOn, fun j z hz => by
    simp only [hu.periodic j z hz, hv.periodic j z hz]⟩

theorem nit_wbound_zero : WBound D r s (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (0 : ℂ)) 0 := by
  intro I _
  have h0 : ∀ l : Fin n → ℤ, coeff (fun _ : (Fin n → ℂ) × (Fin m → ℂ) => (0 : ℂ)) I l = 0 :=
    fun l => by simp [coeff, KAM.torusCoeffW, KAM.torusAverage]
  simp [WSummable, wsum, h0]

end Generic

/-- A finite decomposition `g = ∑ⱼ gⱼ`, `gⱼ ∈ 𝒪_{Rⱼ,sⱼ}`, `Rⱼ ≥ R`, `sⱼ ≥ s`, is in `𝒪_{R,s}`
with `|g|_{R,s} ≤ ∑ⱼ Uⱼ`. -/
theorem nit_sum_class (b : PartialBlock n k) {N : ℕ} (gj : Fin N → EC n k → ℂ)
    (Rj sj Uj : Fin N → ℝ) {R s : ℝ} (hs : 0 < s) (hRj : ∀ j, R ≤ Rj j) (hsj : ∀ j, s ≤ sj j)
    (hgj : ∀ j, InClass b.base (Rj j) (sj j) (gj j))
    (hgjb : ∀ j, WBound b.base (Rj j) (sj j) (gj j) (Uj j)) :
    InClass b.base R s (fun z => ∑ j, gj j z) ∧
      WBound b.base R s (fun z => ∑ j, gj j z) (∑ j, Uj j) := by
  have hcl : ∀ j, InClass b.base R s (gj j) := fun j => nit_inClass_mono (hgj j) (hRj j) (hsj j)
  have hb : ∀ j, WBound b.base R s (gj j) (Uj j) := fun j => (hgjb j).mono (hRj j) (hsj j) le_rfl
  have key : ∀ S : Finset (Fin N), InClass b.base R s (fun z => ∑ j ∈ S, gj j z) ∧
      WBound b.base R s (fun z => ∑ j ∈ S, gj j z) (∑ j ∈ S, Uj j) := by
    intro S
    induction S using Finset.induction_on with
    | empty => exact ⟨⟨differentiableOn_const 0, fun _ _ _ => rfl⟩, by simpa using nit_wbound_zero⟩
    | insert a S ha ih =>
      have e : (fun z => ∑ j ∈ insert a S, gj j z) = fun z => gj a z + ∑ j ∈ S, gj j z := by
        funext z; rw [Finset.sum_insert ha]
      rw [e, Finset.sum_insert ha]
      exact ⟨nit_inClass_add (hcl a) ih.1, wbound_add_ext hs (hcl a) ih.1 (hb a) ih.2⟩
  exact key Finset.univ

/-! ### Algebra of the extended bracket -/

/-- A continuous linear functional is the sum of its values on the coordinate directions. -/
private theorem nit_clm_eq_sum (L : EC n k →L[ℂ] ℂ) (x : EC n k) :
    L x = ∑ i, x.1 i * L (Pi.single i 1, 0) + ∑ j, x.2 j * L (0, Pi.single j 1) := by
  have h1 : ((x.1, 0) : EC n k) = ∑ i, x.1 i • ((Pi.single i 1, 0) : EC n k) := by
    ext a
    · simp [Prod.fst_sum, Finset.sum_apply, Pi.single_apply]
    · simp [Prod.snd_sum]
  have h2 : ((0, x.2) : EC n k) = ∑ j, x.2 j • ((0, Pi.single j 1) : EC n k) := by
    ext a
    · simp [Prod.fst_sum]
    · simp [Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hx : x = (x.1, 0) + (0, x.2) := by ext <;> simp
  conv_lhs => rw [hx, map_add, h1, h2, map_sum, map_sum]
  simp only [map_smul, smul_eq_mul]

/-- The coordinate expansion of `A (X^c)`, where `X^c` is the weighted field of the
functional `B`. -/
private def nitE (c : ℝ) (A B : EC n k →L[ℂ] ℂ) : ℂ :=
  ∑ i : Fin n, (B (0, Pi.single (Fin.castAdd (k+k) i) 1) * A (Pi.single i 1, 0) -
      B (Pi.single i 1, 0) * A (0, Pi.single (Fin.castAdd (k+k) i) 1)) +
    ∑ i : Fin k, ((c : ℂ) * B (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1) *
        A (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) -
      (c : ℂ) * B (0, Pi.single (Fin.natAdd n (Fin.castAdd k i)) 1) *
        A (0, Pi.single (Fin.natAdd n (Fin.natAdd k i)) 1))

private theorem nit_extBracket_eq (c : ℝ) (u v : EC n k → ℂ) (z : EC n k) :
    extBracket c u v z = nitE c (fderiv ℂ u z) (fderiv ℂ v z) := by
  unfold extBracket
  rw [nit_clm_eq_sum (fderiv ℂ u z) (wfield c v z)]
  simp only [wfield, Fin.sum_univ_add, Fin.append_left, Fin.append_right, nitE, neg_mul,
    Finset.sum_neg_distrib, Finset.sum_sub_distrib]
  ring

private theorem nitE_swap (c : ℝ) (A B : EC n k →L[ℂ] ℂ) : nitE c A B = -nitE c B A := by
  unfold nitE
  rw [neg_add, ← Finset.sum_neg_distrib, ← Finset.sum_neg_distrib]
  congr 1 <;> exact Finset.sum_congr rfl fun i _ => by ring

/-- Antisymmetry of the extended bracket: `{u, v}_c = -{v, u}_c`. -/
theorem nit_extBracket_antisymm (c : ℝ) (u v : EC n k → ℂ) (z : EC n k) :
    extBracket c u v z = -extBracket c v u z := by
  rw [nit_extBracket_eq c u v z, nit_extBracket_eq c v u z]
  exact nitE_swap c _ _

/-- The bracket `{u, φ}_c` at `z` only sees `u` on an open neighbourhood of `z`. -/
theorem nit_bracket_congr {c : ℝ} {u u' φ : EC n k → ℂ} {U : Set (EC n k)} (hU : IsOpen U)
    (hEq : EqOn u u' U) {z : EC n k} (hz : z ∈ U) :
    extBracket c u φ z = extBracket c u' φ z := by
  have hd : fderiv ℂ u z = fderiv ℂ u' z :=
    Filter.EventuallyEq.fderiv_eq (Filter.eventuallyEq_of_mem (hU.mem_nhds hz) hEq)
  unfold extBracket
  rw [hd]

/-- Linearity of `{·, φ}_c` on a combination of three differentiable functions. -/
theorem nit_bracket_lin (c : ℝ) {u v w φ : EC n k → ℂ} {z : EC n k} (a₁ a₂ : ℂ)
    (hu : DifferentiableAt ℂ u z) (hv : DifferentiableAt ℂ v z) (hw : DifferentiableAt ℂ w z) :
    extBracket c (fun x => u x + a₁ * v x + a₂ * w x) φ z =
      extBracket c u φ z + a₁ * extBracket c v φ z + a₂ * extBracket c w φ z := by
  have hd : fderiv ℂ (fun x => u x + a₁ * v x + a₂ * w x) z =
      fderiv ℂ u z + a₁ • fderiv ℂ v z + a₂ • fderiv ℂ w z := by
    have h1 : HasFDerivAt (fun x => u x + a₁ * v x + a₂ * w x)
        (fderiv ℂ u z + a₁ • fderiv ℂ v z + a₂ • fderiv ℂ w z) z :=
      (hu.hasFDerivAt.add (hv.hasFDerivAt.const_mul a₁)).add (hw.hasFDerivAt.const_mul a₂)
    exact h1.fderiv
  unfold extBracket
  rw [hd]
  simp only [add_apply, smul_apply, smul_eq_mul]

/-! ### The fast Hamiltonian on the extended space -/

/-- The fast projection of `V_R(base)` lies in `V_R({I_c})`. -/
theorem nit_fast_mem {b : PartialBlock n k} {R : ℝ} {J : Fin (n + (k + k)) → ℂ}
    (hJ : J ∈ polyNbhd b.base R) :
    (fun i => J (Fin.castAdd (k+k) i)) ∈ polyNbhd {KAM.realInclusion n b.Ic} R := by
  obtain ⟨J', ⟨x, -, rfl⟩, hlt⟩ := hJ
  refine ⟨KAM.realInclusion n b.Ic, rfl, lt_of_le_of_lt ?_ hlt⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (J - Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i / b.lam : ℝ) : ℂ)) (fun i => ((x.2 i / b.lam : ℝ) : ℂ))))
    (Fin.castAdd (k+k) i)
  simpa [Fin.append_left] using this

/-- `h ∘ fastAction ∈ 𝒪_{R',s'}` for `h` holomorphic on `V_R(I_c)`, `R' ≤ R`. -/
theorem nit_liftFast_class (b : PartialBlock n k) {R R' s' : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R)) (hR : R' ≤ R) :
    InClass b.base R' s' (liftFast (k := k) h) := by
  have hfast : Differentiable ℂ
      (fun J : Fin (n + (k + k)) → ℂ => fun i => J (Fin.castAdd (k+k) i)) :=
    differentiable_pi.2 fun i => differentiable_apply _
  refine ⟨fun z hz => ?_, fun _ _ _ => rfl⟩
  have h1 : DifferentiableAt ℂ h (fastAction z) :=
    hh.differentiableAt ((isOpen_polyNbhd _ _).mem_nhds (polyNbhd_mono hR (nit_fast_mem hz.2)))
  have h2 : DifferentiableAt ℂ (fun w : EC n k => fastAction w) z :=
    (hfast.comp differentiable_snd) z
  exact (h1.comp z h2).differentiableWithinAt

/-- `h ∘ fastAction` is real on real points when `h` is real on the real points of
`V_R(I_c)`. -/
theorem nit_liftFast_real {b : PartialBlock n k} {R R' s' : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hR : R' ≤ R)
    (hhr : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
      (h (KAM.realInclusion n I)).im = 0) :
    extReal (Dom n b.base R' s') (liftFast (k := k) h) := by
  intro x hx
  have hmem : (fun i => KAM.realInclusion (n + (k + k)) x.2 (Fin.castAdd (k+k) i)) ∈
      polyNbhd {KAM.realInclusion n b.Ic} R :=
    polyNbhd_mono hR (nit_fast_mem hx.2)
  have e : (fun i => KAM.realInclusion (n + (k + k)) x.2 (Fin.castAdd (k+k) i)) =
      KAM.realInclusion n (fun i => x.2 (Fin.castAdd (k+k) i)) := by
    funext i
    simp only [KAM.realInclusion_apply]
  rw [e] at hmem
  have h1 := hhr _ hmem
  rw [← e] at h1
  exact h1

/-- A function real on the real points of an open set has real frequency there (the hypothesis
of the reality clause of `hom`). -/
theorem nit_freq_im {S : Set (Fin n → ℂ)} {R : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd S R))
    (hhr : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd S R →
      (h (KAM.realInclusion n I)).im = 0)
    {I : Fin n → ℝ} (hI : KAM.realInclusion n I ∈ polyNbhd S R) (i : Fin n) :
    (freq h (KAM.realInclusion n I) i).im = 0 := by
  set v : Fin n → ℂ := Pi.single i 1 with hv
  set x₀ := KAM.realInclusion n I with hx₀
  let γ : ℝ → Fin n → ℂ := fun t => x₀ + (t : ℂ) • v
  have hγ : HasDerivAt γ v 0 := by
    have h1 : HasDerivAt (fun t : ℝ => (t : ℂ)) 1 0 := Complex.ofRealCLM.hasDerivAt
    have := (h1.smul_const v).const_add x₀
    simpa only [one_smul] using this
  have hγ0 : γ 0 = x₀ := by simp [γ]
  have hopen : IsOpen (polyNbhd S R) := isOpen_polyNbhd S R
  have hev : ∀ᶠ t in nhds (0 : ℝ), γ t ∈ polyNbhd S R :=
    hγ.continuousAt.eventually (hopen.mem_nhds (by rwa [hγ0]))
  have hhd : DifferentiableAt ℂ h (γ 0) :=
    hh.differentiableAt (hopen.mem_nhds (by rwa [hγ0]))
  have hcomp : HasDerivAt (fun t => h (γ t)) (fderiv ℂ h (γ 0) v) 0 :=
    (hhd.hasFDerivAt.restrictScalars ℝ).comp_hasDerivAt (0 : ℝ) hγ
  have him : HasDerivAt (fun t => (h (γ t)).im) (fderiv ℂ h (γ 0) v).im 0 :=
    Complex.imCLM.hasFDerivAt.comp_hasDerivAt (0 : ℝ) hcomp
  have hzero : (fun t => (h (γ t)).im) =ᶠ[nhds (0 : ℝ)] fun _ => (0 : ℝ) := by
    filter_upwards [hev] with t ht
    have hreal : γ t = KAM.realInclusion n (I + t • (Pi.single i 1 : Fin n → ℝ)) := by
      ext j
      by_cases hj : j = i <;> simp [γ, hx₀, hv, hj]
    have hmem : KAM.realInclusion n (I + t • (Pi.single i 1 : Fin n → ℝ)) ∈ polyNbhd S R := by
      rw [← hreal]
      exact ht
    have h2 := hhr _ hmem
    rw [← hreal] at h2
    exact h2
  have h0 := him.congr_of_eventuallyEq hzero.symm
  have := h0.unique (hasDerivAt_const (0 : ℝ) (0 : ℝ))
  rw [hγ0] at this
  simpa [freq, hv] using this

/-- Injectivity from a left inverse. -/
theorem nit_injOn {Φ Ψ : EC n k → EC n k} {U : Set (EC n k)} (hΨ : ∀ z ∈ U, Ψ (Φ z) = z) :
    Set.InjOn Φ U := by
  intro x hx y hy hxy
  calc x = Ψ (Φ x) := (hΨ x hx).symm
    _ = Ψ (Φ y) := by rw [hxy]
    _ = y := hΨ y hy

/-! ### The source premises -/

/-- The source premises of `bpN:p11:iterative` other than the decomposition of `g`
(exactly the binders of the signed `iterative` with `F2-C1`'s `0 < b.c`). -/
structure NitHyp (b : PartialBlock n k) (R s ρ σ K α p δ : ℝ) (h : (Fin n → ℂ) → ℂ)
    (f : EC n k → ℂ) (Λ : Set (Fin n → ℤ)) : Prop where
  nit_k : 1 ≤ k
  nit_rho : 0 < ρ
  nit_rho2 : 2*ρ < R
  nit_sig : 0 < σ
  nit_sig2 : 2*σ < s
  nit_slow : slowLoss b.c ρ σ k
  nit_c : 0 < b.c
  nit_alpha : 0 < α
  nit_p : 1 < p
  nit_K : 0 ≤ K
  nit_hol : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R)
  nit_div : DivisorBound (polyNbhd {KAM.realInclusion n b.Ic} R) K Λ h (α/conjExp p)
  nit_delta : 0 ≤ δ
  nit_fc : InClass b.base R s f
  nit_fb : WBound b.base R s f δ
  nit_small : δ ≤ 2*Real.pi*α*ρ*σ/(4*conjExp p)

namespace NitHyp

variable {b : PartialBlock n k} {R s ρ σ K α p δ : ℝ} {h : (Fin n → ℂ) → ℂ}
  {f : EC n k → ℂ} {Λ : Set (Fin n → ℤ)}

theorem nit_R_pos (H : NitHyp b R s ρ σ K α p δ h f Λ) : 0 < R := by
  linarith [H.nit_rho, H.nit_rho2]

theorem nit_s_pos (H : NitHyp b R s ρ σ K α p δ h f Λ) : 0 < s := by
  linarith [H.nit_sig, H.nit_sig2]

theorem nit_q_ge (H : NitHyp b R s ρ σ K α p δ h f Λ) : 1 ≤ conjExp p := by
  have hp := H.nit_p
  unfold conjExp
  rw [le_div_iff₀ (by linarith)]
  linarith

theorem nit_q_pos (H : NitHyp b R s ρ σ K α p δ h f Λ) : 0 < conjExp p :=
  lt_of_lt_of_le one_pos H.nit_q_ge

/-- `|φ|_{R,s} ≤ V = qδ/(2πα)` is nonnegative. -/
theorem nit_V_nonneg (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    0 ≤ conjExp p*δ/(2*Real.pi*α) := by
  have := H.nit_q_pos
  have := H.nit_alpha
  have := H.nit_delta
  have := Real.pi_pos
  positivity

/-- Step `it-gen`: `V/(ρσ) ≤ 1/4`, i.e. `η = 2V/(ρσ) ≤ 2qδ/(ᾱρσ) ≤ 1/2`. -/
theorem nit_V_le (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    conjExp p*δ/(2*Real.pi*α)/(ρ*σ) ≤ 1/4 := by
  have hq := H.nit_q_pos
  have hα := H.nit_alpha
  have hπ := Real.pi_pos
  have h1 : 0 < 2*Real.pi*α := by positivity
  have h2 : 0 < ρ*σ := mul_pos H.nit_rho H.nit_sig
  have h3 := H.nit_small
  rw [le_div_iff₀ (by positivity : (0:ℝ) < 4*conjExp p)] at h3
  rw [div_le_iff₀ h2, div_le_iff₀ h1]
  linarith

theorem nit_V_half (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    conjExp p*δ/(2*Real.pi*α)/(ρ*σ) ≤ 1/2 :=
  H.nit_V_le.trans (by norm_num)

/-- Step `it-gen`: the signed `hom` (`bpN:p11:hom`) with `q = conjExp p` and `U = δ`. -/
theorem nit_hom (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    InClass b.base R s (projMode Λ (truncate K f)) ∧ InClass b.base R s (homGenerator K Λ h f) ∧
    WBound b.base R s (projMode Λ (truncate K f)) δ ∧ WBound b.base R s (truncate K f) δ ∧
    WBound b.base R s (homGenerator K Λ h f) (conjExp p*δ/(2*Real.pi*α)) ∧
    (∀ z ∈ Dom n b.base R s, extBracket b.c (homGenerator K Λ h f) (liftFast h) z +
      projMode Λ (truncate K f) z = truncate K f z) ∧
    ((∀ j, j ∈ Λ ↔ -j ∈ Λ) → extReal (Dom n b.base R s) f →
      (∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
        ∀ i, (freq h (KAM.realInclusion n I) i).im = 0) →
      extReal (Dom n b.base R s) (projMode Λ (truncate K f)) ∧
        extReal (Dom n b.base R s) (homGenerator K Λ h f)) := by
  obtain ⟨c1, c2, c3, c4, c5, c6, -, c8⟩ := hom b h f H.nit_R_pos H.nit_s_pos H.nit_K
    H.nit_alpha H.nit_q_ge Λ H.nit_hol H.nit_div H.nit_delta H.nit_fc H.nit_fb
  exact ⟨c1, c2, c3, c4, c5, c6, c8⟩

theorem nit_phi_class (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    InClass b.base R s (homGenerator K Λ h f) :=
  H.nit_hom.2.1

theorem nit_phi_bound (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    WBound b.base R s (homGenerator K Λ h f) (conjExp p*δ/(2*Real.pi*α)) :=
  H.nit_hom.2.2.2.2.1

/-- The homological equation in bracket form: `{h, φ}_c = ξ - T_K f` on `𝒟_{R,s}`. -/
theorem nit_bracket_eq (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    ∀ z ∈ Dom n b.base R s, extBracket b.c (liftFast h) (homGenerator K Λ h f) z =
      projMode Λ (truncate K f) z - truncate K f z := by
  intro z hz
  have e1 := H.nit_hom.2.2.2.2.2.1 z hz
  have e2 := nit_extBracket_antisymm b.c (liftFast (k := k) h) (homGenerator K Λ h f) z
  linear_combination e2 - e1

/-- Step `it-taylor` (admissibility): the composition data of `φ` with `u`-domain
`(R-ρ, s-σ)` inside `(R, s)`. -/
theorem nit_compose (H : NitHyp b R s ρ σ K α p δ h f Λ) :
    ExtCompose b R s (R-ρ) (s-σ) ρ σ (conjExp p*δ/(2*Real.pi*α)) (homGenerator K Λ h f) where
  rho_pos := H.nit_rho
  rho_lt := by linarith [H.nit_rho2]
  sig_pos := H.nit_sig
  sig_lt := by linarith [H.nit_sig2]
  radii := by linarith
  widths := by linarith
  bound_nonneg := H.nit_V_nonneg
  hol := H.nit_phi_class
  bound := H.nit_phi_bound
  small := by
    have e : 2*(conjExp p*δ/(2*Real.pi*α))/(ρ*σ) = 2*(conjExp p*δ/(2*Real.pi*α)/(ρ*σ)) := by
      ring
    rw [e]
    linarith [H.nit_V_le]
  slow := H.nit_slow

/-- Step `it-map` (clause (b) of the source): the componentwise displacements of
`canonical_map` with `V = qδ/(2πα)`; the slow one through `(SL)_{ρ,σ}`, `c/ρ ≤ 1/(16kσ)`. -/
theorem nit_disp (H : NitHyp b R s ρ σ K α p δ h f Λ) {Φ : EC n k → EC n k}
    {U : Set (EC n k)}
    (h6 : ∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ conjExp p*δ/(2*Real.pi*α)/ρ ∧
      ‖fastAction (Φ z)-fastAction z‖ ≤ conjExp p*δ/(2*Real.pi*α)/(Real.exp 1*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ b.c*(conjExp p*δ/(2*Real.pi*α))/ρ) :
    ∀ z ∈ U, ‖(Φ z).1-z.1‖ ≤ conjExp p*δ/(2*Real.pi*α*ρ) ∧
      ‖fastAction (Φ z)-fastAction z‖ ≤ conjExp p*δ/(Real.exp 1*2*Real.pi*α*σ) ∧
      ‖slowPair (Φ z)-slowPair z‖ ≤ conjExp p*δ/(16*k*2*Real.pi*α*σ) := by
  intro z hz
  obtain ⟨d1, d2, d3⟩ := h6 z hz
  have hρ := H.nit_rho
  have hσ := H.nit_sig
  have hV := H.nit_V_nonneg
  have hk1 : (1:ℝ) ≤ k := by exact_mod_cast H.nit_k
  have h16 : 0 < 16*(k:ℝ)*σ := mul_pos (mul_pos (by norm_num) (by linarith)) hσ
  have hsl := H.nit_slow
  unfold slowLoss at hsl
  refine ⟨d1.trans (le_of_eq (by ring)), d2.trans (le_of_eq (by ring)), d3.trans ?_⟩
  calc b.c*(conjExp p*δ/(2*Real.pi*α))/ρ ≤ conjExp p*δ/(2*Real.pi*α)/(16*k*σ) := by
        rw [div_le_div_iff₀ hρ h16]
        linarith [mul_le_mul_of_nonneg_left hsl hV]
    _ = conjExp p*δ/(16*k*2*Real.pi*α*σ) := by ring

/-- `|g₊ - g|_{R-2ρ,s-2σ} ≤ δ`, `g₊ = g + P_Λ T_K f` (clause (c) of the source). -/
theorem nit_gp_bound (H : NitHyp b R s ρ σ K α p δ h f Λ) (G : EC n k → ℂ) :
    WBound b.base (R-2*ρ) (s-2*σ) ((G + projMode Λ (truncate K f)) - G) δ := by
  have hξb := H.nit_hom.2.2.1
  have hs : (0:ℝ) < s - 2*σ := by linarith [H.nit_sig2]
  refine wbound_congr_ext hs (fun z _ => ?_)
    (hξb.mono (by linarith [H.nit_rho]) (by linarith [H.nit_sig]) le_rfl)
  show projMode Λ (truncate K f) z = (G z + projMode Λ (truncate K f) z) - G z
  ring

end NitHyp

end KAM.Nekhoroshev

end
