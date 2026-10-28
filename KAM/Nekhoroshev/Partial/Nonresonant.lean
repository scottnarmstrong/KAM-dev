/-
Copyright (c) 2026 Scott Armstrong, Zohar Komargodski. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Zohar Komargodski
-/
module

public import KAM.Nekhoroshev.Partial.Setting
public import KAM.Nekhoroshev.NormalForm.Setting
public import KAM.Nekhoroshev.Partial.NormalForm
public import KAM.Nekhoroshev.Partial.RealSystem
public import KAM.Nekhoroshev.Partial.Preimage
public import KAM.Nekhoroshev.Partial.Transfer
public import KAM.Nekhoroshev.Partial.CompositionCoeff
public import KAM.Nekhoroshev.Stability.Setting
public import KAM.Weighted.Coefficients
public import KAM.Weighted.Projections
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.Deriv.Pi
public import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Nonresonant block stability (Part 11, package N11-M1)

`nonresonant` (`bpN:p11:nonresonant`): on a nonresonant block the fast actions of an orbit
that starts at the block centre and keeps its slow pair in the block move by at most `r_B/2`.
Design `docs/tracks/N/design/N11-LEAN-DESIGN.md`.

The proof follows the four steps of the blueprint (`p11c-partial-stability.tex` L69–74):

* `stepN:p11:nr-nf`: `nf` with `Λ = {0}` gives `Ψ`, `g`, `f_*` on `Dom(r_B/2, s/6)`;
* `stepN:p11:nr-t12`: the displacement bounds (T1) of `reExtMap Ψ` (`nnr_fast_re_le`,
  `nnr_slow_re_le`) and the real preimages (T2), from `preimage` with `ϱ' = r_B/2`, `σ' = s/3`
  (`nnr_arith_nf` checks `κ_* ≤ 1/4`);
* `stepN:p11:nr-t3`: (T3) is *proved* (design decision 5), with `ϱ = 15 r_B/32`: along a normal-form
  orbit `İ = -∂_θ f_*` (`nnr_fast_field_bound`: `h` depends on `I` only and `∂_θ g = 0` at real
  points because `g` has only the zero mode, `real_system_resonant`), so `|İ| ≤ 6η/(e s)`
  (`real_system_bounds`) and the drift is at most `|t|·6η/(e s) ≤ 6r_B/(5e) < 15r_B/32`
  (`nnr_drift`, `nnr_arith_drift`);
* `stepN:p11:nr-concl`: `transfer_conditional` gives `|I(u)-I_c| ≤ 15r_B/32 + 2 r_B/2⁷ ≤ r_B/2`.
-/

@[expose] public noncomputable section

open Set
open KAM.Weighted KAM.NormalForm

namespace KAM.Nekhoroshev

variable {n k : ℕ}

/-! ### The fast part `h(I)` of the Hamiltonian -/

/-- The fast action as a continuous `ℂ`-linear map. -/
private def nnrFastCLM (n k : ℕ) : EC n k →L[ℂ] (Fin n → ℂ) :=
  ContinuousLinearMap.pi fun i =>
    (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin (n + (k + k)) => ℂ)
      (Fin.castAdd (k + k) i)).comp (ContinuousLinearMap.snd ℂ (Fin n → ℂ) (Fin (n + (k + k)) → ℂ))

private theorem nnrFastCLM_theta (i : Fin n) : nnrFastCLM n k (Pi.single i 1, 0) = 0 := by
  funext j; simp [nnrFastCLM]

private theorem nnr_fastAction_extCx (z : ER n k) :
    fastAction (extCx z) = KAM.realInclusion n (fastAction z) := by
  ext i; simp [fastAction, extCx]

/-- The fast action of a point of `V_R(base)` lies in `V_R({I_c})`. -/
private theorem nnr_fast_mem (b : PartialBlock n k) {R : ℝ} {z : EC n k}
    (hz : z.2 ∈ polyNbhd b.base R) :
    fastAction z ∈ polyNbhd {KAM.realInclusion n b.Ic} R := by
  obtain ⟨J, ⟨x, -, rfl⟩, hlt⟩ := hz
  refine ⟨KAM.realInclusion n b.Ic, rfl, lt_of_le_of_lt ?_ hlt⟩
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have := norm_le_pi_norm (z.2 - Fin.append (fun i => (b.Ic i : ℂ))
    (Fin.append (fun i => ((x.1 i / b.lam : ℝ) : ℂ)) (fun i => ((x.2 i / b.lam : ℝ) : ℂ))))
    (Fin.castAdd (k + k) i)
  simpa [fastAction] using this

/-- The derivative of `liftFast h = h ∘ fastAction`. -/
private theorem nnr_liftFast_hasFDerivAt (b : PartialBlock n k) {R : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R)) {z : EC n k}
    (hz : z.2 ∈ polyNbhd b.base R) :
    HasFDerivAt (liftFast h : EC n k → ℂ)
      ((fderiv ℂ h (fastAction z)).comp (nnrFastCLM n k)) z := by
  have hm := nnr_fast_mem b hz
  have hd : DifferentiableAt ℂ h (fastAction z) :=
    (hh _ hm).differentiableAt ((isOpen_polyNbhd _ R).mem_nhds hm)
  have h1 : HasFDerivAt h (fderiv ℂ h (fastAction z)) (nnrFastCLM n k z) := hd.hasFDerivAt
  have hfun : (liftFast h : EC n k → ℂ) = h ∘ nnrFastCLM n k := funext fun w => rfl
  rw [hfun]
  exact h1.comp z (nnrFastCLM n k).hasFDerivAt

/-- The fast part `h(I)` is an extended-class function (holomorphy and reality only). -/
private theorem nnr_ext_class_liftFast (b : PartialBlock n k) {R s : ℝ} {h : (Fin n → ℂ) → ℂ}
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} R))
    (hr : ∀ I : Fin n → ℝ, KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} R →
      (h (KAM.realInclusion n I)).im = 0) :
    ext_class b R s (liftFast h) :=
  ⟨⟨fun z hz => (nnr_liftFast_hasFDerivAt b hh hz.2).differentiableAt.differentiableWithinAt,
    fun _ _ _ => rfl⟩, fun (x : ER n k) hx => by
    have h0 := nnr_fast_mem b (z := extCx x) hx.2
    rw [nnr_fastAction_extCx] at h0
    have h1 := hr _ h0
    rw [← nnr_fastAction_extCx] at h1
    exact h1⟩

private theorem nnr_ext_class_add (b : PartialBlock n k) {R s : ℝ} {u v : EC n k → ℂ}
    (hu : ext_class b R s u) (hv : ext_class b R s v) : ext_class b R s (u + v) :=
  ⟨⟨hu.1.differentiableOn.add hv.1.differentiableOn, fun j z hz => by
    simp only [Pi.add_apply, hu.1.periodic j z hz, hv.1.periodic j z hz]⟩, fun x hx => by
    simp [Pi.add_apply, hu.2 x hx, hv.2 x hx]⟩

/-! ### Class bookkeeping for `g` -/

private theorem nnr_inClass_mono {m : ℕ} {D : Set (Fin m → ℂ)} {r r' s s' : ℝ}
    {u : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u) (hr : r' ≤ r) (hs : s' ≤ s) :
    InClass D r' s' u :=
  ⟨hu.differentiableOn.mono (Dom_mono hr hs), fun j z hz => hu.periodic j z (Dom_mono hr hs hz)⟩

private theorem nnr_inClass_sub {m : ℕ} {D : Set (Fin m → ℂ)} {r s : ℝ}
    {u v : (Fin n → ℂ) × (Fin m → ℂ) → ℂ} (hu : InClass D r s u) (hv : InClass D r s v) :
    InClass D r s (u - v) :=
  ⟨hu.differentiableOn.sub hv.differentiableOn, fun j z hz => by
    simp only [Pi.sub_apply, hu.periodic j z hz, hv.periodic j z hz]⟩

/-- The resonant span of the zero lattice is trivial. -/
private theorem nnr_resSpan_zero : KAM.Stability.resSpan ({0} : Set (Fin n → ℤ)) = ⊥ := by
  rw [KAM.Stability.resSpan, Submodule.span_eq_bot]
  intro v hv
  obtain ⟨j, hj, rfl⟩ := hv
  rw [mem_singleton_iff] at hj
  subst hj
  ext i
  simp

/-! ### Real parts and displacements (T1) -/

private theorem nnr_re_le (a : ℂ) (x : ℝ) : |a.re - x| ≤ ‖a - (x : ℂ)‖ := by
  have h := Complex.abs_re_le_norm (a - (x : ℂ))
  rwa [Complex.sub_re, Complex.ofReal_re] at h

private theorem nnr_extRe_extCx (y : ER n k) : extRe (extCx y) = y := by
  ext i <;> simp [extRe, extCx]

/-- Taking real parts does not increase the fast displacement. -/
private theorem nnr_fast_re_le (w : EC n k) (z : ER n k) :
    ‖fastAction (extRe w) - fastAction z‖ ≤ ‖fastAction w - fastAction (extCx z)‖ := by
  refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun i => ?_
  have h1 := norm_le_pi_norm (fastAction w - fastAction (extCx z)) i
  have h2 := nnr_re_le (w.2 (Fin.castAdd (k+k) i)) (z.2 (Fin.castAdd (k+k) i))
  have e1 : (fastAction (extRe w) - fastAction z) i =
      (w.2 (Fin.castAdd (k+k) i)).re - z.2 (Fin.castAdd (k+k) i) := rfl
  have e2 : (fastAction w - fastAction (extCx z)) i =
      w.2 (Fin.castAdd (k+k) i) - (z.2 (Fin.castAdd (k+k) i) : ℂ) := rfl
  rw [e1, Real.norm_eq_abs]
  rw [e2] at h1
  exact h2.trans h1

/-- Taking real parts does not increase the slow displacement. -/
private theorem nnr_slow_re_le (w : EC n k) (z : ER n k) :
    ‖slowPair (extRe w) - slowPair z‖ ≤ ‖slowPair w - slowPair (extCx z)‖ := by
  have hA : ‖(slowPair (extRe w) - slowPair z).1‖ ≤ ‖slowPair w - slowPair (extCx z)‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_
    have h1 := (norm_le_pi_norm (slowPair w - slowPair (extCx z)).1 l).trans
      (norm_fst_le (slowPair w - slowPair (extCx z)))
    have h2 := nnr_re_le (w.2 (Fin.natAdd n (Fin.castAdd k l)))
      (z.2 (Fin.natAdd n (Fin.castAdd k l)))
    have e1 : (slowPair (extRe w) - slowPair z).1 l =
        (w.2 (Fin.natAdd n (Fin.castAdd k l))).re - z.2 (Fin.natAdd n (Fin.castAdd k l)) := rfl
    have e2 : (slowPair w - slowPair (extCx z)).1 l =
        w.2 (Fin.natAdd n (Fin.castAdd k l)) - (z.2 (Fin.natAdd n (Fin.castAdd k l)) : ℂ) := rfl
    rw [e1, Real.norm_eq_abs]
    rw [e2] at h1
    exact h2.trans h1
  have hB : ‖(slowPair (extRe w) - slowPair z).2‖ ≤ ‖slowPair w - slowPair (extCx z)‖ := by
    refine (pi_norm_le_iff_of_nonneg (norm_nonneg _)).2 fun l => ?_
    have h1 := (norm_le_pi_norm (slowPair w - slowPair (extCx z)).2 l).trans
      (norm_snd_le (slowPair w - slowPair (extCx z)))
    have h2 := nnr_re_le (w.2 (Fin.natAdd n (Fin.natAdd k l)))
      (z.2 (Fin.natAdd n (Fin.natAdd k l)))
    have e1 : (slowPair (extRe w) - slowPair z).2 l =
        (w.2 (Fin.natAdd n (Fin.natAdd k l))).re - z.2 (Fin.natAdd n (Fin.natAdd k l)) := rfl
    have e2 : (slowPair w - slowPair (extCx z)).2 l =
        w.2 (Fin.natAdd n (Fin.natAdd k l)) - (z.2 (Fin.natAdd n (Fin.natAdd k l)) : ℂ) := rfl
    rw [e1, Real.norm_eq_abs]
    rw [e2] at h1
    exact h2.trans h1
  calc ‖slowPair (extRe w) - slowPair z‖
      = max ‖(slowPair (extRe w) - slowPair z).1‖ ‖(slowPair (extRe w) - slowPair z).2‖ := by
        rw [Prod.norm_def]
    _ ≤ ‖slowPair w - slowPair (extCx z)‖ := max_le hA hB

/-! ### The fast velocity of the normal form (T3) -/

/-- Along the normal form `h + g + f_*` with `∂_θ g = 0` at real points, the fast component of
the real weighted field is `-∂_θ f_*`, hence bounded by `∑ⱼ |∂_{θⱼ} f_*|`. -/
private theorem nnr_fast_field_bound (b : PartialBlock n k) {r s B : ℝ}
    {h : (Fin n → ℂ) → ℂ} {g fs : EC n k → ℂ} (hr : 0 < r) (hs : 0 < s)
    (hh : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} r))
    (hH : ext_class b r s (liftFast h + g + fs))
    (hg : ext_class b r s g) (hf : ext_class b r s fs)
    (hg0 : ∀ z ∈ b.realDom r, ∀ i, dtheta i g (extCx z) = 0)
    (hfb : ∀ z ∈ b.realDom r, ∑ j, ‖dtheta j fs (extCx z)‖ ≤ B) (hB : 0 ≤ B) :
    ∀ z ∈ b.realDom r,
      ‖fastAction (realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z)‖ ≤ B := by
  intro z hz
  have hcx : extCx (realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z) =
      wfield b.c (liftFast h + g + fs) (extCx z) := (real_system b hr hs hH).2.2.1 z hz
  have hzD : extCx z ∈ Dom n b.base r s := ⟨KAM.ofReal_mem_complexStrip hs z.1, hz.2⟩
  have hopen : IsOpen (Dom n b.base r s) := isOpen_Dom (n := n) b.base r s
  have hL := nnr_liftFast_hasFDerivAt b hh hzD.2
  have hG : HasFDerivAt g (fderiv ℂ g (extCx z)) (extCx z) :=
    (hg.1.differentiableOn.differentiableAt (hopen.mem_nhds hzD)).hasFDerivAt
  have hF : HasFDerivAt fs (fderiv ℂ fs (extCx z)) (extCx z) :=
    (hf.1.differentiableOn.differentiableAt (hopen.mem_nhds hzD)).hasFDerivAt
  have hHs : HasFDerivAt (liftFast h + g + fs)
      ((fderiv ℂ h (fastAction (extCx z))).comp (nnrFastCLM n k) + fderiv ℂ g (extCx z) +
        fderiv ℂ fs (extCx z)) (extCx z) := (hL.add hG).add hF
  have hsum : fderiv ℂ (liftFast h + g + fs) (extCx z) =
      (fderiv ℂ h (fastAction (extCx z))).comp (nnrFastCLM n k) + fderiv ℂ g (extCx z) +
        fderiv ℂ fs (extCx z) := hHs.fderiv
  refine (pi_norm_le_iff_of_nonneg hB).2 fun i => ?_
  have h1 : (((realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z).2
      (Fin.castAdd (k+k) i) : ℝ) : ℂ) =
      (wfield b.c (liftFast h + g + fs) (extCx z)).2 (Fin.castAdd (k+k) i) :=
    congrArg (fun w : EC n k => w.2 (Fin.castAdd (k+k) i)) hcx
  have h2 : (wfield b.c (liftFast h + g + fs) (extCx z)).2 (Fin.castAdd (k+k) i) =
      -fderiv ℂ (liftFast h + g + fs) (extCx z) (Pi.single i 1, 0) := by
    simp only [wfield, Fin.append_left]
  have hgi : fderiv ℂ g (extCx z) (Pi.single i 1, 0) = 0 := hg0 z hz i
  have h3 : fderiv ℂ (liftFast h + g + fs) (extCx z) (Pi.single i 1, 0) =
      fderiv ℂ fs (extCx z) (Pi.single i 1, 0) := by
    rw [hsum, add_apply, add_apply,
      ContinuousLinearMap.comp_apply, nnrFastCLM_theta, map_zero, hgi]
    simp only [zero_add]
  have e : fastAction (realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z) i =
      (realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z).2
        (Fin.castAdd (k+k) i) := rfl
  calc ‖fastAction (realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z) i‖
      = ‖(((realWfield b.c (realHamiltonianExt b r (liftFast h + g + fs)) z).2
          (Fin.castAdd (k+k) i) : ℝ) : ℂ)‖ := by rw [e, Complex.norm_real]
    _ = ‖fderiv ℂ fs (extCx z) (Pi.single i 1, 0)‖ := by rw [h1, h2, h3, norm_neg]
    _ ≤ ∑ j, ‖dtheta j fs (extCx z)‖ :=
        Finset.single_le_sum (f := fun j => ‖dtheta j fs (extCx z)‖)
          (fun _ _ => norm_nonneg _) (Finset.mem_univ i)
    _ ≤ B := hfb z hz

/-- The fast actions of an orbit drift at most `|t| B` if the fast velocity is bounded by `B`. -/
private theorem nnr_drift {b : PartialBlock n k} {r B : ℝ} {Ht : EC n k → ℂ}
    (hB : ∀ z ∈ b.realDom r,
      ‖fastAction (realWfield b.c (realHamiltonianExt b r Ht) z)‖ ≤ B)
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ExtOrbit b r Ht J y) {t : ℝ} (ht : t ∈ J) :
    ‖fastAction (y t) - fastAction (y 0)‖ ≤ |t| * B := by
  have hsub : uIcc (0:ℝ) t ⊆ J := hJ.uIcc_subset h0 ht
  have hder : ∀ τ ∈ uIcc (0:ℝ) t, HasDerivWithinAt (fun σ => fastAction (y σ))
      (fastAction (realWfield b.c (realHamiltonianExt b r Ht) (y τ))) (uIcc (0:ℝ) t) τ := by
    intro τ hτ
    obtain ⟨-, hd⟩ := hy τ (hsub hτ)
    have hsnd : HasDerivAt (fun σ => (y σ).2)
        (realWfield b.c (realHamiltonianExt b r Ht) (y τ)).2 τ :=
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) (Fin (n+(k+k)) → ℝ)).hasFDerivAt.comp_hasDerivAt
        τ hd
    have h2 : HasDerivAt (fun σ => fastAction (y σ))
        (fastAction (realWfield b.c (realHamiltonianExt b r Ht) (y τ))) τ :=
      hasDerivAt_pi.2 fun i => hasDerivAt_pi.1 hsnd (Fin.castAdd (k+k) i)
    exact h2.hasDerivWithinAt
  have hmvt := (convex_uIcc (0:ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le hder
    (fun τ hτ => hB _ (hy τ (hsub hτ)).1) left_mem_uIcc right_mem_uIcc
  exact hmvt.trans_eq (by rw [sub_zero, Real.norm_eq_abs]; ring)

/-! ### Arithmetic -/

private theorem nnr_conjExp_pos {p : ℝ} (hp : 1 < p) : 0 < conjExp p := by
  unfold conjExp
  exact div_pos (by linarith) (by linarith)

/-- The numerical facts of steps `nr-t12` and `nr-concl`. -/
private theorem nnr_arith_nf {q K ε α r s : ℝ} (hq : 0 < q) (hK : 0 < K) (hε : 0 < ε)
    (hα : 0 < α) (hr : 0 < r) (hs : 0 < s) (hcut : 6 ≤ 2*Real.pi*K*s)
    (hsmall : ε ≤ α*r/(2^7*q*K)) :
    q*K*ε/α ≤ r/128 ∧
    max (10*q*ε/(2*Real.pi*α*r)/(s/3)) (max (q*K*ε/α/(r/2)) (q*K*ε/(8*α)/(r/2))) ≤ 1/4 ∧
    q*K*ε/(8*α) < r/2 ∧ q*K*ε/α + 15*r/32 < r/2 ∧ 15*r/32 + 2*(q*K*ε/α) ≤ r/2 := by
  have h1 : ε * (2^7*q*K) ≤ α*r := (le_div_iff₀ (by positivity)).1 hsmall
  have h1' : 128*(q*K*ε) ≤ α*r :=
    calc 128*(q*K*ε) = ε * (2^7*q*K) := by ring
      _ ≤ α*r := h1
  have hd : q*K*ε/α ≤ r/128 := by
    rw [div_le_iff₀ hα]
    linarith
  have hθ : 10*q*ε/(2*Real.pi*α*r) ≤ s/12 := by
    rw [div_le_iff₀ (by positivity)]
    have h3 : 2*Real.pi*s*(128*(q*K*ε)) ≤ 2*Real.pi*s*(α*r) :=
      mul_le_mul_of_nonneg_left h1' (by positivity)
    have h4 : 6*(q*ε) ≤ 2*Real.pi*K*s*(q*ε) :=
      mul_le_mul_of_nonneg_right hcut (by positivity)
    nlinarith [h3, h4, mul_pos hq hε]
  have hdx : q*K*ε/(8*α) = q*K*ε/α/8 := by ring
  refine ⟨hd, max_le ?_ (max_le ?_ ?_), ?_, ?_, ?_⟩
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · rw [div_le_iff₀ (by positivity)]
    linarith
  · rw [hdx, div_le_iff₀ (by positivity)]
    linarith
  · rw [hdx]
    linarith
  · linarith
  · linarith

/-- Time bound times the fast-velocity bound (`stepN:p11:nr-t3`): `6r/(5e) < 15r/32`. -/
private theorem nnr_arith_drift {s r ε K t : ℝ} (hs : 0 < s) (hr : 0 < r) (hε : 0 < ε)
    (ht : |t| ≤ s*r/(5*ε)*Real.exp ((2*Real.pi*K*s)/6)) :
    |t| * (Real.exp (-(2*Real.pi*K*s)/6)*ε/(Real.exp 1*(s/6))) ≤ 15*r/32 := by
  have hE : Real.exp (-(2*Real.pi*K*s)/6) * Real.exp ((2*Real.pi*K*s)/6) = 1 := by
    rw [← Real.exp_add]
    have e : -(2*Real.pi*K*s)/6 + (2*Real.pi*K*s)/6 = 0 := by ring
    rw [e, Real.exp_zero]
  have he : (2.56 : ℝ) < Real.exp 1 := by
    have := Real.exp_one_gt_d9
    linarith
  have h4 : s*r/(5*ε)*ε = s*r/5 := by
    rw [div_mul_eq_mul_div, div_eq_iff (mul_pos (by norm_num : (0:ℝ) < 5) hε).ne']
    ring
  have h1 : |t| * (Real.exp (-(2*Real.pi*K*s)/6) * ε) ≤ s*r/5 := by
    calc |t| * (Real.exp (-(2*Real.pi*K*s)/6) * ε)
        ≤ s*r/(5*ε)*Real.exp ((2*Real.pi*K*s)/6) * (Real.exp (-(2*Real.pi*K*s)/6) * ε) :=
          mul_le_mul_of_nonneg_right ht (by positivity)
      _ = s*r/(5*ε)*ε * (Real.exp (-(2*Real.pi*K*s)/6) * Real.exp ((2*Real.pi*K*s)/6)) := by
          ring
      _ = s*r/5 := by rw [hE, mul_one, h4]
  have e3 : |t| * (Real.exp (-(2*Real.pi*K*s)/6)*ε/(Real.exp 1*(s/6))) =
      |t| * (Real.exp (-(2*Real.pi*K*s)/6) * ε) / (Real.exp 1*(s/6)) := by ring
  rw [e3, div_le_iff₀ (by positivity)]
  nlinarith [h1, mul_pos (mul_pos hs hr) (sub_pos.2 he)]

/-! ### Proposition 1^e -/

/-- `bpN:p11:nonresonant`. Steps `nr-nf`, `nr-t12`, `nr-t3` (proved here, never assumed) and
`nr-concl` of `p11c-partial-stability.tex` L69–74. -/
theorem nonresonant (b : PartialBlock n k) {s K α L p ε : ℝ}
    {h : (Fin n → ℂ) → ℂ} {f : EC n k → ℂ}
    (hh : ExtNFHyp b s K α L p ε {0} h f)
    (hsmall : ε ≤ α*b.rB/(2^7*conjExp p*K))
    (F : ER n k → ER n k)
    (hF : EqOn F (realWfield b.c (realHamiltonianExt b b.rB (liftFast h+f))) (b.realDom b.rB))
    {J : Set ℝ} (hJ : J.OrdConnected) (h0 : (0:ℝ) ∈ J) {y : ℝ → ER n k}
    (hy : ∀ u ∈ J, HasDerivAt y (F (y u)) u)
    (hinit : fastAction (y 0) = b.Ic) (hx : b.lam • slowPair (y 0) ∈ b.S)
    {t1 : ℝ} (ht1 : t1 ∈ J) (ht : |t1| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6))
    (hstop : ∀ u ∈ uIcc 0 t1, b.lam • slowPair (y u) ∈ b.S) :
    ∀ u ∈ uIcc 0 t1, ‖fastAction (y u)-b.Ic‖ ≤ b.rB/2 := by
  have hrB : 0 < b.rB := hh.radius_pos
  have hw : 0 < b.w := hh.slow_width_pos
  have hs : 0 < s := hh.s_pos
  have hK : 0 < K := hh.K_pos
  have hα : 0 < α := hh.alpha_pos
  have hε : 0 < ε := hh.eps_pos
  have hq : 0 < conjExp p := nnr_conjExp_pos hh.p_gt
  have hr2 : 0 < b.rB/2 := by linarith
  have hs6 : 0 < s/6 := by linarith
  obtain ⟨-, hpresmall, hdxr, hgap, hfin⟩ :=
    nnr_arith_nf hq hK hε hα hrB hs hh.cutoff hsmall
  -- `stepN:p11:nr-nf`: the normal form with `Λ = {0}`
  obtain ⟨Ψ, g, fs, hΨd, hΨmap, -, hΨcan, -, hΨreal, hgC, hfsC, hgco, hconj, hgB0, hfsB,
    hΨdisp⟩ := nf b hh hsmall
  have hhol2 : DifferentiableOn ℂ h (polyNbhd {KAM.realInclusion n b.Ic} (b.rB/2)) :=
    hh.hol.mono (polyNbhd_mono (by linarith))
  have hreal2 : ∀ I : Fin n → ℝ,
      KAM.realInclusion n I ∈ polyNbhd {KAM.realInclusion n b.Ic} (b.rB/2) →
      (h (KAM.realInclusion n I)).im = 0 :=
    fun I hI => hh.real I (polyNbhd_mono (by linarith) hI)
  have houter : ext_class b b.rB s (liftFast h + f) :=
    nnr_ext_class_add b (nnr_ext_class_liftFast b hh.hol hh.real) hh.pert
  have hinner : ext_class b (b.rB/2) (s/6) (liftFast h + g + fs) :=
    nnr_ext_class_add b (nnr_ext_class_add b (nnr_ext_class_liftFast b hhol2 hreal2) hgC) hfsC
  have hc : ExtConjHyp b b.rB s (b.rB/2) (s/6) (liftFast h + f) (liftFast h + g + fs) Ψ :=
    { R_pos := hrB
      r_pos := hr2
      s_pos := hs
      t_pos := hs6
      r_le := by linarith
      t_le := by linarith
      outer := houter
      inner := hinner
      hol := hΨd
      maps := hΨmap
      real := fun z hz => hΨreal z hz
      canon := hΨcan
      identity := fun z hz => by
        simp only [Pi.add_apply]
        exact (hconj z hz).symm }
  -- `stepN:p11:nr-t12`: (T1) displacement of the real map
  have hdispT : ∀ z ∈ b.realDom (b.rB/2),
      ‖fastAction (reExtMap Ψ z) - fastAction z‖ ≤ conjExp p*K*ε/α ∧
      ‖slowPair (reExtMap Ψ z) - slowPair z‖ ≤ conjExp p*K*ε/(8*α) := by
    intro z hz
    have hzD : extCx z ∈ Dom n b.base (b.rB/2) (s/6) :=
      ⟨KAM.ofReal_mem_complexStrip hs6 z.1, hz.2⟩
    obtain ⟨h1, -, h3⟩ := hΨdisp (extCx z) hzD
    exact ⟨(nnr_fast_re_le (Ψ (extCx z)) z).trans h1, (nnr_slow_re_le (Ψ (extCx z)) z).trans h3⟩
  -- (T2) real preimages, `ϱ' = r_B/2`, `σ' = s/3`
  have hpreim := KAM.Nekhoroshev.preimage b hrB hw (R := b.rB/2) (s := s/6)
    (dθ := 10*conjExp p*ε/(2*Real.pi*α*b.rB)) (dI := conjExp p*K*ε/α)
    (dx := conjExp p*K*ε/(8*α)) (ρ := b.rB/2) (σ := s/3) hΨd (fun z hz => hΨreal z hz)
    (fun z hz => ⟨(hΨdisp z hz).2.1, (hΨdisp z hz).1, (hΨdisp z hz).2.2⟩)
    hr2 le_rfl (by linarith) (by linarith) hpresmall
  have hpreT : ∀ y' : ER n k, fastAction y' = b.Ic → b.lam • slowPair y' ∈ b.S →
      ∃ x ∈ b.realDom (b.rB/2), reExtMap Ψ x = y' ∧
        ‖fastAction x - b.Ic‖ ≤ conjExp p*K*ε/α := by
    intro y' hI hS
    obtain ⟨x, hxD, hxy, -, hxI, -⟩ := hpreim y' hI hS
    refine ⟨x, hxD, ?_, hxI⟩
    show extRe (Ψ (extCx x)) = y'
    rw [hxy]
    exact nnr_extRe_extCx y'
  -- `stepN:p11:nr-t3`: `g` has only the zero mode, so `∂_θ g = 0` at real points
  obtain ⟨hTc, -, hTb, -, -⟩ :=
    projections hs hh.pert.1 hh.bound {j : Fin n → ℤ | KAM.Fourier.modeSize j ≤ K}
  have hTc' : InClass b.base b.rB s (truncate K f) := hTc
  have hTb' : WBound b.base b.rB s (truncate K f) ε := hTb
  obtain ⟨hPc, -, hPb, -, -⟩ := projections hs hTc' hTb' {0}
  have hPc' : InClass b.base (b.rB/2) (s/6) (projMode {0} (truncate K f)) :=
    nnr_inClass_mono hPc (by linarith) (by linarith)
  have hPb' : WBound b.base (b.rB/2) (s/6) (projMode {0} (truncate K f)) ε :=
    hPb.mono (by linarith) (by linarith) le_rfl
  have hDc : InClass b.base (b.rB/2) (s/6) (g - projMode {0} (truncate K f)) :=
    nnr_inClass_sub hgC.1 hPc'
  have hgsum := wbound_add_ext hs6 hDc hPc' hgB0 hPb'
  have hgB : WBound b.base (b.rB/2) (s/6) g (16*(2*conjExp p*K/(α*b.rB))*ε^2 + ε) := by
    simpa only [Pi.sub_apply, sub_add_cancel] using hgsum
  have hg0 : ∀ z ∈ b.realDom (b.rB/2), ∀ i, dtheta i g (extCx z) = 0 := by
    intro z hz i
    obtain ⟨h1, h2⟩ := real_system_resonant b hs6 hgC.1 hgB (Λ := ({0} : Set (Fin n → ℤ)))
      (fun J' hJ' j hj => hgco J' hJ' j (fun hj' => hj hj'.1)) z hz
    rw [nnr_resSpan_zero, Submodule.mem_bot] at h1 h2
    have hre : (dtheta i g (extCx z)).re = 0 := congrFun h1 i
    have him : (dtheta i g (extCx z)).im = 0 := congrFun h2 i
    exact Complex.ext (by rw [hre, Complex.zero_re]) (by rw [him, Complex.zero_im])
  -- the fast velocity of the normal form is `-∂_θ f_*`, of size `≤ 6η/(e s)`
  have hB0 : 0 ≤ Real.exp (-(2*Real.pi*K*s)/6)*ε/(Real.exp 1*(s/6)) := by positivity
  have hfield := nnr_fast_field_bound b hr2 hs6 hhol2 hinner hgC hfsC hg0
    (fun z hz => (real_system_bounds b hs6 hfsC.1 hfsB z hz).2) hB0
  have hTr : 0 < s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6) := by positivity
  -- (T3) with `ϱ = 15 r_B/32` and `T = T_nr`
  have hT3 : ∀ J' : Set ℝ, J'.OrdConnected → (0:ℝ) ∈ J' → ∀ y' : ℝ → ER n k,
      ExtOrbit b (b.rB/2) (liftFast h + g + fs) J' y' →
      ‖fastAction (y' 0) - b.Ic‖ ≤ conjExp p*K*ε/α →
      (∀ u ∈ J', slowTube b (conjExp p*K*ε/(8*α)) (slowPair (y' u))) →
      ∀ u ∈ J', ENNReal.ofReal |u| ≤
        ENNReal.ofReal (s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6)) →
      ‖fastAction (y' u) - fastAction (y' 0)‖ ≤ 15*b.rB/32 := by
    intro J' hJ' h0' y' hy' _ _ u hu huT
    have hu' : |u| ≤ s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6) :=
      (ENNReal.ofReal_le_ofReal_iff hTr.le).1 huT
    exact (nnr_drift hfield hJ' h0' hy' hu).trans (nnr_arith_drift hs hrB hε hu')
  -- `stepN:p11:nr-concl`: the stopped transfer
  have hd0 : 0 ≤ conjExp p*K*ε/α :=
    div_nonneg (mul_nonneg (mul_nonneg hq.le hK.le) hε.le) hα.le
  have hdx0 : 0 ≤ conjExp p*K*ε/(8*α) :=
    div_nonneg (mul_nonneg (mul_nonneg hq.le hK.le) hε.le) (by linarith)
  have ha : 0 < 15*b.rB/32 := by linarith
  have key := transfer_conditional b hrB hw hc (fun a => ‖a‖) KAM.Stability.isActionNorm_norm
    (d := conjExp p*K*ε/α) (dx := conjExp p*K*ε/(8*α)) (a := 15*b.rB/32)
    (T := ENNReal.ofReal (s*b.rB/(5*ε)*Real.exp ((2*Real.pi*K*s)/6)))
    hd0 hdx0 hdxr ha hgap (ENNReal.ofReal_pos.2 hTr) hdispT hpreT hT3 F hF hJ h0 hy hinit hx
    ht1 (ENNReal.ofReal_le_ofReal ht) hstop
  intro u hu
  exact (key u hu).2.trans hfin

end KAM.Nekhoroshev

end
